From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path bigop finfun .

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From BloomFilter
     Require Import Parameters Hash HashVec Comp Notationv1 BitVector FixedList.



Section CountingBloomFilter.
  (*
   A fomalization of a counting bloom filter structure and properties

   *)

  (*
    k - number of hashes
   *)
  Variable k: nat.
  (*
    n - maximum number of hashes supported
   *)
  Variable n: nat.
  Variable Hkgt0: k >0.

  (*
     list of hash functions used in the bloom filter
   *)

  Definition CountVector := (Hash_size.+1).-tuple 'I_n.




    Record CountingBloomFilter := mkCountingBloomFilter {
                              counting_bloomfilter_state: CountVector
                          }.

  Definition Countingbloomfilter_prod (bf: CountingBloomFilter) :=
    (counting_bloomfilter_state bf).
  Definition prod_Countingbloomfilter  pair := let: (state) := pair in @mkCountingBloomFilter state.

  Lemma countingbloomfilter_cancel : cancel (Countingbloomfilter_prod) (prod_Countingbloomfilter).
  Proof.
      by case.
  Qed.


  Definition countingbloomfilter_eqMixin :=
    CanEqMixin countingbloomfilter_cancel .
  Canonical countingbloomfilter_eqType  :=
    Eval hnf in EqType CountingBloomFilter  countingbloomfilter_eqMixin .

  Definition countingbloomfilter_choiceMixin :=
    CanChoiceMixin countingbloomfilter_cancel.
  Canonical countingbloomfilter_choiceType  :=
    Eval hnf in ChoiceType CountingBloomFilter  countingbloomfilter_choiceMixin.

  Definition countingbloomfilter_countMixin :=
    CanCountMixin countingbloomfilter_cancel.
  Canonical countingbloomfilter_countType :=
    Eval hnf in CountType CountingBloomFilter  countingbloomfilter_countMixin.

  Definition countingbloomfilter_finMixin :=
    CanFinMixin countingbloomfilter_cancel .
  Canonical countingbloomfilter_finType :=
    Eval hnf in FinType CountingBloomFilter  countingbloomfilter_finMixin.

  Definition incr_bit (value: 'I_n) : 'I_n :=
    (if value.+1 < n as b return ((value.+1 < n) = b -> 'I_n)
    then (fun b0 => Ordinal b0)
    else (fun _ => value)) (erefl (value.+1 < n)).


  

  Definition countingbloomfilter_set_bit (value: 'I_(Hash_size.+1)) bf : CountingBloomFilter :=
    mkCountingBloomFilter
      (set_tnth (counting_bloomfilter_state bf)
                (incr_bit (tnth (counting_bloomfilter_state bf) value))
                value).

  Definition countingbloomfilter_get_bit (value: 'I_(Hash_size.+1)) bf : bool :=
      (tnth (counting_bloomfilter_state bf) value) > 0.

  Fixpoint countingbloomfilter_add_internal (items: seq 'I_(Hash_size.+1)) bf : CountingBloomFilter :=
    match items with
      h::t => countingbloomfilter_add_internal t (countingbloomfilter_set_bit h bf)
    | [::]   => bf
    end.

  Definition countingbloomfilter_add (value: hash_keytype) (hashes: k.-tuple (HashState n)) (bf: CountingBloomFilter) : Comp [finType of (k.-tuple (HashState n)) * CountingBloomFilter] :=
    hash_res <-$ (hash_vec_int value hashes);
      let (new_hashes, hash_vec) := hash_res in
      let new_bf := countingbloomfilter_add_internal (tval hash_vec) bf in
      ret (new_hashes, new_bf).

  Definition countingbloomfilter_query_internal (items: seq 'I_(Hash_size.+1)) bf : bool :=
    all (fun h => countingbloomfilter_get_bit h bf) items.

  Definition countingbloomfilter_query (value: hash_keytype) (hashes: k.-tuple (HashState n)) (bf: CountingBloomFilter) : Comp [finType of (k.-tuple (HashState n)) * bool ] :=
    hash_res <-$ (hash_vec_int value hashes);
      let (new_hashes, hash_vec) := hash_res in
      let qres := countingbloomfilter_query_internal (tval hash_vec) bf in
      ret (new_hashes, qres).

  Definition countingbloomfilter_bitcount (bf: CountingBloomFilter) : nat :=
    (foldr (fun a b => (nat_of_ord a) + b) 0 (tval (counting_bloomfilter_state bf))).


  Definition countingbloomfilter_free_capacity (bf: CountingBloomFilter) l :=
    all (fun a => (nat_of_ord a) + l < n) (tval (counting_bloomfilter_state bf)).

  Definition countingbloomfilter_new (Hngt0 : n > 0):  CountingBloomFilter.
    apply mkCountingBloomFilter.
    apply Tuple with (nseq Hash_size.+1 (Ordinal Hngt0)).
      by rewrite size_nseq.
  Defined.

  Definition countingbloomfilter_add_multiple  hsh_0 bf_0 values :=
    @foldr B (Comp [finType of k.-tuple (HashState n) * CountingBloomFilter])
           (fun val hsh_bf =>
              res_1 <-$ hsh_bf;
                let (hsh, bf) := res_1 in
                countingbloomfilter_add val hsh bf) (ret (hsh_0, bf_0)) values.

  

  Lemma countingbloomfilter_new_empty_bitcount (Hngt0: n > 0):
    countingbloomfilter_bitcount (countingbloomfilter_new Hngt0) = 0.
  Proof.
    rewrite/countingbloomfilter_bitcount //=; rewrite add0n.
    by elim: Hash_size => [//=| m IHm] //=.
  Qed.
  

    
  Lemma countingbloomfilter_bitcount_incr l bf ind:
    countingbloomfilter_free_capacity bf l.+1 ->
    countingbloomfilter_bitcount bf + l.+1 =
    countingbloomfilter_bitcount (countingbloomfilter_set_bit ind bf) + l.
  Proof.
    move: bf => []; rewrite/CountVector //=.

    rewrite/countingbloomfilter_free_capacity
           /countingbloomfilter_set_bit
           /countingbloomfilter_bitcount/counting_bloomfilter_state.
    elim: (Hash_size) ind => [| m Im].
    - {
        move=> [ind Hind] [[//=|b [|//=]] Hbf] /allP Hbits //=.

        rewrite //= addn0.

        case: ind Hind => //= Hind.
        - {
            rewrite addn0; have ->: (tnth (Tuple Hbf) (Ordinal Hind)) = b; first by [].
            have H1: (b \in Tuple (Hbf)); first by rewrite mem_seq1 eq_refl.
            move: (Hbits b H1).
            rewrite addnS -addSn => /InvMisc.addr_ltn H2.  
            rewrite/incr_bit; move: (erefl _ ) => //=.
            by rewrite {2 3}H2 //=.
          }
      }
    - {
        move=> [[|ind] Hind] [[//=| x xs] Hxs] //=/andP [Hltn Hallltn].
        - {
            have H1: (0 < m.+1); first by [].
            rewrite -addnA.
            have Hxs': size xs == m.+1; first by move/eqP: Hxs => //= [->] //=.
            have->: (tnth (Tuple Hxs) (Ordinal Hind)) = x; first by [].
            move: Hltn; rewrite addnS -addSn => /InvMisc.addr_ltn H2.
            rewrite/incr_bit; move: (erefl _ ) => //=.
            rewrite {2 3}H2 //= =>_.
            by rewrite addnS addnS -addSn addnA.
          }
        - {
            have H1: (ind < m.+1); first by move/InvMisc.ltn_Snn: Hind.
            have H2: size xs == m.+1; first by move/eqP: Hxs => //= [->] //=.
            rewrite -addnA; move: (Im (Ordinal H1) (Tuple H2))=> //= -> //=.
            have->: (ntuple_head (Tuple Hxs)) = x; first by [].
            rewrite -addnA; apply f_equal.
            rewrite addnC [foldr _ _ _ + _]addnC; apply f_equal => //=.

            move: (erefl _ ) => //= H3.
            apply f_equal=>//=.
            case: ind Hind H1 H3 => //=; intros.

            {
              have->: (Tuple H2) = (behead_tuple (Tuple Hxs)).

              {
                rewrite/behead_tuple; move: (behead_tupleP _) => //= H2'.
                  by rewrite (proof_irrelevance _ H2 H2').              
              }
              rewrite tnth_behead //=.
              have->: (inord 1) = (Ordinal Hind).
              {
                rewrite/inord/insubd/odflt/oapp //=.
                move: (insubT (fun i => i < m.+2)) ->.
                  by rewrite/Sub//=.              
              }
                by [].
              
            }

            {
              rewrite/ntuple_tail.
              move: (behead_tupleP _) => //= H4.
              move: (behead_tupleP _) => //= H5.
              move: (behead_tupleP _) => //= H6.
              rewrite (proof_irrelevance _ H2 H5); clear H2.
              rewrite (proof_irrelevance _ H4 H6); clear H4.
              do? apply f_equal.
              have->: (Tuple H5) = (behead_tuple (Tuple Hxs)).
              {
                rewrite/behead_tuple; move: (behead_tupleP _) => //= H2'.
                  by rewrite (proof_irrelevance _ H5 H2').              
              }
              rewrite tnth_behead //=.
              have->: (inord n0.+2) = (Ordinal Hind).
              {
                rewrite/inord/insubd/odflt/oapp //=.
                move: (insubT (fun i => i < m.+2)) ->.
                  by rewrite/Sub//=.              
              }
                by [].

            }

      }

      }
      
  Qed.


  Lemma countingbloomfilter_add_capacity_decr l bf ind val:
    countingbloomfilter_free_capacity bf l.+1 ->
    val \in counting_bloomfilter_state (countingbloomfilter_set_bit ind bf) ->
            val + l < n.
  Proof.

    case: bf; rewrite/CountVector=> bf; case: ind => ind Hind.
    rewrite/countingbloomfilter_free_capacity/counting_bloomfilter_state/countingbloomfilter_set_bit//.

    have->: (set_tnth (counting_bloomfilter_state {| counting_bloomfilter_state := bf |})
          (incr_bit
             (tnth (counting_bloomfilter_state {| counting_bloomfilter_state := bf |}) (Ordinal Hind)))
          (Ordinal Hind)) =
          (set_tnth bf (incr_bit (tnth bf (Ordinal Hind))) (Ordinal Hind)
          ); first by [].


    elim: Hash_size bf ind Hind => [|m IHm] bf.

    - {
        move=> [|//=] Hind  /allP Hall //=.        

        rewrite in_cons =>/orP [].

        - {
            move=>/eqP ->.
            move: (Hall _ (mem_tnth (Ordinal Hind) bf)).
            rewrite addnS -addSn => /InvMisc.addr_ltn H2.
            rewrite/incr_bit; move: (erefl _ ) => //=.
            rewrite {2 3}H2 //= =>_.
              by rewrite addSn -addnS; apply Hall; apply mem_tnth.
          }

        - {
            move=>/(mem_behead )/Hall; rewrite addnS -{1}(addn1 (val + l)).
              by move => /InvMisc.addr_ltn.
          }
      }

    - {

        move=>[|ind] Hind /allP Hall.
        rewrite in_cons =>/orP [].

        - {
            move=>/eqP ->.
            move: (Hall _ (mem_tnth (Ordinal Hind) bf)).
            rewrite addnS -addSn => /InvMisc.addr_ltn H2.
            rewrite/incr_bit; move: (erefl _ ) => //=.
            rewrite {2 3}H2 //= =>_.
              by rewrite addSn -addnS; apply Hall; apply mem_tnth.
          }

        - {
            move=>/(mem_behead )/Hall; rewrite addnS -{1}(addn1 (val + l)).
              by move => /InvMisc.addr_ltn.
          }



          have Hind' : ind < m.+1; first by move: Hind=>/InvMisc.ltn_Snn.

          move: bf Hall => [[//=| b bf] Hbf] Hall.

          have Hbf': (size bf) == m.+1; first by move: (Hbf) =>/eqP //=.

          have->: (set_tnth (Tuple Hbf)
                            (incr_bit (tnth (Tuple Hbf) (Ordinal Hind)))
                  (Ordinal Hind)) = (
            [tuple of b ::
                   (set_tnth (Tuple Hbf') ((incr_bit (tnth (Tuple Hbf') (Ordinal Hind')))) (Ordinal Hind'))]
              ).

          {
            move=> //=.
            have->: (ntuple_head (Tuple Hbf)) = b; first by [].
            case: ind Hind Hind' => [|ind] Hind Hind'.

            - {

                
                have Heq: (Tuple Hbf') = (behead_tuple (Tuple Hbf)).
                {
                  rewrite/behead_tuple; move: (behead_tupleP _) => //= H2'.
                    by rewrite (proof_irrelevance _ Hbf' H2').              
                }



                have->:  (tnth (Tuple Hbf) (Ordinal Hind)) = (tnth (Tuple Hbf') (Ordinal Hind')).
                {
                  have->: (Tuple Hbf') = [tuple of behead (Tuple Hbf)]; first by [].
                  rewrite tnth_behead.
                  have->: (inord (Ordinal Hind').+1) = (Ordinal Hind).
                  {
                    rewrite/inord/insubd/odflt/oapp //=.
                    move: (insubT (fun i => i < m.+2)) ->.
                      by rewrite/Sub//=.              
                  }
                    by [].

                }
                move=>//=.
                rewrite 2!/[tuple of _].

                rewrite/ntuple_tail.
                move: (behead_tupleP (Tuple Hbf)) => //= H1.
                move: (behead_tupleP (Tuple H1)) => //= H2.
                move: (behead_tupleP (Tuple Hbf')) => //= H3.
                rewrite (proof_irrelevance _ H2 H3); clear H2.
                  by move: (valP _) => //= H2.
              }

            - {
                rewrite/ntuple_tail.
                move: (behead_tupleP (Tuple Hbf)) => //= H1.
                move: (behead_tupleP (Tuple H1)) => //= H2.
                move: (behead_tupleP (Tuple Hbf')) => //= H3.
                rewrite (proof_irrelevance _ H2 H3); clear H2.
                have->:  (tnth (Tuple Hbf) (Ordinal Hind)) = (tnth (Tuple Hbf') (Ordinal Hind')).
                {
                  have->: (Tuple Hbf') = [tuple of behead (Tuple Hbf)].
                  {
                    rewrite /[tuple of _] //=.
                    move: (behead_tupleP _) => //= H4.
                    rewrite (proof_irrelevance _ H4 Hbf') => //=.
                  }

                  rewrite tnth_behead.
                  have->: (inord (Ordinal Hind').+1) = (Ordinal Hind).
                  {
                    rewrite/inord/insubd/odflt/oapp //=.
                    move: (insubT (fun i => i < m.+2)) ->.
                      by rewrite/Sub//=.              
                  }
                    by [].
                }

                by rewrite (proof_irrelevance _ H1 Hbf') //=; clear H1.
              }

          }
                
        rewrite in_cons =>/orP [].
        - {
            move=>/eqP ->.
            have H1: (b \in (Tuple Hbf)); first by rewrite (tuple_eta (Tuple Hbf)) //= in_cons eq_refl.
            move: (Hall _ H1); rewrite addnS -{1}(addn1 (_ + l)).
              by move => /InvMisc.addr_ltn.
          }
        - {
            move=>/IHm IHm'; apply/IHm'; apply/allP=> b' Hb'.
            have H1: (b' \in (Tuple Hbf));
              first by rewrite (tuple_eta (Tuple Hbf)) //= in_cons Hb' Bool.orb_true_r.
            by move: (Hall _ H1).
          }
       }
Qed.
      
  Lemma countingbloomfilter_add_internal_incr l (bf: CountingBloomFilter) (inds: seq 'I_(Hash_size.+1)):
    length inds == l ->
    countingbloomfilter_free_capacity bf l ->
    countingbloomfilter_bitcount bf + l =
    countingbloomfilter_bitcount (countingbloomfilter_add_internal inds bf).
    Proof.

      elim: l bf inds => [| l IHl] bf .
      - by move=> [|//=] _ _ //=; rewrite addn0.
      - {
          move=> [//=| ind inds] Hlen Hfree //= .
          rewrite -IHl.
          apply  countingbloomfilter_bitcount_incr =>//=.
          - by move/eqP:Hlen => //= [->].

          - {
              apply/allP => val Hval; move: Hfree Hval; clear.
              by apply countingbloomfilter_add_capacity_decr.
            }
        }

    Qed.        

End CountingBloomFilter.
