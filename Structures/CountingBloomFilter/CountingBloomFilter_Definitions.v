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

From ProbHash.Computation
     Require Import Comp Notationv1.

From ProbHash.Core
     Require Import Hash HashVec FixedList.

From ProbHash.BloomFilter
     Require Import BloomFilter_Definitions BloomFilter_Probability.

Module CountingBloomFilterDefinitions (Spec:HashSpec).

  Module BloomFilterProbability := (BloomFilterProbability Spec).
  Export BloomFilterProbability.


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

    Lemma Hngt0: n.+1 > 0.
    Proof. by []. Qed.
    
    Variable Hkgt0: k >0.
    (*
     list of hash functions used in the bloom filter
     *)
    Definition CountVector := (Hash_size.+1).-tuple 'I_n.+1.

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

    Definition incr_bit (value: 'I_n.+1) : 'I_n.+1 :=
      (if value.+1 < n.+1 as b return ((value.+1 < n.+1) = b -> 'I_n.+1)
       then (fun b0 => Ordinal b0)
       else (fun _ => value)) (erefl (value.+1 < n.+1)).

    Lemma decr_bitP m : m.+1 < n.+1 -> m < n.+1.
    Proof. by rewrite -{1}addn1 => /InvMisc.addr_ltn. Qed.

    Definition decr_bit (value: 'I_n.+1) : 'I_n.+1 :=
      match value with
        Ordinal 0 Hm => Ordinal Hm
      | Ordinal m.+1 Hm => Ordinal (decr_bitP Hm)
      end.
    
    Definition countingbloomfilter_set_bit (value: 'I_(Hash_size.+1)) bf : CountingBloomFilter :=
      mkCountingBloomFilter
        (set_tnth (counting_bloomfilter_state bf)
                  (incr_bit (tnth (counting_bloomfilter_state bf) value))
                  value).

    Definition countingbloomfilter_unset_bit (value: 'I_(Hash_size.+1)) bf : CountingBloomFilter :=
      mkCountingBloomFilter
        (set_tnth (counting_bloomfilter_state bf)
                  (decr_bit (tnth (counting_bloomfilter_state bf) value))
                  value).

    Definition countingbloomfilter_get_bit (value: 'I_(Hash_size.+1)) bf : bool :=
      (tnth (counting_bloomfilter_state bf) value) > 0.

    Fixpoint countingbloomfilter_add_internal (items: seq 'I_(Hash_size.+1)) bf : CountingBloomFilter :=
      match items with
        h::t => countingbloomfilter_add_internal t (countingbloomfilter_set_bit h bf)
      | [::]   => bf
      end.

    Fixpoint countingbloomfilter_remove_internal (items: seq 'I_(Hash_size.+1)) bf : CountingBloomFilter :=
      match items with
        h::t => countingbloomfilter_remove_internal t (countingbloomfilter_unset_bit h bf)
      | [::]   => bf
      end.

    Definition countingbloomfilter_add (value: hash_keytype) (hashes: k.-tuple (HashState n)) (bf: CountingBloomFilter) : Comp [finType of (k.-tuple (HashState n)) * CountingBloomFilter] :=
      hash_res <-$ (hash_vec_int value hashes);
        let (new_hashes, hash_vec) := hash_res in
        let new_bf := countingbloomfilter_add_internal (tval hash_vec) bf in
        ret (new_hashes, new_bf).

    Definition countingbloomfilter_remove (value: hash_keytype) (hashes: k.-tuple (HashState n)) (bf: CountingBloomFilter) : Comp [finType of (k.-tuple (HashState n)) * CountingBloomFilter] :=
      hash_res <-$ (hash_vec_int value hashes);
        let (new_hashes, hash_vec) := hash_res in
        let new_bf := countingbloomfilter_remove_internal (tval hash_vec) bf in
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
      all (fun a => (nat_of_ord a) + l < n.+1) (tval (counting_bloomfilter_state bf)).

    Definition countingbloomfilter_used_capacity (bf: CountingBloomFilter) l :=
      all (fun a => l < (nat_of_ord a)) (tval (counting_bloomfilter_state bf)).

    Definition countingbloomfilter_new :  CountingBloomFilter.
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
    
    Lemma countingbloomfilter_new_empty_bitcount (Hngt0: n.+1 > 0):
      countingbloomfilter_bitcount (countingbloomfilter_new) = 0.
    Proof.
      rewrite/countingbloomfilter_bitcount //=; rewrite add0n.
        by elim: Hash_size => [//=| m IHm] //=.
    Qed.

    Lemma incr_bit_valid ind (Hngt0: n > 0):
      0 < incr_bit ind.
    Proof.
      rewrite /incr_bit.
      move: n  ind Hngt0 => [//=[]//=|//= ];clear n.
      move=> n [m Hm].
      move: (erefl _ ) => //=.
      case Hltn: (m < n.+1).
      - {
          have Hltn': (m.+1 < n.+2); first by apply InvMisc.ltn_SnnP.
            by rewrite {2 3}Hltn' //=.
        }
      - {
          have Hltn': (m.+1 < n.+2) = false;
          first by case Hltn'': (_ < _) => //=;move/InvMisc.ltn_SnnP: Hltn'' Hltn ->.
          rewrite {2 3}Hltn' //= => _.
          move/Bool.negb_true_iff: Hltn; rewrite leqNgt Bool.negb_involutive => Hn.
            by move: (InvMisc.ltnSn_eq _ _ Hm Hn)=>/eqP ->.
        }
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
              val + l < n.+1.
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

    Lemma countingbloomfilter_add_internal_decr m l (bf: CountingBloomFilter) (inds: seq 'I_(Hash_size.+1)):
      length inds == l ->
      countingbloomfilter_free_capacity bf l ->
      countingbloomfilter_used_capacity bf (m + l) ->
      countingbloomfilter_used_capacity (countingbloomfilter_add_internal inds bf) m.
    Proof.
      elim: l m bf inds => [| l IHl] m bf .
      - by move=> [|//=] _ _ //=; rewrite addn0.
      - {
          move=> [//=| ind inds] Hlen Hfree Hused //= .
          apply IHl => //=.
          - rewrite/countingbloomfilter_free_capacity; apply/allP => v Hv.
              by apply (@countingbloomfilter_add_capacity_decr l bf ind ) => //=.
          - rewrite/countingbloomfilter_used_capacity; apply/allP => v Hv.
            move: Hv; move=>/tnthP [v_ind ->]; clear v.

            case Hvind: (v_ind == ind); last first.
            {
              move/Bool.negb_true_iff: Hvind => Hvind; rewrite tnth_set_nth_neq //=.              
              move/allP: Hused => Hused; move: (Hused _ (mem_tnth v_ind (counting_bloomfilter_state bf)) ).
              by rewrite addnS -addn1 =>/InvMisc.addr_ltn.
            }
            {
              move/eqP: Hvind => ->; rewrite tnth_set_nth_eq; clear v_ind.
              rewrite/incr_bit; move: (erefl _); case: {2 3}(_ < _) => //= Htnth.
              move/allP: Hused => Hused; move: (Hused _ (mem_tnth ind (counting_bloomfilter_state bf)) ).
                by rewrite addnS -addn1 =>/InvMisc.addr_ltn/(ltn_addr 1); rewrite addn1.
              move/allP: Hused => Hused; move: (Hused _ (mem_tnth ind (counting_bloomfilter_state bf)) ).
                by rewrite addnS -addn1 =>/InvMisc.addr_ltn.
               by [].
            }
        }
    Qed.        


    Lemma countingbloomfilter_new_capacity l :
      l < n.+1 -> countingbloomfilter_free_capacity (countingbloomfilter_new ) l.
    Proof.
      move=> Hlen; rewrite/countingbloomfilter_new/countingbloomfilter_free_capacity//=.
      rewrite add0n; apply/andP; split => //=.
      apply/allP => val.
        by rewrite mem_nseq =>/andP [Hgt0 /eqP ->] //=.
    Qed.

    Lemma countingbloomfilter_add_capacity_change m l bf values: 
      length values == m ->
      countingbloomfilter_free_capacity bf (m  + l) ->
      @countingbloomfilter_free_capacity (countingbloomfilter_add_internal values bf) l.
    Proof.
      rewrite /countingbloomfilter_free_capacity//=.
      move: values bf m k  ; clear k Hkgt0.
      elim => [//=| val vals Hvals] bf [//=|].
      - by move=> n' k' Hk' /eqP.
      - {
          move=> m k Hlen Hall //=.
          apply (@Hvals _ m k).
          - by move/eqP: Hlen => [->].
          - apply/allP => ind.
            move: Hall.
            move: (@countingbloomfilter_add_capacity_decr (m + l) bf val ind).
              by rewrite /countingbloomfilter_free_capacity//=.
        }
    Qed.

    Lemma countingbloomfilter_set_exchange bf ind ind':
      countingbloomfilter_set_bit ind'
                                  (countingbloomfilter_set_bit ind bf) =
      countingbloomfilter_set_bit ind
                                  (countingbloomfilter_set_bit ind' bf).
      Proof.

        have H v: (counting_bloomfilter_state ({| counting_bloomfilter_state := v |})) = v; first by [].
        case Hindeq: (ind == ind'); first by move/eqP: Hindeq <-; clear ind'.
        move/Bool.negb_true_iff: Hindeq => Hindeq.
        rewrite/countingbloomfilter_set_bit !H; rewrite !tnth_set_nth_neq; try by []; try by rewrite eq_sym.
        apply f_equal.
        apply eq_from_tnth => pos.
        case Hpos: (pos == ind').
        - {
            move/eqP:Hpos ->; clear pos.
            rewrite tnth_set_nth_eq; try by []; rewrite tnth_set_nth_neq; try by []; try by rewrite eq_sym.
            rewrite tnth_set_nth_eq; try by []; try by rewrite eq_sym.
          }
        case Hpos': (pos == ind).
        - {
            move/eqP:Hpos' Hpos ->; clear pos => _.
            rewrite tnth_set_nth_neq; try by []; rewrite tnth_set_nth_eq; try by []; rewrite tnth_set_nth_eq; try by [].
          }
          move/Bool.negb_true_iff: Hpos => Hpos; move/Bool.negb_true_iff: Hpos' => Hpos'.
          by do !(rewrite tnth_set_nth_neq; try by []).
      Qed.

    Lemma countingbloomfilter_add_internal_set_exchange (bf: CountingBloomFilter) ind inds:
      countingbloomfilter_add_internal inds (countingbloomfilter_set_bit ind bf) =
           (countingbloomfilter_set_bit  ind (countingbloomfilter_add_internal inds bf)).
    Proof.
      elim: inds bf ind => [| ind' inds Hinds] bf ind //=.
      by rewrite 3!Hinds countingbloomfilter_set_exchange.
    Qed.
    Lemma countingbloomfilter_set_unset_idempotent (bf: CountingBloomFilter) (ind: 'I_(Hash_size.+1)):
      (tnth  (counting_bloomfilter_state bf) ind).+1 < n.+1 ->
      countingbloomfilter_unset_bit ind (countingbloomfilter_set_bit ind bf) = bf.
    Proof.
      have H v: (counting_bloomfilter_state ({| counting_bloomfilter_state := v |})) = v; first by [].
      move: bf => [bf]; rewrite/countingbloomfilter_unset_bit/countingbloomfilter_set_bit !H => Htnth; apply f_equal.
      rewrite tnth_set_nth_eq; try by [].
      apply eq_from_tnth => pos.
      case Hposeq: (pos == ind).
      - {
          move/eqP:Hposeq => ->; clear pos.
          rewrite tnth_set_nth_eq; try by [].
          rewrite/incr_bit/decr_bit //=; move: (erefl _ ) => //=.
          case Heq: {-}((tnth bf ind).+1 < n.+1) => //=.
          - {
              rewrite {2 3}Heq => He.
              by move: (decr_bitP He); case: (tnth bf ind) => //= i H1 H2; rewrite (proof_irrelevance _ H1 H2).
            }
          - {
              rewrite {2 3}Heq => //=.
              by case: (tnth bf ind) Heq Htnth => //= [[| m] ] //= Hm ->.
            }
        }
      - by move/Bool.negb_true_iff: Hposeq => Hposeq; do !(rewrite tnth_set_nth_neq; try by []).
    Qed.

    Lemma countingbloomfilter_add_remove_idempotent l (bf: CountingBloomFilter) (inds: seq 'I_(Hash_size.+1)):
      length inds == l ->
      countingbloomfilter_free_capacity bf l ->
      bf = countingbloomfilter_remove_internal inds (countingbloomfilter_add_internal inds bf).
    Proof.
      move=>/eqP <-; elim: inds bf => [ //= | ind inds IHinds] bf //= /allP Hin.
      rewrite countingbloomfilter_add_internal_set_exchange.
      rewrite countingbloomfilter_set_unset_idempotent; first
        by rewrite -IHinds //=; apply/allP => v Hv; move: (Hin v Hv); rewrite addnS -addn1 => /InvMisc.addr_ltn.

      move: (@countingbloomfilter_add_capacity_change (length inds) 1 bf inds (eq_refl (length inds))).
      rewrite/countingbloomfilter_free_capacity addn1; move/allP: Hin => Hin /(_ Hin)/allP Hin'.
      by move: (Hin' _ (mem_tnth ind _)); rewrite addn1.
    Qed.
    
    Lemma countingbloomfilter_add_preserve (bf: CountingBloomFilter) (inds inds': seq 'I_(Hash_size.+1)): (n > 0) ->
      countingbloomfilter_query_internal inds bf ->
      countingbloomfilter_query_internal inds 
         (countingbloomfilter_add_internal inds' bf).
    Proof.
      have H v: (counting_bloomfilter_state ({| counting_bloomfilter_state := v |})) = v; first by [].
      move=> Hngt0; rewrite/countingbloomfilter_query_internal => /allP Hall; elim: inds' => [//=|]; first by move/allP: Hall.
      move=> ind' inds' Hinds' //=; apply/allP => v Hv.
      rewrite  countingbloomfilter_add_internal_set_exchange.
      rewrite/countingbloomfilter_get_bit/countingbloomfilter_set_bit !H.
      case Hvind: ( v == ind').
      - by rewrite tnth_set_nth_eq //=; apply incr_bit_valid.
      - {
          move/Bool.negb_true_iff: Hvind => Hvind; rewrite tnth_set_nth_neq //=.
          by move/allP: Hinds' => /(_ v Hv).
        }
    Qed.
    
    Section OfBloomFilter.

      Variable Hngt0 : n > 0.

      Definition toBitVector (vec: CountVector) : BitVector.
        generalize vec; unfold CountVector; intro vec'.
        apply (map_tuple (fun (cnt:'I_n.+1) => cnt > 0) vec').
      Defined.

      Definition toBloomFilter (cbf: CountingBloomFilter) : BloomFilter :=
        mkBloomFilter (toBitVector (counting_bloomfilter_state cbf)).

      Lemma countingbloomfilter_bloomfilter_query_eq cbf inds :
        countingbloomfilter_query_internal inds cbf = bloomfilter_query_internal  inds (toBloomFilter cbf).
      Proof.
        rewrite/countingbloomfilter_query_internal/bloomfilter_query_internal.
        apply eq_in_all => ind Hind.
        rewrite /countingbloomfilter_get_bit/bloomfilter_get_bit/toBloomFilter.
          by rewrite tnth_map.
      Qed.



      Lemma countingbloomfilter_bloomfilter_set_bitC cbf ind:
        toBloomFilter (countingbloomfilter_set_bit ind cbf) = bloomfilter_set_bit ind (toBloomFilter cbf).
      Proof.
        rewrite/toBloomFilter/bloomfilter_set_bit; apply f_equal.
        apply eq_from_tnth => ind'; rewrite tnth_map.
        case Heqind': (ind' == ind).
        - rewrite tnth_set_nth_eq //= /countingbloomfilter_set_bit/countingbloomfilter_set_bit.
          rewrite tnth_set_nth_eq //=.
            by apply incr_bit_valid.
        - move/Bool.negb_true_iff:Heqind' =>Heqind'; rewrite tnth_set_nth_neq //=.
          rewrite /countingbloomfilter_set_bit/countingbloomfilter_set_bit tnth_set_nth_neq //=.
            by rewrite tnth_map //=.
      Qed.
      

      
      Lemma countingbloomfilter_bloomfilter_add_internalC cbf inds :
        toBloomFilter (countingbloomfilter_add_internal inds cbf) =
        (bloomfilter_add_internal inds (toBloomFilter cbf)).
      Proof.
        elim: inds cbf => [//=| ind inds Hinds cbf //=].
        rewrite Hinds; apply f_equal => //=; clear Hinds inds.
          by rewrite countingbloomfilter_bloomfilter_set_bitC.
      Qed.
      


      Lemma counting_bloomfilter_new_bloomfilter_eq:
        (toBloomFilter (countingbloomfilter_new)) = bloomfilter_new.
      Proof.
        rewrite/toBloomFilter/countingbloomfilter_new/bloomfilter_new //=; apply f_equal.
        rewrite/toBitVector //=.
        move: (eq_ind_r _ _ _) (eq_ind_r _ _ _) => //= H1 H2.
        rewrite/map_tuple; move: (map_tupleP _ _ ) => //=.
        rewrite map_nseq.
        have ->: ((0 < Ordinal (Hngt0))) = false; first by []; move=>H3.
          by rewrite (proof_irrelevance _ H1 H3).
      Qed.
      
      

    End OfBloomFilter.

  End CountingBloomFilter.
End CountingBloomFilterDefinitions.

