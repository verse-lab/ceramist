From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path bigop finfun binomial.

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path .

From infotheo
     Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From BloomFilter
     Require Import Parameters Hash Comp Notationv1 BitVector BloomFilter InvMisc bigop_tactics FixedList seq_ext seq_subset FixedMap rsum_ext.

(*
Proof idea
----------

1. if hashstate_find value hash_state is None, then the output of the hash function is uniformly distributed from 0..Hash_size.+1
2. folding on a list of values such that all the values are not-equal ensures that hashstate_find value is always None
3. after insert, probability of all hash functions not setting a bit is (1 - 1/(Hash_size.+1))^k.
4. after k inserts,  probability of all hash functions not setting a bit is (1 - 1/(Hash_size.+1))^kn.
5. after k inserts,  probability of all hash functions setting a bit is 1 - (1 - 1/(Hash_size.+1))^kn.



 *)

Open Scope R_scope.




Lemma bloomfilter_set_bitC bf ind ind':
  (bloomfilter_set_bit ind (bloomfilter_set_bit ind' bf)) =
  (bloomfilter_set_bit ind' (bloomfilter_set_bit ind bf)).
Proof.
  rewrite /bloomfilter_set_bit/bloomfilter_state//.
  apply f_equal => //.
  apply eq_from_tnth => pos.
  case Hpos: (pos == ind); case Hpos': (pos == ind').
  - by rewrite !FixedList.tnth_set_nth_eq.
  - rewrite FixedList.tnth_set_nth_eq; last by [].
    rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos' ->.
      by rewrite FixedList.tnth_set_nth_eq; last by [].
  - rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos ->.
    rewrite FixedList.tnth_set_nth_eq; last by [].
      by rewrite FixedList.tnth_set_nth_eq; last by [].

  - rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos ->.  
    rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos' ->.
    rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos' ->.  
      by rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos ->.
Qed.


Lemma bloomfilter_add_internal_hit bf (ind: 'I_Hash_size.+1) hshs :
  (ind \in hshs) ->
  (tnth (bloomfilter_state (bloomfilter_add_internal hshs bf)) ind).
Proof.
  elim: hshs bf  => //= hsh hshs IHs bf.

  rewrite in_cons => /orP [/eqP -> | H]; last by apply IHs.

  clear IHs ind.
  elim: hshs bf hsh => //.
  - rewrite /bloomfilter_add_internal/bloomfilter_set_bit/bloomfilter_state //.
      by move=> bf hsh; rewrite FixedList.tnth_set_nth_eq => //=.
  - move=> hsh hshs IHs bf hsh'.    
    move=> //=.
    rewrite bloomfilter_set_bitC .
      by apply IHs.
Qed.

Lemma bloomfilter_add_internal_preserve bf ind hshs:
  tnth (bloomfilter_state bf) ind ->
  tnth (bloomfilter_state (bloomfilter_add_internal hshs bf)) ind.
Proof.

  elim: hshs bf ind => //= hsh hshs IHs bf ind Htnth.
  apply IHs.
  rewrite /bloomfilter_set_bit/bloomfilter_state //.
  case Hhsh: (ind == hsh).
  - by rewrite FixedList.tnth_set_nth_eq //=.
  - rewrite FixedList.tnth_set_nth_neq; first by move: Htnth; rewrite/bloomfilter_state//=.
      by move/Bool.negb_true_iff: Hhsh.
Qed.


Lemma bloomfilter_add_internal_miss
      bf (ind: 'I_Hash_size.+1) hshs :
  ~~ tnth (bloomfilter_state bf) ind ->
  ~~ ( ind \in hshs) ->
  (~~ tnth (bloomfilter_state (bloomfilter_add_internal hshs bf)) ind).
Proof.

  move=> Htnth.
  elim: hshs bf Htnth => //= hsh hshs IHs bf Htnth.
  move=> H; move: (H).
  rewrite in_cons.
  rewrite negb_or => /andP [Hneq Hnotin].
  apply IHs.
  rewrite /bloomfilter_state/bloomfilter_set_bit.
  rewrite FixedList.tnth_set_nth_neq => //=.
  exact Hnotin.
Qed.


Lemma bloomfilter_add_internal_hit_infer bf (ind: 'I_Hash_size.+1) inds:
  ~~ bloomfilter_get_bit ind bf ->
  tnth (bloomfilter_state (bloomfilter_add_internal inds bf)) ind ->
  ind \in inds.
Proof.
  move=> Hbit Htnth.
  case Hind: (ind \in inds) =>//=; move/Bool.negb_true_iff: Hind => Hind.
    by move/Bool.negb_true_iff: (bloomfilter_add_internal_miss Hbit Hind) Htnth ->.
Qed.




Lemma hash_vec_insert_length n l (value: hash_keytype) (hashes: l.-tuple (HashState n)) (inds: l.-tuple 'I_Hash_size.+1):
  size (map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
               let (hash,ind) := pair in @hashstate_put _ value ind hash)
            (zip (tval hashes) (tval inds))) == l.
Proof.
    by rewrite size_map size_zip !size_tuple /minn ltnn //=.
Qed.


Lemma hash_vec_insert_length_consP n l (value: hash_keytype)
      (hashes: seq (HashState n)) (hash: HashState n) (Hhashes: size (hash :: hashes) == l.+1)
      (inds: seq 'I_Hash_size.+1) (ind: 'I_Hash_size.+1) (Hind: size (ind :: inds) == l.+1) :
  Tuple (hash_vec_insert_length value (Tuple Hhashes) (Tuple Hind)) =
  cons_tuple
    (@hashstate_put _ value ind hash) 
    (Tuple (hash_vec_insert_length value (Tuple (cons_sizeP  Hhashes)) (Tuple (cons_sizeP Hind)))).
Proof.

  move: (cons_sizeP  _ ) => //= Hhashes'.
  move: (cons_sizeP  _) => //= Hinds'.
  move: (hash_vec_insert_length _ _ _) => Hinsert'.

  move: (Hinsert') => Hinsert; move: Hinsert'.
  have:    (map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                   let (hash,ind) := pair in @hashstate_put _ value ind hash)
                (zip (Tuple Hhashes) (Tuple Hind))) = 
           (hashstate_put n value ind hash) :: (map
                                                 (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                                                    let (hash,ind) := pair in @hashstate_put _ value ind hash)
                                                 (zip (Tuple Hhashes') (Tuple Hinds'))).
    by [].
    move=> ->; move: Hinsert =>  H1 H2.
    rewrite (proof_irrelevance _ H1 H2); clear H1.
    erewrite tuple_eta; case Heq: [tuple of _ :: _] => [[//=| x xs] Hxs].

    move: Heq.
    rewrite theadE.

    have: behead_tuple
            (cons_tuple (hashstate_put n value ind hash)
                        (Tuple (hash_vec_insert_length value (Tuple Hhashes') (Tuple Hinds')))) = (Tuple (hash_vec_insert_length value (Tuple Hhashes') (Tuple Hinds'))).

    rewrite /behead_tuple //=; move:  (hash_vec_insert_length _ _ _) (behead_tupleP _ ) => //= H3 H4.
      by rewrite (proof_irrelevance _ H3 H4).

      move=>-> [Heqx Heqxs].

      move: Hxs H2; rewrite Heqx Heqxs => //= Ha Hb.
        by rewrite (proof_irrelevance _ Ha Hb).

Qed.


Definition hash_vec_contains_value n l (value: hash_keytype) (hashes: l.-tuple (HashState n)) (inds: l.-tuple 'I_Hash_size.+1) : bool :=
  all (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
         let (hash,ind) := pair in @hashstate_find _ value hash == Some ind)
      (zip (tval hashes) (tval inds)).

Lemma hash_vec_contains_value_preserve n l (value value': hash_keytype) (hashes: l.-tuple (HashState n)) (inds inds': l.-tuple 'I_Hash_size.+1) : value != value' ->
                                                                                                                                                  hash_vec_contains_value value hashes inds ->
                                                                                                                                                  hash_vec_contains_value value (Tuple (hash_vec_insert_length value' hashes inds')) inds.
Proof.

  move=> Hvalueq Hcontains; move: Hcontains inds'.
  elim: l  hashes inds => [|l IHl]  hashes inds Hcontains inds' //=.
    by rewrite !tuple0/hash_vec_contains_value //= !zip_empty_r //=.
    move: (IHl (behead_tuple hashes) (behead_tuple inds)) Hcontains.
    rewrite (tuple_eta inds) (tuple_eta hashes) (tuple_eta inds') //=.
    rewrite /hash_vec_contains_value //= => IHl' /andP [Hsh_eq /IHl' IH].
    apply/andP;split; last by apply IH => //=.
    clear IH IHl IHl'.

    move: Hsh_eq; rewrite /hashstate_find/hashstate_put //=.

    case: hashes => [[|hshs hshses] Hhshs] //=.
    case: inds' => [[|ind' inds'] Hinds'] //=.
    case: inds => [[|ind inds] Hinds] //=.
    have ->: (thead (Tuple Hhshs)) = hshs; first by [].
    have ->: (thead (Tuple Hinds')) = ind'; first by [].
    have ->: (thead (Tuple Hinds)) = ind; first by [].
    move: Hvalueq; clear.
    elim: n hshs => [//=|n IHn] hshs.
    move=>//=.

    rewrite  /FixedList.ntuple_head (tuple_eta hshs) !theadE !ntuple_tailE.

    case: hshs => [[| hsh hshs] Hhshs] //=.
    have ->:  thead (Tuple Hhshs) = hsh; first by [].

    case: hsh Hhshs => [[k v]|] Hshsh //=; last first.
  - {
      move=> Hneq; move: (Hneq); rewrite eq_sym =>/Bool.negb_true_iff -> //=.
      move: Hshsh (eq_ind _ _ _ _ _ )  => //= H1 H2.
      rewrite/ FixedList.ntuple_tail/behead_tuple (proof_irrelevance _ H1 H2) //=.
      move: (behead_tupleP _ ) (behead_tupleP _) => //= H3 H4.
        by rewrite (proof_irrelevance _ H3 H4) //=.
    }
  - {
      case Hkeq: (k == value).
      - {
          move/eqP: Hkeq => -> /Bool.negb_true_iff ->.
            by rewrite ntuple_head_consE eq_refl.
        }
      - {
          case Hkeq': (k == value').
          - {
              move: Hshsh (eq_ind _ _ _ _ _) =>//= H1 H2.
              rewrite /FixedList.ntuple_tail /behead_tuple.
              move: (behead_tupleP _) (behead_tupleP _) => //= H3 H4.
                by rewrite (proof_irrelevance _ H3 H4) eq_sym =>/Bool.negb_true_iff ->.
            }
          - {
              rewrite ntuple_head_consE Hkeq.
              rewrite ntuple_tail_consE.
                by move=> Hneq Hfind; apply IHn => //=.
            }
        }
    }
Qed.    



Lemma hash_vec_contains_value_base n l (value: hash_keytype) (hashes: l.-tuple (HashState n)) (inds
                                                                                               : l.-tuple 'I_Hash_size.+1) : 
  all (fun hsh => FixedList.fixlist_length hsh + 1 <= n) hashes ->
  hash_vec_contains_value value (Tuple (hash_vec_insert_length value hashes inds)) inds.
Proof.

  elim: l  hashes inds => [|l IHl]  hashes inds //=.
    by rewrite !tuple0/hash_vec_contains_value //= !zip_empty_r //=.

    move=> /allP Hhashes.
    have H1: all
               (fun hsh : FixedList.fixlist [eqType of hash_keytype * hash_valuetype] n =>
                  FixedList.fixlist_length hsh + 1 <= n) (behead_tuple hashes).
    {
      apply/allP => ind Hind; apply Hhashes => //=.
        by move: Hind; rewrite (tuple_eta hashes) //= in_cons => ->; rewrite Bool.orb_true_r //=.    
    }

    move: (IHl (behead_tuple hashes) (behead_tuple inds) H1); clear IHl H1.
    rewrite (tuple_eta inds) (tuple_eta hashes) //=.
    rewrite /hash_vec_contains_value //= => H1; apply/andP; split=>//=; last first.
    clear H1.
    have: (thead hashes \in hashes); first by rewrite (tuple_eta hashes) in_cons theadE eq_refl//=.
    move=>/(Hhashes (thead hashes)); clear Hhashes.
    move: (thead hashes) (thead inds); clear hashes inds l.
    elim: n => [//= | n IHn].
  - {
      move=> hsh ind; rewrite addn1 //=.
    }

  - {

      move=> [[//=| hsh hshs] Hhshs] inds //=.
      have ->: FixedList.ntuple_head (Tuple Hhshs) = hsh; first by [].

      case: hsh Hhshs => //= [[k v]|] Hshsh.
      - {
          case Hkeq: (k == value) => //=.
          - by rewrite eq_refl.
          - {
              rewrite /FixedList.ntuple_head //= ntuple_head_consE Hkeq.
              rewrite ntuple_tail_consE => Hlen.
                by apply IHn => //=.
            }
        }

      - {
            by rewrite eq_refl.
        }
    }
Qed.










Definition stirling_no_2 (kn i: nat):=
  Rdefinitions.Rinv (Factorial.fact i) *R* (
    \sum_(j in 'I_i) (((Rdefinitions.Ropp 1) ^R^ j) *R*
                      ('C (i, j) %R) *R*
                      ((j %R) ^R^ kn)
                     )
  ).



Axiom second_stirling_number_sum: forall l k m (f: nat -> Rdefinitions.R),
    (\sum_(inds in [finType of (l * k).-tuple 'I_m.+1])
      ((Rdefinitions.Rinv (m.+1 %R) ^R^ l * k) *R*
       (f (length (undup inds)))) ) =
    \sum_(len in [finType of 'I_(l * k)])
     (f(len) *R*
      ( ('C ((l * k), len) %R) *R*
        (Factorial.fact len %R) *R* (stirling_no_2 (l * k) len) *R*
        (Rdefinitions.Rinv (m.+1 %R) ^R^ (l * k))
     )).













Section Hash.

  Lemma hash_uni n (hash_state: HashState n) value (hash_value: 'I_Hash_size.+1) :
    (hashstate_find _ value hash_state == None) ->
    (
      P[ ((hash n value hash_state) |> (fun h => ret (snd h ))) === hash_value ] =
      ((1 %R) /R/ (#|ordinal Hash_size.+1| %R))
    ).
  Proof.
    move=>/eqP Hhsfindnone; rewrite /hash Hhsfindnone //= DistBindA //= DistBindp1.
    rewrite (functional_extensionality (fun x : 'I_Hash_size.+1 => DistBind.d (Dist1.d (hashstate_put n value x hash_state, x)) (fun b : HashState n * 'I_Hash_size.+1 => Dist1.d b.2)) (fun x : 'I_Hash_size.+1 => Dist1.d x)); first last.
      by move=> x; rewrite DistBind1f //=.
        by  rewrite DistBindp1 Uniform.dE div1R  //=.
  Qed.

End Hash.



Lemma hash_vecP n l (value: hash_keytype) (hashes: l.-tuple (HashState n))
      (inds: l.-tuple 'I_Hash_size.+1) (Huns: all (fun hsh => FixedMap.fixmap_find value hsh == None) hashes) :
  d[ hash_vec_int value hashes ] (Tuple (hash_vec_insert_length value hashes inds), inds) =
  ((Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l).
Proof.

  elim: l value hashes inds Huns => [//=| l IHl].
  - by move=> value [[|//=] Hlen] [[|//=] Hinds]; rewrite Dist1.dE //=.

  - move=> //= value [[//=| x xs] Hxs] [[//=| y ys] Hys] Huns; rewrite DistBind.dE.   
    erewrite <- (IHl value (FixedList.ntuple_tail (Tuple Hxs))).
    rewrite /FixedList.ntuple_tail; move: (behead_tupleP _) => //= Hlen.

    transitivity (
        \sum_(hshs in [finType of l.-tuple (HashState n)])
         \sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
         \sum_(hsh in hashstate_of_finType n)
         \sum_(ind in ordinal_finType Hash_size.+1)
         ((d[ hash_vec_int value (Tuple Hlen)]) (hshs, inds) *R*
          ((d[ hash n value (thead (Tuple Hxs))]) (hsh, ind) *R*
           ([&& (hsh == hashstate_put n value y x ) &&
                (hshs == Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs)) (Tuple (cons_sizeP Hys)))),
             ind == y
             & inds == Tuple (cons_sizeP Hys)] %R)
         ))
      ).
    rewrite rsum_split.
    apply eq_bigr => hshs _; apply eq_bigr => inds _ //=; rewrite DistBind.dE //=.
    rewrite mulRC rsum_Rmul_distr_r rsum_split.
    apply eq_bigr => hsh _; apply eq_bigr => ind _ //=.
    apply f_equal; apply f_equal => //=; rewrite Dist1.dE.
    rewrite xpair_eqE.
    rewrite hash_vec_insert_length_consP.
    rewrite !xcons_eqE.
    have: (Tuple Hys = cons_tuple y (Tuple (cons_sizeP Hys))).
    rewrite (tuple_eta (cons_tuple _ _)) //= theadE; case Heq: [tuple of _] => [[//=| y' ys'] Hys'].
    move: Heq => [Heqy' Heqys'].
    move: Hys'; rewrite -Heqy' -Heqys'; move: Hys => H1 H2.
      by rewrite (proof_irrelevance _ H1 H2).
      move=>->; rewrite xcons_eqE.

      rewrite eq_sym; apply f_equal; apply f_equal.

      case: (_ == _); rewrite ?Bool.andb_true_l ?Bool.andb_false_l//=.
      rewrite eq_sym.
      case: (_ == _); rewrite ?Bool.andb_true_l ?Bool.andb_false_l //=.
      rewrite eq_sym.
        by case: (_ == _); rewrite ?Bool.andb_true_l ?Bool.andb_false_l//=. 
        have H x1 y1 z1 : (y1 = (0 %R)) -> x1 = z1 -> x1 +R+ y1 = z1. by move=> -> ->; rewrite addR0.
        transitivity (
            \sum_(hshs in [finType of l.-tuple (HashState n)])
             \sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
             ((d[ hash_vec_int value (Tuple Hlen)]) (hshs, inds) *R*
              ((d[ hash n value (thead (Tuple Hxs))]) (hashstate_put n value y x, y) *R*
               ([&& (hshs == Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs))
                                                           (Tuple (cons_sizeP Hys))) ) & inds ==  Tuple (cons_sizeP Hys)] %R)))
          ).                
  - apply eq_bigr => hshs _; apply eq_bigr => inds _.
    rewrite (bigID (fun hsh => hsh == hashstate_put n value y x)) big_pred1_eq eq_refl //=.

    apply H.
  - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
    apply prsumr_eq0P => ind' Hind'; first by dispatch_Rgt.
      by rewrite //= !mulR0.

      rewrite (bigID (fun ind => ind == y)) big_pred1_eq eq_refl //=.

      apply H.
  - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
      by rewrite !Bool.andb_false_l Bool.andb_false_r //= !mulR0.
        by [].     

        transitivity (
            ((d[ hash_vec_int value (Tuple Hlen)]) (Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs)) (Tuple (cons_sizeP Hys))), Tuple (cons_sizeP Hys)) *R*
             ((d[ hash n value (thead (Tuple Hxs))]) (hashstate_put n value y x, y)))
          ).
        rewrite (bigID (fun hshs => hshs == Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs)) (Tuple (cons_sizeP Hys))))) big_pred1_eq eq_refl //=.

        apply H.
  - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
    apply prsumr_eq0P => ind' Hind'; first by dispatch_Rgt.
      by rewrite //= !mulR0.

      rewrite (bigID (fun inds => inds == Tuple (cons_sizeP Hys))) big_pred1_eq eq_refl //=.                  apply H.
  - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
      by rewrite //= !mulR0.
        by rewrite mulR1.

        move: (cons_sizeP _) => Hlen'; rewrite (proof_irrelevance _ Hlen' Hlen); clear Hlen'.
        apply Logic.eq_sym; rewrite mulRC.
        apply f_equal.

        move: Huns => /allP Huns.

        have H1: (x \in Tuple Hxs). by rewrite in_cons eq_refl //=.
        move /eqP: (Huns x H1) => Hx.
        have: (thead (Tuple Hxs)) = x. by [].
        move=>->; rewrite /hash/hashstate_find Hx //= DistBind.dE.
        apply Logic.eq_sym.

        transitivity (
            \sum_(a in [finType of 'I_Hash_size.+1])
             (\sum_(a0 in ordinal_finType Hash_size.+1)
               ((Uniform.d (size_enum_equiv (size_enum_ord Hash_size.+1))) a0 *R* (Dist1.d a0) a) *R*
              ((hashstate_put n value y x == hashstate_put n value a x) && (a == y) %R))
          ).
        apply eq_bigr => a _.
          by rewrite DistBind.dE Dist1.dE xpair_eqE (eq_sym y).

          rewrite (bigID (fun a => a == y)) big_pred1_eq eq_refl //=.   
          apply H.

  - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first (dispatch_Rgt; move=>_; dispatch_Rgt).
      by rewrite Bool.andb_false_r //= mulR0.

      rewrite eq_refl //= mulR1. 

      transitivity (
          \sum_(a0 in 'I_Hash_size.+1)
           ((Uniform.d (size_enum_equiv (size_enum_ord Hash_size.+1))) a0 *R* (a0 == y %R))
        ).
        by apply eq_bigr => a' _; rewrite Dist1.dE eq_sym.

        rewrite (bigID (fun a0 => a0 == y)) big_pred1_eq //= eq_refl mulR1 //=.
        apply H.

  - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by dispatch_Rgt.
      by rewrite mulR0.
        by rewrite Uniform.dE card_ord.

        rewrite /FixedList.ntuple_tail //=.
          by move: Huns => //= =>/andP [].
Qed.


Lemma neg_hash_vecP n l (value: hash_keytype) (hashes hashes': l.-tuple (HashState n))
      (inds: l.-tuple 'I_Hash_size.+1)
      (Huns: all (fun hsh => FixedMap.fixmap_find value hsh == None) hashes)
  : (tval hashes' != map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                            let (hash,ind) := pair in
                            @hashstate_put _ value ind hash) (zip (tval hashes) (tval inds))) ->
    d[ hash_vec_int value hashes ] (hashes', inds) =
    (0 %R).
Proof.


  elim: l value hashes hashes' inds Huns => [//=| l IHl].
  - move=> value hashes hashes' inds.
    have: (hashes == [tuple]); last move=> /eqP ->; first by case: hashes => [[]] //=.
    have: (hashes' == [tuple]); last move=> /eqP ->; first by case: hashes' => [[]] //=.
    have: (inds == [tuple]); last move=> /eqP ->; first by case: inds => [[]] //=.
      by clear hashes hashes' inds => //=.

  - move=> //= value [[//=| x xs] Hxs] [[//=| y ys] Hys] [[//=| z zs] Hzs] /allP Huns; rewrite DistBind.dE //=.   

    rewrite negb_consP =>/orP [Hyneq | Hysneq].

    transitivity (  
        \sum_(hshs' in tuple_finType l (hashstate_of_finType n))
         \sum_(bf' in tuple_finType l (ordinal_finType Hash_size.+1))
         (
           (d[ hash_vec_int value (FixedList.ntuple_tail (Tuple Hxs))]) (hshs', bf') *R* 
           (
             \sum_(hshs'' in hashstate_of_finType n)
              \sum_(ind' in ordinal_finType Hash_size.+1)
              \sum_(ind'' in [finType of 'I_Hash_size.+1])
              (0%R)
           )

      )).
  - rewrite rsum_split; apply eq_bigr => hshs' _; apply eq_bigr => bf' _ //=.
    have: (thead (Tuple Hxs)) = x; last move=> ->; first by [].
    apply f_equal; rewrite DistBind.dE rsum_split.
    apply eq_bigr => hshs'' _; apply eq_bigr => ind' _ //=.
    rewrite /hash/hashstate_find Dist1.dE.
    case Hteq: ((_,_) == _); last by rewrite bigsum_card_constE //= !mulR0.
    move/eqP: Hteq => [<- _ <- _ ] //=; rewrite mulR1.
    have Hin: (x \in Tuple Hxs); first by rewrite (tuple_eta (Tuple Hxs)) //= in_cons; apply/orP;left. 
    move/eqP: (Huns x Hin) -> => //=; rewrite DistBind.dE.
    apply eq_bigr => ind'' _; rewrite Dist1.dE xpair_eqE.
    case Hz: (z == ind''); last by rewrite Bool.andb_false_r //= mulR0.
      by move/eqP: Hz <-; move/Bool.negb_true_iff: Hyneq -> => //=; rewrite mulR0.  
        by do ? [
                (apply prsumr_eq0P; intros; first by dispatch_Rgt; intros; dispatch_Rgt)|
                (apply RIneq.Rmult_eq_0_compat_l)
              ].

        apply prsumr_eq0P => [[hshs' bf']|] ; first by dispatch_Rgt; case; intros; dispatch_Rgt.  
        move=> [hshs' bf'] _; case Heq: (tval hshs' == ys); last first.
  - apply RIneq.Rmult_eq_0_compat_l => //=; rewrite DistBind.dE.
    apply prsumr_eq0P => [[hshs'' ind']|[hshs'' ind']] _; first by dispatch_Rgt.
    rewrite //= Dist1.dE xpair_eqE //=; apply RIneq.Rmult_eq_0_compat_l => //=.
    suff: (Tuple Hys == [tuple of hshs'' :: hshs']) = false; first by move => -> //=.
    rewrite (tuple_eta (Tuple Hys)).
    have: (thead (Tuple Hys)) = y; last move=> -> //=; first by  [].
    move: Heq; clear=> Heq.
    rewrite !tupleE xcons_eqE //= /behead_tuple.
    move: (behead_tupleP _) => //= Hys' //=.
    move: hshs' Heq => [hshs' Hhshs'] //= Hneq.
    suff: (Tuple Hys' == Tuple Hhshs') = false; first by move=>->; rewrite Bool.andb_false_r.
      by rewrite tuple_eq_inj eq_sym Hneq.
      case Hbfeq: (tval bf' == zs); last first.      
  - apply RIneq.Rmult_eq_0_compat_l => //=; rewrite DistBind.dE.
    apply prsumr_eq0P => [[hshs'' ind']|[hshs'' ind']] _; first by dispatch_Rgt.
    rewrite //= Dist1.dE xpair_eqE //=; apply RIneq.Rmult_eq_0_compat_l => //=.
    suff: (Tuple Hzs == [tuple of ind' :: bf']) = false; first by move => ->; rewrite Bool.andb_false_r //=.
    rewrite (tuple_eta (Tuple Hzs)).
    have: (thead (Tuple Hzs)) = z; last move=> -> //=; first by  [].
      by rewrite tuple_eq_inj eqseq_cons [zs == _]eq_sym Hbfeq Bool.andb_false_r.
      apply RIneq.Rmult_eq_0_compat_r; apply IHl;move/eqP:Heq=>Heq;move/eqP:Hbfeq=>Hbfeq; rewrite ?Heq ?Hbfeq //=.
      clear IHl.
        by apply/allP => x' Hx'; apply Huns=> //=; rewrite in_cons;apply/orP;right.

Qed.


Lemma hash_vec_simpl (n' k': nat) (hashes: k'.-tuple (HashState n')) value inds f :
  all (fun hsh : FixedMap.fixmap hash_keytype hash_valuetype n' => FixedMap.fixmap_find value hsh == None) hashes ->
  (\sum_(hshs' in [finType of k'.-tuple (HashState n')])
    ((d[ hash_vec_int value hashes]) (hshs', inds) *R* (f hshs'))) =
  ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k') *R* (f (Tuple (hash_vec_insert_length value hashes inds)))).
Proof.
  move=> Hall.
  rewrite (bigID (fun hshs' => hshs' == (Tuple (hash_vec_insert_length value hashes inds)))) big_pred1_eq//=.

  under big i Hneq rewrite neg_hash_vecP ?mul0R //=.
  rewrite bigsum_card_constE mulR0 addR0.
  rewrite hash_vecP //=.
Qed.


Lemma hash_vec_find_simpl n l (value: hash_keytype) (hashes hashes': l.-tuple (HashState n))
      (inds inds': l.-tuple 'I_Hash_size.+1):
  hash_vec_contains_value value hashes inds ->
  d[ hash_vec_int value hashes ] (hashes', inds') =
  ((hashes' == hashes) && (inds' == inds) %R).
Proof.
  elim: l hashes inds hashes'  inds' => [//=| l IHl].
  - by do ?(case; case => //=; intro); move=> _ //=; rewrite Dist1.dE xpair_eqE //= !tuple0 //=.
  - move=> [[//=| hash hashes] Hhashes] [[//=| ind inds] Hinds] [[//=| hash' hashes'] Hhashes']  [[//=|ind' inds'] Hinds'] //=.
    rewrite DistBind.dE rsum_split //=.
    have H1: (thead (Tuple Hhashes)) = hash; first by [].
    under big a _ under big b _ rewrite H1.
    move: (IHl (FixedList.ntuple_tail (Tuple Hhashes)) (FixedList.ntuple_tail (Tuple Hinds))) => IHl' /allP Hcontains.
    under big a H3 under big b H4 rewrite IHl' ?boolR_distr -?mulRA.
    {
      rewrite exchange_big; under big b _ rewrite -rsum_pred_demote big_pred1_eq.
      rewrite -rsum_pred_demote big_pred1_eq //=.
      rewrite DistBind.dE rsum_split //=.

      under big a _ under big b _ rewrite Dist1.dE xpair_eqE//=.

      have Heq (a: HashState n) (b: 'I_Hash_size.+1):
        (Tuple Hhashes' == [tuple of a :: (FixedList.ntuple_tail (Tuple Hhashes))])
          && (Tuple Hinds' == [tuple of b :: FixedList.ntuple_tail (Tuple Hinds)]) =
        ((a == hash') && (b == ind') &&
                      ((FixedList.ntuple_tail (Tuple Hhashes')) == (FixedList.ntuple_tail (Tuple Hhashes))) &&
                      ((FixedList.ntuple_tail (Tuple Hinds')) == (FixedList.ntuple_tail (Tuple Hinds)))
        ).
      {
        have ->: (Tuple Hhashes') = ([tuple of hash' :: (FixedList.ntuple_tail (Tuple Hhashes'))]).
        {
          rewrite (tuple_eta (Tuple Hhashes')) //=.
          rewrite!/[tuple of _] //=; move: (valP _) =>//= H8; move: (valP _ )=>//=H9.
            by rewrite (proof_irrelevance _ H8 H9).        
        }
        rewrite xcons_eqE eq_sym -andbA -andbA -andbA; apply f_equal.
        have ->: (Tuple Hinds') = ([tuple of ind' :: (FixedList.ntuple_tail (Tuple Hinds'))]).
        {
          rewrite (tuple_eta (Tuple Hinds')) //=.
          rewrite!/[tuple of _] //=; move: (valP _) =>//= H8; move: (valP _ )=>//=H9.
            by rewrite (proof_irrelevance _ H8 H9).        
        }
        rewrite xcons_eqE andbC eq_sym -andbA //=; apply f_equal.
          by rewrite !ntuple_tailE //= andbC //=.
      }

      under big a _ under big b _ rewrite Heq !boolR_distr mulRC -!mulRA.

      rewrite exchange_big; under big a _ rewrite -rsum_pred_demote big_pred1_eq.
      rewrite -rsum_pred_demote big_pred1_eq //=.
      rewrite/Hash.hash //=.

      have ->: (Tuple Hhashes' == Tuple Hhashes) && (Tuple Hinds' == Tuple Hinds) =
      (hash == hash') && (ind == ind') &&
                      (FixedList.ntuple_tail (Tuple Hhashes') == FixedList.ntuple_tail (Tuple Hhashes)) &&
                      (FixedList.ntuple_tail (Tuple Hinds') == FixedList.ntuple_tail (Tuple Hinds)).
      {
        rewrite (tuple_eta (Tuple Hhashes')) (tuple_eta (Tuple Hhashes)) (tuple_eta (Tuple Hinds)) (tuple_eta (Tuple Hinds'))  //=.
        rewrite !ntuple_tailE //=.
        have -> : (thead (Tuple Hhashes')) = hash'; first by [].
        have -> : (thead (Tuple Hhashes)) = hash; first by [].
        have -> : (thead (Tuple Hinds')) = ind'; first by [].
        have -> : (thead (Tuple Hinds)) = ind; first by [].
        apply Logic.eq_sym.

        transitivity (
            ((hash' == hash) && (behead_tuple (Tuple Hhashes') == behead_tuple (Tuple Hhashes))) &&
                                                                                                 ((ind' == ind) && (behead_tuple (Tuple Hinds') == behead_tuple (Tuple Hinds)))
          ).

        {
          rewrite -andbA -andbA -andbA eq_sym; apply f_equal.
          rewrite andbC -andbA; apply f_equal.
            by rewrite andbC eq_sym.
        }
          by rewrite -!xcons_eqE //=.
      }
      rewrite andbC andbA andbC !boolR_distr; do? apply f_equal.
      have Hin: ((hash, ind) \in zip (Tuple Hhashes) (Tuple Hinds)); first by rewrite //= in_cons eq_refl //=.
        by move: (Hcontains (hash,ind) Hin) =>/eqP -> //=; rewrite Dist1.dE eq_sym xpair_eqE boolR_distr //=.
        
    }
    {

      apply/allP => [[hsh_tail ind_tail]] //= Hin.

      have Hin': (hsh_tail, ind_tail) \in zip (Tuple Hhashes) (Tuple Hinds); first by rewrite//= in_cons Hin Bool.orb_true_r.
        by move: (Hcontains (hsh_tail, ind_tail) Hin').

    }
Qed.







  Lemma hash_vec_int_id' (n' k': nat) (hashes: k'.-tuple (HashState n')) value inds ps :
    all (fun y => FixedList.fixlist_length y + 1 <= n') hashes ->
    (d[ hash_vec_int  value (Tuple (hash_vec_insert_length value hashes inds))])
      (ps, inds) = (ps == (Tuple (hash_vec_insert_length value hashes inds)) %R).
  Proof.

    move: (hash_vec_insert_length _ _ _) => //=.
    elim: k' n'  inds hashes ps => [//=|k' IHk'] n' [[//=| x xs] Hxs] [[//=|y ys] Hys] ps Hprf Hprf'' //=.
    move: Hprf => //= H0; rewrite Dist1.dE xpair_eqE //=.
    apply Logic.eq_sym; case Heq: (_ == _) => //=.
      by move/eqP: Heq ->; case: ps => //= [//= []] //=; rewrite tuple0 //=.
        by case: ps Heq  => //= [//= []] //= Hprf.

        case: ps => //= [//=[]]; (try by []); move=>  p ps Hps.
        rewrite /FixedList.ntuple_tail.
        move: (behead_tupleP _ ) => //= Hprf'.
        rewrite DistBind.dE.
        rewrite rsum_split //=; under big a _ under big b _ rewrite DistBind.dE.

        under big a _ under big b _ rewrite rsum_split //=.
        under big a _ under big b _ under big c _ under big d _ rewrite Dist1.dE xpair_eqE //=.

        have Hsusp1 (c: HashState n') (a: k'.-tuple (HashState n')) : ( (Tuple Hps) ==  [tuple of c :: a]) = ((p == c) && (ps == a)).
          by rewrite/[tuple of _] //=.
          have Hsusp2 (d: 'I_Hash_size.+1) (b: k'.-tuple 'I_Hash_size.+1) : ( (Tuple Hxs) ==  [tuple of d :: b]) = ((x == d) && (xs == b)).
            by rewrite/[tuple of _] //=.
            under big a _ under big b _ under big c _ under big d _ rewrite Hsusp1 Hsusp2 !boolR_distr eq_sym mulRC -mulRA -mulRA -mulRA.
            under big a _ under big b _ rewrite exchange_big.
            under big a _ under big b _ under big c _ rewrite -rsum_pred_demote big_pred1_eq //=.

            under big b _ under big c _ under big d _ rewrite mulRC eq_sym -mulRA.
            under big b _ under big c _ rewrite -rsum_pred_demote big_pred1_eq.

            under big b _ under big c _ rewrite mulRC -mulRA -mulRA eq_sym.

            have H (c: k'.-tuple 'I_Hash_size.+1): (tval c == xs) = (c == (behead_tuple (Tuple Hxs))).
              by rewrite/behead_tuple //=.

              (under big b _ under big c _ rewrite H); clear H.
              under big b _ rewrite -rsum_pred_demote big_pred1_eq//=.
              have H (b: k'.-tuple (HashState n')): (tval b == ps) = (b == (behead_tuple (Tuple Hps))).
                by rewrite/behead_tuple //=.

                under big b _ rewrite mulRC -mulRA  eq_sym H.
                rewrite -rsum_pred_demote big_pred1_eq.

                move: (IHk' n' (behead_tuple (Tuple Hxs)) (behead_tuple (Tuple Hys)) (behead_tuple (Tuple Hps))) =>//=.
                move=> /(_ Hprf') -> //=; clear IHk'.
                rewrite /hash //=.

                have ->: ((thead (Tuple Hprf)) = (hashstate_put n' value x y)); first by move=>//=.
                rewrite hash_find_insert_involutive //= ?Dist1.dE ?xpair_eqE ?eq_refl //=.
                rewrite ?Bool.andb_true_r.

                have ->: ((Tuple Hps == Tuple Hprf) = ((thead (Tuple Hps)== thead (Tuple Hprf))
                                                         && (behead_tuple (Tuple Hps) == (Tuple Hprf'))));
                  move=>//=.
                  by rewrite !boolR_distr;apply Logic.eq_sym; rewrite mulRC; apply f_equal => //=.
                    by move: Hprf'' => //= /andP [] //=.
                      by move: Hprf'' => //= /andP [] //=.
  Qed.


  Lemma hash_vec_int_id (n' k': nat) (hashes: k'.-tuple (HashState n')) value inds ps qs :
 all (fun y => FixedList.fixlist_length y + 1 <= n') hashes ->
                                                                                        (d[ hash_vec_int  value (Tuple (hash_vec_insert_length value hashes inds))])
                                                                                          (ps, qs) = ((ps == (Tuple (hash_vec_insert_length value hashes inds))) && (qs == inds) %R).
  Proof.

    move=> Hall.

    case Heq: (qs == inds).
  - {
      rewrite Bool.andb_true_r.
                             by move/eqP:Heq ->; rewrite hash_vec_int_id'.      
                           }

                           - rewrite Bool.andb_false_r //=.
                             move: (hash_vec_insert_length _ _ _) Heq Hall => //=.
                             elim: k' n'  inds hashes ps qs => [//=|k' IHk'] n' [[//=| x xs] Hxs] [[//=|y ys] Hys] ps qs Hprf Hprf''' Hprf''  //=.
                             move: Hprf => //= H0; rewrite Dist1.dE xpair_eqE //=.
                             apply Logic.eq_sym; case Heq: (_ == _) => //=.

                               by move: Hxs Hprf''' => //=; rewrite !tuple0 => Hxs //=.

                               case: ps => //= [//=[]]; (try by []); move=>  p ps Hps.
  rewrite /FixedList.ntuple_tail.
                                                                                    move: (behead_tupleP _ ) => //= Hprf'.
                                                                                    rewrite DistBind.dE.
                                                                                    rewrite rsum_split //=; under big a _ under big b _ rewrite DistBind.dE.

                                                                                    under big a _ under big b _ rewrite rsum_split //=.
                                                                                    under big a _ under big b _ under big c _ under big d _ rewrite Dist1.dE xpair_eqE //=.

                                                                                    have Hsusp1 (c: HashState n') (a: k'.-tuple (HashState n')) : ( (Tuple Hps) ==  [tuple of c :: a]) = ((p == c) && (ps == a)).
                                                                                      by rewrite/[tuple of _] //=.
                                                                                      have Hsusp2 (d: 'I_Hash_size.+1) (b: k'.-tuple 'I_Hash_size.+1) : ( (Tuple Hxs) ==  [tuple of d :: b]) = ((x == d) && (xs == b)).
  by rewrite/[tuple of _] //=.

                                                                                                                                                                                                                      under big a _ under big b _ under big c _ under big d _ rewrite Hsusp1 !boolR_distr eq_sym mulRC -mulRA -mulRA.
                                                                                                                                                                                                                      under big a _ under big b _ rewrite exchange_big.
                                                                                                                                                                                                                      under big a _ under big b _ under big c _ rewrite -rsum_pred_demote big_pred1_eq //=.

                                                                                                                                                                                                                      rewrite exchange_big.
                                                                                                                                                                                                                      under big a _ under big b _ rewrite !rsum_Rmul_distr_l ?rsum_Rmul_distr_r. 

                                                                                                                                                                                                                      under big a _ rewrite exchange_big; under big c _ under big d _ rewrite mulRC eq_sym -mulRA.

                                                                                                                                                                                                                      have Hd' (d: k'.-tuple (HashState n')): ((tval d == ps)) = (d == behead_tuple (Tuple Hps)).
                                                                                                                                                                                                                        by rewrite /behead_tuple //=.

                                                                                                                                                                                                                        have Hq' (c: 'I_Hash_size.+1) (a: k'.-tuple ('I_Hash_size.+1)):
                                                                                                                                                                                                                          (qs == [tuple of c :: a]) = ((c == thead qs) && (a == behead_tuple qs)).
                                                                                                                                                                                                                        {
                                                                                                                                                                                                                          rewrite/cons_tuple; rewrite -xcons_eqE eq_sym //=; rewrite (tuple_eta qs).
                                                                                                                                                                                                                          rewrite !theadE !beheadE//= ; case: qs Hprf''' => [[| q qs] Hqs] Hprf'''//=.
                                                                                                                                                                                                                        }

                                                                                                                                                                                                                        rewrite/[tuple of _ :: _] //=.
                                                                                                                                                                                                                        
                                                                                                                                                                                                                        move=>//=.
                                                                                                                                                                                                                        under big a _ under big b _ under big c _ rewrite Hd'.
                                                                                                                                                                                                                        under big a _ under big b _ rewrite -rsum_pred_demote  big_pred1_eq //=.

                                                                                                                                                                                                                        under big a _ under big b _  rewrite Hq' boolR_distr -mulRA -mulRA.
                                                                                                                                                                                                                        under big a _ rewrite -rsum_pred_demote big_pred1_eq.
                                                                                                                                                                                                                        rewrite -rsum_pred_demote big_pred1_eq.

                                                                                                                                                                                                                        clear Hq'.
                                                                                                                                                                                                                        case: qs Hprf''' => [[//=|q qs] Hqs]//= Hprf'''.
                                                                                                                                                                                                                        have: ((q :: qs) == (x :: xs)) = false; first by clear Hprf Hsusp2; move: Hqs Hxs Hprf''' => //=.

                                                                                                                                                                                                                        move=>/Bool.negb_true_iff; rewrite negb_consP =>/orP [Hneq| Heqf]; last first.

                           - {
                               move: (IHk' n' (behead_tuple (Tuple Hxs)) (behead_tuple (Tuple Hys)) (behead_tuple (Tuple Hps)) (behead_tuple (Tuple Hqs))) =>//= -> //=; first by rewrite mulR0.
                               clear Hprf Hsusp2 Hprf'''; move: Hqs Hxs Heqf =>//=.
                               rewrite/behead_tuple//= => Hqs Hxs Hneq; move: (behead_tupleP _) (behead_tupleP _) =>//= H1 H2.
                                 by rewrite tuple_eq_inj //=; apply /Bool.negb_true_iff.
                                   by move: Hprf'' => //= /andP [].
                             }
                           - {
                               rewrite mulR_eq0; left => //=; have ->: (thead (Tuple Hqs)) = q; first by [].
                               have ->: (thead (Tuple Hprf)) = hashstate_put n' value x y; first by [].
                               rewrite/hash.
                               rewrite hash_find_insert_involutive //= ?Dist1.dE ?xpair_eqE ?eq_refl //=.
                                 by move/Bool.negb_true_iff: Hneq ->; rewrite Bool.andb_false_r //=.
                                   by move: Hprf'' => //= /andP [] //=.
                             }

  Qed.


  

  Lemma hash_vec_simpl_inv' (n' k': nat) (hashes: k'.-tuple (HashState n')) value inds f :
    all
      (fun y : FixedList.fixlist [eqType of B * 'I_Hash_size.+1] n' =>
         FixedList.fixlist_length y + 1 <= n') hashes ->
    (\sum_(hshs' in [finType of k'.-tuple (HashState n')])
      ((d[ hash_vec_int  value (Tuple (hash_vec_insert_length value hashes inds))]) (hshs', inds) *R* (f hshs'))) =
    ((f (Tuple (hash_vec_insert_length value hashes inds)))).
  Proof.
    move=> H1.
    under big hshs' _ rewrite hash_vec_int_id' //=.
      by rewrite -rsum_pred_demote big_pred1_eq //=.
  Qed.

  



Module uniform_vec.
  Section definitions.
    Variable n k : nat.

    Definition pmf: pos_ffun [finType of k.-tuple 'I_n.+1].
      split with (finfun (fun a => (Rdefinitions.Rinv (n.+1 %R)) ^R^ k)).
      apply /forallP_leRP=> a //=.
        by rewrite ffunE; apply expR_ge0; left; apply RIneq.Rinv_0_lt_compat; apply ltR0n.
    Defined.

    Lemma pmfE a : pmf a = ((Rdefinitions.Rinv (n.+1 %R)) ^R^ k).
    Proof. by move=> //=;rewrite ffunE. Qed.


    Definition dist: dist [finType of (k.-tuple 'I_n.+1)].
      split with pmf.
      apply/eqP=> //=.
      under big a _ rewrite pmfE.
      rewrite bigsum_card_constE card_tuple card_ord -natRexp.
      rewrite -Rfunctions.Rinv_pow ?mulRV //=.
        by apply expR_neq0; apply/eqP; apply RIneq.not_0_INR.
          by apply RIneq.not_0_INR.
    Defined.

    Lemma dE  a : dist a = ((Rdefinitions.Rinv (n.+1 %R)) ^R^ k).
    Proof. by move=> //=;rewrite ffunE. Qed.

  End definitions.
End uniform_vec.

Section BloomFilter.

  (*
    k - number of hashes
   *)
  Variable k: nat.
  (*
    n - maximum number of hashes supported
   *)
  Variable n: nat.
  (* valid k *)
  Variable Hkgt0: k >0.

  (* the sequence of hash functions used to update the bloom filter *)
  Definition hash_vec := k.-tuple (HashState n).


  Definition hash_not_full (hsh: HashState n) : bool :=
    FixedList.fixlist_length hsh < n.

  Definition hash_unseen (b: B) (hsh: HashState n) : bool :=
    FixedMap.fixmap_find b hsh == None.

  Definition hash_has_free_spaces (s: nat) (hsh: HashState n) : bool :=
    FixedList.fixlist_length hsh + s <= n.

  Definition hashes_not_full (hashes: hash_vec) : bool :=
    (* provided the finite maps of all the hash function are not full*)
    all hash_not_full (tval hashes).

  Definition bloomfilter_value_unseen  (hashes: hash_vec)  (b: B) : bool :=
    (* provided the finite maps of all the hash function have not seen the value*)
    all (hash_unseen b) (tval hashes).

  Definition hashes_have_free_spaces  (hashes: hash_vec) (s: nat) : bool :=
    all (hash_has_free_spaces s) (tval hashes).
  

  Lemma bloomfilter_set_get_eq hash_value bf :  bloomfilter_get_bit hash_value (bloomfilter_set_bit hash_value bf).
  Proof.
      by rewrite /bloomfilter_get_bit/bloomfilter_set_bit// /bloomfilter_state FixedList.tnth_set_nth_eq //=.
  Qed.


  
  




  Lemma bloomfilter_add_internal_prob bf x l:
    ~~ tnth (bloomfilter_state bf) x ->
    \sum_(b in [finType of l.-tuple 'I_Hash_size.+1])
     ((tnth (bloomfilter_state (bloomfilter_add_internal b bf)) x %R) *R*
      ((Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l)) = 
    (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l)).
  Proof.
    elim: l x bf=> [|l IHl] x bf Hnth //=.
    rewrite subRR.
    rewrite unlock.

    have: (index_enum [finType of 0.-tuple 'I_Hash_size.+1]) = [tuple]::[::]; last move=>->//=.     
    rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
    rewrite -enumT //=; rewrite/(enum _)//=.
    rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
    move: (FinTuple.size_enum 0 (ordinal_finType Hash_size.+1))=> //=; rewrite expn0.
    move: (FinTuple.enum _ _)=>[|[[|//=] Hz] []]//= _.
      by move: (@tuple0  'I_Hash_size.+1 (Tuple Hz)) <- =>//=.
        by move/Bool.negb_true_iff: Hnth ->; rewrite //= mul0R add0R.     

        rewrite rsum_tuple_split rsum_split//=.
        rewrite (bigID (fun a => a == x)) big_pred1_eq //=.

        have: (\sum_(b in [finType of l.-tuple 'I_Hash_size.+1])
                ((tnth (bloomfilter_state (bloomfilter_add_internal b (bloomfilter_set_bit x bf))) x %R) *R*
                 (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) =
               \sum_(b in [finType of l.-tuple 'I_Hash_size.+1])
                ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l.+1)))).
        apply eq_bigr=> b _.
        rewrite bloomfilter_add_internal_preserve; first by rewrite mul1R//=.
        rewrite /bloomfilter_set_bit/bloomfilter_state.
          by rewrite FixedList.tnth_set_nth_eq.
          move=>->; rewrite bigsum_card_constE//=.

          have: (
                  \sum_(i < Hash_size.+1 | i != x) \sum_(b in [finType of l.-tuple 'I_Hash_size.+1])
                   ((tnth (bloomfilter_state (bloomfilter_add_internal b (bloomfilter_set_bit i bf))) x %R) *R*
                    (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))
                  = (\sum_(i < Hash_size.+1 | i != x)
                      (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ l))))); last move=>->.
          apply eq_bigr=> i Hneq.

          transitivity (
              Rdefinitions.Rinv (Hash_size.+1 %R) *R* 
              \sum_(b in [finType of l.-tuple 'I_Hash_size.+1])
               ((tnth
                   (bloomfilter_state
                      (bloomfilter_add_internal b (bloomfilter_set_bit i bf))) x %R) *R*
                ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) 
            ).
          rewrite rsum_Rmul_distr_l; apply eq_bigr=>b _.
            by rewrite mulRA mulRC mulRA mulRC; apply f_equal; rewrite mulRC; apply f_equal.
            rewrite IHl; first by [].
            rewrite (FixedList.tnth_set_nth_neq) //=.
              by rewrite eq_sym.
              rewrite bigsum_card_constE//=.
              rewrite card_tuple.
              rewrite cardC1 card_ord //=.


              have: (((Hash_size.+1 ^ l %R) *R*
                      (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) =
                     Rdefinitions.Rinv (Hash_size.+1 %R)
                    ); last move=>->.

              rewrite -{3}(mulR1 (Rdefinitions.Rinv _)) mulRA mulRC mulRA mulRC ; apply f_equal.
              rewrite -natRexp; clear; elim: l => [|l IHl] //=; rewrite ?mulR1//=.
              transitivity (
                  (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Hash_size.+1 %R)) *R*
                  (((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R* (((Hash_size.+1 %R) ^R^ l)))
                ).
              rewrite -mulRA -mulRA mulRC mulRA mulRC; apply f_equal.
              rewrite  mulRC mulRA mulRC; apply f_equal.
                by rewrite mulRC.
                rewrite !Raxioms.Rinv_l ?mul1R ?IHl //=.
                  by apply RIneq.not_0_INR =>//=.

                  rewrite !RIneq.Rmult_minus_distr_l.

                  rewrite addRA //= mulR1.

                  rewrite -{1}(mul1R (Rdefinitions.Rinv _)) -RIneq.Rmult_plus_distr_r.

                  have: (Rdefinitions.IZR 1 = (1 %R)); last move=>->; first by [].
                  rewrite -natRD add1n RIneq.Rinv_r //= .
                  rewrite addR_opp mulRA.

                  have: (((Hash_size %R) *R* Rdefinitions.Rinv (Hash_size.+1 %R))) = ((1 %R) -R- Rdefinitions.Rinv (Hash_size.+1 %R)); last move=>->.

                  rewrite -{2}(mulR1 (Rdefinitions.Rinv _)) //=.

                  have: (1 %R) = Rdefinitions.IZR 1; last move=>->; first by [].
                  rewrite -{1}(RIneq.Rinv_r (Hash_size.+1 %R)).
                  rewrite [(_.+1 %R) *R* Rdefinitions.Rinv _]mulRC.
                  rewrite -(RIneq.Rmult_minus_distr_l).
                  have: (Rdefinitions.IZR 1 = (1 %R)); last move=>->; first by [].
                    by rewrite -natRB //= subn1 //= mulRC.
                      by apply RIneq.not_0_INR =>//=.

                      
                      have: (1 %R) = Rdefinitions.IZR 1; last move=>->; first by [].
                        by [].
                          by apply RIneq.not_0_INR =>//=.
  Qed.





  (* for a given index ind *)

  Lemma bloomfilter_addn hashes (ind: 'I_(Hash_size.+1)) (bf: BloomFilter) (value: B):
    (* provided the bloom filter is not full *)
    hashes_not_full hashes ->
    (* and that the bloom filter has not set the value *)
    bloomfilter_value_unseen hashes value ->
    (* the bit in question is not set  *)
    ~~ bloomfilter_get_bit ind bf ->
    P[
        (
          (* bf' is the result of inserting into bf *)
          res <-$ bloomfilter_add  value hashes bf;
            let: (new_hashes, bf') := res in
            (* the probability of the given bit being set is *)
            ret (~~ bloomfilter_get_bit ind bf')
        )
      ] = 
    ((1 -R- Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ k).
  Proof.
    rewrite /bloomfilter_add/hashes_not_full/bloomfilter_value_unseen/hash_unseen /hash_not_full /bloomfilter_get_bit  => /allP Hnfl /allP Husn Hunset //= .  
    rewrite !DistBind.dE //=.

    transitivity (
        \sum_(exp_hashes in [finType of k.-tuple (HashState n)])
         \sum_(exp_bf in [finType of BloomFilter])
         \sum_(exp_hashes' in [finType of k.-tuple (HashState n)])
         \sum_(exp_bf' in [finType of k.-tuple 'I_Hash_size.+1])
         (((true == ~~ tnth (bloomfilter_state exp_bf) ind) %R) *R*
          ((d[ hash_vec_int value hashes]) (exp_hashes', exp_bf') *R*
           ((exp_hashes == exp_hashes') && (exp_bf == bloomfilter_add_internal exp_bf' bf) %R)))).
    - rewrite rsum_split.
      apply eq_bigr => exp_hashes _.
      apply eq_bigr => exp_bf _.
      rewrite DistBind.dE//= Dist1.dE rsum_Rmul_distr_r.
      rewrite rsum_split => //=.
      apply eq_bigr => exp_hashes' _.
      apply eq_bigr => exp_bf' _.
        by rewrite Dist1.dE//= xpair_eqE.

        transitivity (
            \sum_(exp_bf' in [finType of k.-tuple 'I_Hash_size.+1])
             \sum_(exp_hashes in [finType of k.-tuple (HashState n)])
             \sum_(exp_bf in [finType of BloomFilter])
             (((true == ~~ tnth (bloomfilter_state exp_bf) ind) %R) *R*
              ((d[ hash_vec_int value hashes]) (exp_hashes, exp_bf') *R*
               ((exp_bf == bloomfilter_add_internal exp_bf' bf) %R)))
          ).

    - apply Logic.eq_sym; rewrite exchange_big; apply eq_bigr => exp_hashes _ //=.
      rewrite exchange_big; apply eq_bigr => exp_bf _ //=.
      apply Logic.eq_sym; rewrite exchange_big; apply eq_bigr => exp_bf' _ //=.
      rewrite (bigID (fun exp_hashes' => exp_hashes' == exp_hashes)) //=.
      have H x y z : (y = (0 %R)) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
      apply H.
      apply prsumr_eq0P => exp_hashes' /Bool.negb_true_iff Heq; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
        by rewrite [exp_hashes == _]eq_sym Heq //= !mulR0.
        rewrite big_pred1_eq; do ?(apply f_equal).
          by rewrite eq_refl Bool.andb_true_l.
          

          transitivity (       
              \sum_(exp_bf in [finType of k.-tuple 'I_Hash_size.+1])
               \sum_(exp_hashes in [finType of k.-tuple (HashState n)])
               (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal exp_bf bf)) ind) %R) *R*
                ((d[ hash_vec_int value hashes]) (exp_hashes, exp_bf)))
            ).
    - apply eq_bigr => exp_bf _; apply eq_bigr => exp_hashes _.
      rewrite (bigID (fun exp_bf' => exp_bf' == (bloomfilter_add_internal exp_bf bf))).
      have H x y z : (y = (0 %R)) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
      apply H.
      apply prsumr_eq0P => exp_bf' /Bool.negb_true_iff -> //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
        by rewrite !mulR0.
          by rewrite big_pred1_eq eq_refl //= mulR1.
          (*
        Sum has now been simplified to simplest form:
         \sum_(hs in k.-tuple (HashState n))
            \sum_(hashs in k.-tuple 'I_Hash_size.+1)
               ((d[ hash_vec_int Hkgt0 value hashes (Hpredkvld Hkgt0)]) (hs, hashs) *R*
                (tnth (bloomfilter_state (bloomfilter_add_internal hashs bf)) ind %R)) =
         ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k %R))
           *)              
          (*
         It is also clear now why the probability is the the way it is - given that bit at ind is unset at the start,
         the probability it will be set after bloomfilter_add_internal is equal to the probability that all the k hashes
         produced by hash_vec_int are 0 (where each hash has a probability of 1 - 1/HashSize of not selecting ind
           *)

          move: (Hpredkvld Hkgt0).

          move:  Hkgt0 hashes Hnfl Husn; rewrite /hash_vec.
          elim: k   => //=.
          clear k Hkgt0.
          case=> [ _  |k IHk] Hkgt0 hashes Hnfl Husn.
    - move=> _ //=.
      rewrite mulR1.

      transitivity (
          \sum_(exp_bf in [finType of 1.-tuple 'I_Hash_size.+1])
           \sum_(exp_hashes in [finType of 1.-tuple (HashState n)])
           \sum_(hashes' in [finType of 0.-tuple (HashState n)])
           \sum_(values' in [finType of 0.-tuple 'I_Hash_size.+1])
           \sum_(hashes'' in hashstate_of_finType n)
           \sum_(values'' in ordinal_finType Hash_size.+1)
           ((((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal exp_bf bf)) ind) %R) *R*
             ((hashes' == [tuple]) && (values' == [tuple]) %R)) *R*
            ((d[ hash n value (thead hashes)]) (hashes'', values'') *R*
             ((exp_hashes == [tuple of hashes'' :: hashes']) && (exp_bf == [tuple of values'' :: values']) %R)))
        ).

    - apply eq_bigr => exp_bf _.
      apply eq_bigr => exp_hashes _.
      rewrite mulRC DistBind.dE rsum_Rmul_distr_r //=.
      rewrite rsum_split.
      apply eq_bigr => hashes' _.
      apply eq_bigr => values' _.
      rewrite Dist1.dE xpair_eqE //=.
      rewrite mulRA mulRC DistBind.dE !rsum_Rmul_distr_r.
      rewrite rsum_split.
      apply eq_bigr => hashes'' _.
      apply eq_bigr => values'' _ //=.
        by rewrite Dist1.dE xpair_eqE//=.

        transitivity (
            \sum_(exp_hashes in [finType of 1.-tuple (HashState n)])
             \sum_(hashes' in [finType of 0.-tuple (HashState n)])
             \sum_(values' in [finType of 0.-tuple 'I_Hash_size.+1])
             \sum_(hashes'' in hashstate_of_finType n)
             \sum_(values'' in ordinal_finType Hash_size.+1)
             ((((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal [tuple of values'' :: values'] bf)) ind)
                  %R) *R* ((hashes' == [tuple]) && (values' == [tuple]) %R)) *R*
              ((d[ hash n value (thead hashes)])
                 (hashes'', values'') *R*

               ((exp_hashes == [tuple of hashes'' :: hashes']) %R)))
          ).

    - rewrite exchange_big; apply eq_bigr => exp_hashes _.
      rewrite exchange_big; apply eq_bigr => hashes' _.
      rewrite exchange_big; apply eq_bigr => values' _.
      rewrite exchange_big; apply eq_bigr => hashes'' _.
      rewrite exchange_big; apply eq_bigr => values'' _.
      rewrite (bigID (fun i => i == [tuple of values'' :: values'])).

      have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
      apply H.

      apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
        by rewrite //= Bool.andb_false_r !mulR0.
          by rewrite big_pred1_eq eq_refl //= !Bool.andb_true_r.

          transitivity (
              \sum_(hashes'' in hashstate_of_finType n)
               \sum_(values'' in ordinal_finType Hash_size.+1)
               ((((true == ~~ tnth (bloomfilter_state (
                                        bloomfilter_add_internal [tuple of values'' :: [tuple]] bf)) ind) %R) *R*
                 ((d[ hash n value (thead hashes)])
                    (hashes'', values''))))
            ).                                 
    - rewrite exchange_big.
      rewrite (bigID (fun i => i == [tuple])) big_pred1_eq.
      have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
      apply H.

    - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by  dispatch_Rgt.
      apply prsumr_eq0P => i' _ //=; first by dispatch_Rgt.
      apply prsumr_eq0P => values' _ //=; first by dispatch_Rgt.
      apply prsumr_eq0P => hashes''  _ //=; first by dispatch_Rgt.
      apply prsumr_eq0P => values''  _ //=; first by dispatch_Rgt.
        by rewrite !mulR0 mul0R.

        rewrite exchange_big //= (bigID (fun i => i == [tuple])) big_pred1_eq //=. 
        apply H.
    - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=;  first by dispatch_Rgt. 
      apply prsumr_eq0P => i' _ //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
      apply prsumr_eq0P => values' _ //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
      apply prsumr_eq0P => hashes''  _ //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
        by rewrite !mulR0 mul0R.
        rewrite exchange_big; apply eq_bigr => hashes'' _.
        rewrite exchange_big; apply eq_bigr => values'' _.
        rewrite (bigID (fun i => i == [tuple hashes''])) big_pred1_eq //=.

        apply H.
    - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
        by rewrite !mulR0.
        rewrite mulR1; do ?(apply f_equal).
          by rewrite (eq_refl [tuple hashes'']) //= mulR1.

          rewrite /hash/hashstate_find.
          have Hthead: (thead hashes) \in hashes.
            by clear; rewrite (tuple_eta hashes) theadE//=; apply mem_head.
            move/eqP: (Husn (thead hashes) Hthead) ->.

            rewrite exchange_big (bigID (fun values'' => values'' == ind)).

            have H x y z: y = (0 %R) -> x = z -> y +R+ x = z.
              by move=> -> ->; rewrite add0R.

              apply H.
    - apply prsumr_eq0P => ind' /eqP ->; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
      rewrite bloomfilter_add_internal_hit //=.
      apply prsumr_eq0P => i' _; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
        by rewrite mul0R.
          by apply mem_head.

          transitivity ( 
              \sum_(i in 'I_Hash_size.+1 | i != ind)
               \sum_(i0 in hashstate_of_finType n)
               ((d[ rnd <-$ gen_random; ret (hashstate_put n value rnd (thead hashes), rnd)]) (i0, i))
            ).

    - apply eq_bigr => ind' /andP [_ Hnind].
      apply eq_bigr => vl _.
      rewrite bloomfilter_add_internal_miss.
        by rewrite eq_refl //= mul1R.
          by [].
            by rewrite mem_seq1 eq_sym. 

            move=> //=.               

            transitivity (
                \sum_(i < Hash_size.+1 | i != ind)
                 \sum_(hs in [finType of HashState n])
                 \sum_(hs' in [finType of 'I_Hash_size.+1])
                 \sum_(i' in ordinal_finType Hash_size.+1)
                 (((hs == hashstate_put n value hs' (thead hashes)) && (i == hs') %R) *R*
                  (Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R) *R* ((hs' == i') %R)))
              ).
    - apply eq_bigr => i Hneq.
      apply eq_bigr => hs _.
      rewrite DistBind.dE.
      apply eq_bigr => hs' _.
      rewrite DistBind.dE rsum_Rmul_distr_r.
      apply eq_bigr => i' _.
        by rewrite !Dist1.dE Uniform.dE xpair_eqE.

        transitivity (        
            \sum_(i < Hash_size.+1 | i != ind)
             \sum_(hs in [finType of HashState n])
             \sum_(i' in ordinal_finType Hash_size.+1)
             (((hs == hashstate_put n value i' (thead hashes)) && (i == i') %R) *R*
              (Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R)))
          ).

    - apply eq_bigr => i Hneq.
      apply eq_bigr => hs _.
      rewrite exchange_big; apply eq_bigr=> i' _.
      rewrite (bigID (fun i0 => i0 == i')) //= addRC.
      apply H.
    - apply prsumr_eq0P => i0 /Bool.negb_true_iff ->; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
        by rewrite //= !mulR0.

          by rewrite big_pred1_eq eq_refl //= mulR1; do ?(apply f_equal).
          transitivity (
              \sum_(i < Hash_size.+1 | i != ind)
               Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R)
            ).

    - apply eq_bigr => i Hneq.
      rewrite exchange_big (bigID (fun i' => i' == i)) //= addRC.
      apply H.
    - apply prsumr_eq0P => i0 /Bool.negb_true_iff Heq; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
      apply prsumr_eq0P => i1 _; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
        by rewrite eq_sym in Heq; rewrite Heq //= Bool.andb_false_r //= mul0R.
        rewrite big_pred1_eq.       
        rewrite (bigID (fun i0 => i0 == hashstate_put n value i (thead hashes))) big_pred1_eq //= addRC.

        apply H.
    - apply prsumr_eq0P => i0 /Bool.negb_true_iff ->; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
        by rewrite //= mul0R.

          by rewrite !eq_refl Bool.andb_true_l //= mul1R.       
          apply prsumr_sans_one => //=.
            by rewrite card_ord.
            rewrite bigsum_card_constE card_ord RIneq.Rinv_r //=.
              by apply RIneq.not_0_INR => //=.
              (* Base case completed *) 

              move=> Hpredkvld .
              rewrite -(IHk _ (FixedList.ntuple_tail hashes)); last first.
    - by rewrite -pred_Sn.
    - destruct hashes eqn: Hhashes => ls.
      clear Hnfl; move: tval i Hhashes Husn => [//= | x [//=| y xs]] Hprf Heq Hnfl.
      rewrite FixedList.ntuple_tail_coerce => Hin; apply Hnfl => //=.
        by move: Hin; rewrite [ls \in [:: x, y & xs]]in_cons /tval => ->; rewrite Bool.orb_true_r.

    - destruct hashes eqn: Hhashes => ls.
      clear Husn; move: tval i Hhashes Hnfl => [//= | x [//= | y xs]] Hprf Heq Husn.
      rewrite FixedList.ntuple_tail_coerce => Hin; apply Husn => //=.
        by move: Hin; rewrite [ls \in [:: x, y & xs]]in_cons /tval => ->; rewrite Bool.orb_true_r.
    - by apply ltn0Sn.
    - rewrite mulRC !rsum_Rmul_distr_r.
      transitivity (
          \sum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
           \sum_(ind' in 'I_Hash_size.+1)
           \sum_(h in hashstate_of_finType n)
           \sum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
           \sum_(exp_hashes in tuple_finType k.+1 (hashstate_of_finType n))
           \sum_(result in tuple_finType k.+1 (ordinal_finType Hash_size.+1))
           (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
            ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
             (d[ hash_vl <-$ hash n value (thead hashes);
                 (let (new_hsh_fun, result0) := hash_vl in
                  ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
               (cons_tuple h hs, cons_tuple ind' inds)))
        ).
    - rewrite rsum_tuple_split rsum_split exchange_big.
      apply eq_bigr => inds _.
      apply eq_bigr => ind' _.
      rewrite rsum_tuple_split rsum_split.
      apply eq_bigr => h _.
      apply eq_bigr => hs _.
      rewrite DistBind.dE mulRC rsum_Rmul_distr_r rsum_split.

      apply eq_bigr => exp_hashes _.
        by apply eq_bigr => result _.

        transitivity (
            \sum_(result in tuple_finType k.+1 (ordinal_finType Hash_size.+1))
             \sum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
             \sum_(ind' in 'I_Hash_size.+1)
             \sum_(h in hashstate_of_finType n)
             \sum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
             \sum_(exp_hashes in tuple_finType k.+1 (hashstate_of_finType n))
             (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
              ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
               (d[ hash_vl <-$ hash n value (thead hashes);
                   (let (new_hsh_fun, result0) := hash_vl in
                    ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                 (cons_tuple h hs, cons_tuple ind' inds)))
          ).

    - apply Logic.eq_sym.
      rewrite exchange_big; apply eq_bigr => inds _.
      rewrite exchange_big; apply eq_bigr => ind' _.
      rewrite exchange_big; apply eq_bigr => h _.
      rewrite exchange_big; apply eq_bigr => hs _.
        by rewrite exchange_big; apply eq_bigr => exp_hashes _.


        apply eq_bigr => result _.
        rewrite mulRC rsum_Rmul_distr_r.

        transitivity (
            \sum_(exp_hashes in tuple_finType k.+1 (hashstate_of_finType n))
             \sum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
             \sum_(ind' in 'I_Hash_size.+1)
             \sum_(h in hashstate_of_finType n)
             \sum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
             (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
              ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
               (d[ hash_vl <-$ hash n value (thead hashes);
                   (let (new_hsh_fun, result0) := hash_vl in
                    ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                 (cons_tuple h hs, cons_tuple ind' inds)))
          ).
    - apply Logic.eq_sym.
      rewrite exchange_big; apply eq_bigr => inds _.
      rewrite exchange_big; apply eq_bigr => ind' _.
      rewrite exchange_big; apply eq_bigr => h _.
        by rewrite exchange_big; apply eq_bigr => hs _.


        apply eq_bigr => exp_hashes _.


        transitivity (
            \sum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
             \sum_(ind' in 'I_Hash_size.+1)
             \sum_(h in hashstate_of_finType n)
             \sum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
             ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
              (((true ==
                 ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
               (d[ hash_vl <-$ hash n value (thead hashes);
                   (let (new_hsh_fun, result0) := hash_vl in
                    ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                 (cons_tuple h hs, cons_tuple ind' inds))
             )
          ).
    - apply eq_bigr => inds _.
      apply eq_bigr => ind' _.
      apply eq_bigr => h _.
      apply eq_bigr => hs _.
      rewrite mulRC -mulRA.
      apply f_equal.
        by rewrite mulRC.

        transitivity (
            (d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
            \sum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
             \sum_(ind' in 'I_Hash_size.+1)
             \sum_(h in hashstate_of_finType n)
             \sum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
             ((((true ==
                 ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
               (d[ hash_vl <-$ hash n value (thead hashes);
                   (let (new_hsh_fun, result0) := hash_vl in
                    ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                 (cons_tuple h hs, cons_tuple ind' inds))
             )
          ).

    - apply Logic.eq_sym.
      rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => inds _.
      rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => ind' _.
      rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => h _.
        by rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => hs _.

        apply Logic.eq_sym; rewrite mulRA mulRC; apply f_equal; apply Logic.eq_sym.


        transitivity (
            \sum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
             \sum_(ind' in 'I_Hash_size.+1)
             \sum_(h in [finType of HashState n])
             \sum_(hs in [finType of (k.+1).-tuple (HashState n)])
             \sum_(hs_fun' in hashstate_of_finType n)
             \sum_(result' in ordinal_finType Hash_size.+1)
             \sum_(hshs in [finType of 'I_Hash_size.+1])
             \sum_(hshs' in ordinal_finType Hash_size.+1)
             ((((true ==
                 ~~ tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit ind' bf))) ind)
                  %R) *R* ([&& (h == hs_fun') && (hs == exp_hashes), ind' == result' & inds == result] %R)) *R*
              ((((hs_fun', result') == (hashstate_put n value hshs (thead hashes), hshs)) %R) *R*
               (Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R) *R* ((hshs == hshs') %R))))

          ).
    - apply eq_bigr => inds _.
      apply eq_bigr => ind' _.
      apply eq_bigr => h _.
      apply eq_bigr => hs _.
      rewrite //= DistBind.dE mulRC rsum_Rmul_distr_r //=.
      rewrite rsum_split.
      apply eq_bigr => hs_fun' _.
      apply eq_bigr => result' _.
      rewrite /hash/hashstate_find.
      have Hhead: (thead hashes \in hashes). by rewrite (tuple_eta hashes) //= theadE; apply mem_head.
      move /eqP: (Husn (thead hashes) Hhead) ->.
      rewrite mulRC //= DistBind.dE !rsum_Rmul_distr_r.
      apply eq_bigr => hshs _.
      rewrite !Dist1.dE !DistBind.dE xpair_eqE !xcons_eqE mulRA mulRC !rsum_Rmul_distr_r.
      apply eq_bigr => hshs' _.
        by rewrite Uniform.dE Dist1.dE.


        rewrite (bigID (fun inds => inds == result)) //=.      

        have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
        apply H.

    - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move => [] //=.
      apply prsumr_eq0P => ind' _; first by dispatch_Rgt; move => [] //=.
      apply prsumr_eq0P => h _; first by dispatch_Rgt; move => [] //=.
      apply prsumr_eq0P => hs _; first by dispatch_Rgt; move => [] //=.
      apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move => [] //=.
      apply prsumr_eq0P => result' _; first by dispatch_Rgt; move => [] //=.
      apply prsumr_eq0P => hshs _; first by dispatch_Rgt; move => [] //=.
      apply prsumr_eq0P => hshs' _//=; first by dispatch_Rgt; move => [] //=.
        by rewrite !Bool.andb_false_r //= mulR0 mul0R.

        rewrite big_pred1_eq.        

        transitivity (
            \sum_(result' in 'I_Hash_size.+1)
             \sum_(ind' in 'I_Hash_size.+1)
             \sum_(h in [finType of HashState n])
             \sum_(hs in [finType of (k.+1).-tuple (HashState n)])
             \sum_(hs_fun' in [finType of HashState n])
             \sum_(hshs in 'I_Hash_size.+1)
             \sum_(hshs' in 'I_Hash_size.+1)
             ((((true == ~~ tnth
                            (bloomfilter_state
                               (bloomfilter_add_internal result (bloomfilter_set_bit ind' bf))) ind) %R) *R*
               ([&& (h == hs_fun') && (hs == exp_hashes), ind' == result'
                                                          & result == result] %R)) *R*
              ((((hs_fun', result') == (hashstate_put n value hshs (thead hashes), hshs)) %R) *R*
               (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
          ).

    - apply Logic.eq_sym.
      rewrite exchange_big; apply eq_bigr => ind' _.
      rewrite exchange_big; apply eq_bigr => h _.
      rewrite exchange_big; apply eq_bigr => hs _.
        by rewrite exchange_big; apply eq_bigr => hs_fun' _.

        transitivity (     
            \sum_(result' in 'I_Hash_size.+1)
             \sum_(h in [finType of HashState n])
             \sum_(hs in [finType of (k.+1).-tuple (HashState n)])
             \sum_(hs_fun' in [finType of HashState n])
             \sum_(hshs in 'I_Hash_size.+1)
             \sum_(hshs' in 'I_Hash_size.+1)
             ((((true == ~~ tnth
                            (bloomfilter_state
                               (bloomfilter_add_internal result (bloomfilter_set_bit result' bf))) ind) %R) *R*
               ([&& (h == hs_fun') & (hs == exp_hashes) ] %R)) *R*
              ((((hs_fun', result') == (hashstate_put n value hshs (thead hashes), hshs)) %R) *R*
               (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
          ).

        apply eq_bigr => result' _.

        rewrite (bigID (fun ind' => ind' == result')) big_pred1_eq.
        apply H.
    - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move => [] //=.
      apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => hs _; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => hshs _; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => hshs' _; first by dispatch_Rgt; move=> [] //=.

        by rewrite eq_refl Bool.andb_true_r Bool.andb_false_r //= mulR0 mul0R.

        apply eq_bigr => h _.
        apply eq_bigr => hs _.
        apply eq_bigr => hs_fun' _.
        apply eq_bigr => hshs' _.
        apply eq_bigr => hshs _.
          by rewrite !eq_refl !Bool.andb_true_r.

          transitivity (   
              \sum_(hshs' in 'I_Hash_size.+1)
               \sum_(result' in 'I_Hash_size.+1)
               \sum_(h in [finType of HashState n])
               \sum_(hs in [finType of (k.+1).-tuple (HashState n)])
               \sum_(hs_fun' in [finType of HashState n])
               \sum_(hshs in 'I_Hash_size.+1)

               ((((true == ~~ tnth
                              (bloomfilter_state
                                 (bloomfilter_add_internal result (bloomfilter_set_bit result' bf))) ind)
                    %R) *R* ((h == hs_fun') && (hs == exp_hashes) %R)) *R*
                ((((hs_fun' == hashstate_put n value hshs (thead hashes)) && (result' == hshs)) %R) *R*
                 (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
            ).
    - apply Logic.eq_sym.

      rewrite exchange_big; apply eq_bigr => result' _.
      rewrite exchange_big; apply eq_bigr => h _.
      rewrite exchange_big; apply eq_bigr => hs _.
      rewrite exchange_big; apply eq_bigr => hshs _.
      rewrite exchange_big; apply eq_bigr => hshs' _.
      apply eq_bigr => hshs'' _.
        by rewrite xpair_eqE.

        transitivity (          
            \sum_(hshs' in 'I_Hash_size.+1)
             \sum_(hshs in 'I_Hash_size.+1)
             \sum_(result' in 'I_Hash_size.+1)
             \sum_(h in [finType of HashState n])
             \sum_(hs in [finType of (k.+1).-tuple (HashState n)])
             \sum_(hs_fun' in [finType of HashState n])
             ((((true ==
                 ~~
                   tnth
                   (bloomfilter_state
                      (bloomfilter_add_internal result (bloomfilter_set_bit result' bf))) ind)
                  %R) *R* ((h == hs_fun') && (hs == exp_hashes) %R)) *R*
              (((hs_fun' == hashstate_put n value hshs (thead hashes)) && (result' == hshs) %R) *R*
               (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
          ).

    - apply eq_bigr => hshs' _; apply Logic.eq_sym.
      rewrite exchange_big; apply eq_bigr => result' _.
      rewrite exchange_big; apply eq_bigr => h _.
      rewrite exchange_big; apply eq_bigr => hs _.
        by rewrite exchange_big; apply eq_bigr => hs_fun' _.


        transitivity (
            \sum_(hshs' in 'I_Hash_size.+1)
             \sum_(h in [finType of HashState n])
             \sum_(hs in [finType of (k.+1).-tuple (HashState n)])
             \sum_(hs_fun' in [finType of HashState n])
             ((((true ==
                 ~~
                   tnth
                   (bloomfilter_state
                      (bloomfilter_add_internal result (bloomfilter_set_bit hshs' bf))) ind)
                  %R) *R* ((h == hs_fun') && (hs == exp_hashes) %R)) *R*
              (((hs_fun' == hashstate_put n value hshs' (thead hashes))  %R) *R*
               (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R))))
          ).
        apply eq_bigr => hshs' _.
        rewrite (bigID (fun hshs => hshs == hshs')) big_pred1_eq.
        apply H.

    - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => result' _; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => hs _; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.

        by rewrite //= !mulR0.

        rewrite (bigID (fun result' => result' == hshs')) big_pred1_eq.                                        apply H.
    - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => hs _; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.
        by rewrite !Bool.andb_false_r //= !mul0R mulR0.

        apply eq_bigr => h _.
        apply eq_bigr => hs _.
        apply eq_bigr => hs_fun' _.
        do ?(apply f_equal).
          by rewrite eq_refl //= Bool.andb_true_r mulR1.
          transitivity (                                                  
              \sum_(hshs' in 'I_Hash_size.+1)
               \sum_(hs_fun' in [finType of HashState n])                                
               \sum_(h in [finType of HashState n])
               
               ((((true ==
                   ~~
                     tnth
                     (bloomfilter_state
                        (bloomfilter_add_internal result (bloomfilter_set_bit hshs' bf))) ind) %R) *R*
                 ((h == hs_fun')%R)) *R*
                (((hs_fun' == hashstate_put n value hshs' (thead hashes)) %R) *R*
                 Rdefinitions.Rinv (#|'I_Hash_size.+1| %R)))
            ).

    - apply eq_bigr => hshs' _.
      apply Logic.eq_sym.
      rewrite exchange_big; apply eq_bigr => h _.
      apply Logic.eq_sym.
      rewrite (bigID (fun hs => hs == exp_hashes)) big_pred1_eq.
      apply H.
    - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.

        by rewrite Bool.andb_false_r //= mulR0 mul0R.

        apply eq_bigr => hs_fun' _.      
          by rewrite eq_refl Bool.andb_true_r.

          transitivity (
              \sum_(hshs' in 'I_Hash_size.+1)
               ((((true ==
                   ~~
                     tnth
                     (bloomfilter_state (bloomfilter_add_internal result (bloomfilter_set_bit hshs' bf)))
                     ind) %R)) *R*
                (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R)))
            ).

    - apply eq_bigr => hshs' _.

      rewrite  (bigID (fun hs_fun' => hs_fun' == hashstate_put n value hshs' (thead hashes))) big_pred1_eq.

      apply H.
    - move=>//=;apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
      apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
        by rewrite //= mul0R mulR0.
        rewrite (bigID (fun h => h == hashstate_put n value hshs' (thead hashes))) big_pred1_eq.                                                      

        apply H.
    - move=>//=;apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
        by rewrite //=  !mulR0 mul0R.

          by rewrite !eq_refl //= mulR1 mul1R.       


          case Hind: (ind \in result).              
    - rewrite !bloomfilter_add_internal_hit //= mulR0.
      apply prsumr_eq0P => hshs' _; first by dispatch_Rgt; move=> [] //=.
        by rewrite bloomfilter_add_internal_hit //= mul0R.

    - move/Bool.negb_true_iff: Hind => Hind.
      rewrite bloomfilter_add_internal_miss //= mulR1. 

      rewrite (bigID (fun hshs' => hshs' == ind)) big_pred1_eq //= addRC.
      apply H.
      rewrite bloomfilter_add_internal_preserve; first by rewrite mul0R.

      rewrite /bloomfilter_state/bloomfilter_set_bit.
        by rewrite FixedList.tnth_set_nth_eq.

        transitivity (
            \sum_(i < Hash_size.+1 | i != ind)
             (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R))
          ).
    - apply eq_bigr => i Hneq.
      rewrite bloomfilter_add_internal_miss; first by rewrite //= mul1R.

      rewrite /bloomfilter_state/bloomfilter_set_bit.
      rewrite FixedList.tnth_set_nth_neq //= 1?eq_sym //= 1?Hind.
        by [].
        apply prsumr_sans_one => //=.
          by rewrite card_ord.
          rewrite bigsum_card_constE card_ord RIneq.Rinv_r //=.
            by apply RIneq.not_0_INR => //=.


            (* DONE!!!! *)                                                         
  Qed.



  Definition bloomfilter_add_multiple  hsh_0 bf_0 values :=
    @foldr B (Comp [finType of k.-tuple (HashState n) * BloomFilter])
           (fun val hsh_bf =>
              res_1 <-$ hsh_bf;
                let (hsh, bf) := res_1 in
                bloomfilter_add val hsh bf) (ret (hsh_0, bf_0)) values.



  Lemma bloomfilter_add_multiple_unfold A hshs bf x xs (f: _ -> Comp A):
    d[ res <-$ bloomfilter_add_multiple hshs bf (x :: xs);
         f (res) ] =
    d[
        res1 <-$ bloomfilter_add_multiple hshs bf xs;
          let (hshs', bf') := res1 in  
          res2 <-$ bloomfilter_add x hshs' bf';
            f (res2)
      ].
  Proof.
    apply dist_ext => a //=.
    rewrite DistBindA //=.
      by rewrite !DistBind.dE; apply eq_bigr => [[hshs' bf']] _; apply f_equal => //=.
  Qed.
  

  Lemma bloomfilter_add_multiple_find_preserve value  inds hashes hashes' bf bf' xs:
    hash_vec_contains_value value hashes inds ->
    ((d[ bloomfilter_add_multiple hashes bf xs]) (hashes', bf') != (0 %R)) ->
    hash_vec_contains_value value hashes' inds.
  Proof.

    move=> Hcontains.
    elim: xs hashes inds  Hcontains hashes' bf' => [//=| x xs IHxs] hashes inds Hcontains hashes' bf'.

    - {
        rewrite Dist1.dE xpair_eqE.

        case Hhashes: ((hashes') == _) => /eqP //= /eqP.
        case Hbf: ((bf') == _) => /eqP //= /eqP _.
          by move/eqP: Hhashes -> .
      }
    - {
        rewrite //= DistBind.dE rsum_split //=.

        under big a _ under big b _ rewrite DistBind.dE rsum_Rmul_distr_l rsum_split //=.

        under big a _ under big b _ under big c _ under big d _ rewrite Dist1.dE mulRA mulRC eq_sym xpair_eqE boolR_distr -!mulRA.

        under big a _ under big b _ rewrite exchange_big; under big c _ rewrite -rsum_pred_demote big_pred1_eq.

        move: (IHxs);clear IHxs => IHxs.
        move=>/eqP /prsumr_ge0; case; first by (intros; dispatch_Rgt).
      move=> hashes_internal' /RIneq.Rgt_not_eq/prsumr_ge0; case; first by (intros;dispatch_Rgt).
      move=> bf_prev/RIneq.Rgt_not_eq/prsumr_ge0; case; first by (intros;dispatch_Rgt).
      move=> inds_prev.
      case Heq0: ((d[ bloomfilter_add_multiple hashes bf xs]) (hashes_internal', bf_prev) == (0%R)).
      - by move/eqP:Heq0 ->;rewrite !mul0R mulR0 //= RIneq.INR_IZR_INZ //==>/RIneq.Rgt_not_eq //=.
      - {

                                                                        move/Bool.negb_true_iff: Heq0 => //= /IHxs Heq0.          

                                                                        move: (Heq0 _ Hcontains); clear Heq0 => Hcontains_internal.

                                                                        move=>/RIneq.Rgt_not_eq; rewrite (RIneq.INR_IZR_INZ 0) //= =>/eqP.
          rewrite !mulR_neq0' =>/andP[Hadd /andP [Haddm Hint]].

                                                                                                                                          case Hneq: (value == x).

                                                                        - {
              move: Hcontains_internal Hint.
              move/eqP: Hneq <- =>Hcontains_internal.

                                                                           erewrite hash_vec_find_simpl =>//=; last by exact Hcontains_internal.

                                                                           move=>/eqP;
rewrite RIneq.INR_IZR_INZ; case Hand: (_ && _) => //= _.
                                                                           move/andP: Hand => [/eqP ->] //=.
                                                                          }

                                                                          move/Bool.negb_true_iff: Hneq => Hneq.
                                                                          move: Hneq Hcontains_internal Hint; clear.
                                                                          move: k inds hashes' hashes_internal' inds_prev;clear k; elim => [|k IHk].

                                                                        - {
                                                                            do 5!intro; rewrite !tuple0 //= Dist1.dE xpair_eqE => H3.  
                                                                            case Htrue: (_ && _); try rewrite RIneq.INR_IZR_INZ => /eqP //= _.
                                                                              by move/andP: Htrue => [/eqP -> /eqP _].              
                                                                          }
                                                                        - {

                                                                            move=> [[//=| ind inds] Hinds] [[//=| hash hashes] Hhashes] [[//=| hash' hashes'] Hhashes'].
                                                                            move=> [[//=|ind' inds'] Hinds'] Hneq.

                                                                            rewrite(tuple_eta (Tuple Hhashes'))(tuple_eta (Tuple Hinds))(tuple_eta (Tuple Hhashes))(tuple_eta (Tuple Hinds')) //=.

                                                                            rewrite !ntuple_tailE theadE//=.
                                                                            have->: ( thead (Tuple Hhashes)) = hash; first by [].
                                                                            have->: ( thead (Tuple Hhashes')) = hash'; first by [].
                                                                            have->: ( thead (Tuple Hinds)) = ind; first by [].
                                                                            have->: ( thead (Tuple Hinds')) = ind'; first by [].

                                                                            rewrite/hash_vec_contains_value //= => /andP[Hfind Hcontains].

                                                                            rewrite DistBind.dE rsum_split //=.
                                                                            move=> /eqP/prsumr_ge0; case; last move=> b'; first by (intros; dispatch_Rgt).
                                                                            move=> /RIneq.Rgt_not_eq/prsumr_ge0; case; last move=> b; first by (intros; dispatch_Rgt).
                                                                            move=>/RIneq.Rgt_not_eq/eqP.
                                                                            rewrite !mulR_neq0'=>/andP[Hint]/eqP;rewrite DistBind.dE.
                                                                            move=>/prsumr_ge0; case; last move=> [] //=; first by (intros; dispatch_Rgt).

                                                                            move=> hsh_val ind_val; rewrite Dist1.dE xpair_eqE.

                                                                            move=>/RIneq.Rgt_not_eq/eqP; rewrite !mulR_neq0'=>/andP[Hhash].

                                                                            rewrite RIneq.INR_IZR_INZ; case Hand: (_ && _) => //=/eqP //= _.

                                                                            move:Hint.
                                                                            move/andP: Hand =>[/eqP [ H1 H2 ] /eqP [ H3 H4 ]] Hint.
                                                                            have Hcont': hash_vec_contains_value value (behead_tuple (Tuple Hhashes')) (FixedList.ntuple_tail (Tuple Hinds)); first by rewrite/hash_vec_contains_value //=.

                                                                            move: (IHk (FixedList.ntuple_tail (Tuple Hinds)) b' (behead_tuple (Tuple Hhashes')) b Hneq Hcont' Hint); clear IHk; rewrite/hash_vec_contains_value //= -H2 => ->; rewrite Bool.andb_true_r.

                                                                            move:  Hneq Hfind Hhash.
                                                                            rewrite H1 /Hash.hash; clear.
                                                                            case: (hashstate_find n x hash') => //=.
                                                                            - {
                                                                                move=> ind_val' Hneq; rewrite Dist1.dE xpair_eqE=> Hfind'/eqP.
                                                                                case Hand: (_ && _) => //= _.
                                                                                  by move/andP: Hand => [/eqP ->] //=.
                                                                              }
                                                                            - {
                                                                                move=> Hneq Hfind //=; rewrite DistBind.dE=>/eqP.

                                                                                under big a _ rewrite DistBind.dE Dist1.dE xpair_eqE rsum_Rmul_distr_r.

                                                                                under big a _ under big a0 _ rewrite mulRC -mulRA mulRC -mulRA Dist1.dE eq_sym.

                                                                                under big a _ rewrite -rsum_pred_demote big_pred1_eq andbC boolR_distr -!mulRA eq_sym.
                                                                                rewrite -rsum_pred_demote big_pred1_eq //==>/eqP.

                                                                                rewrite mulR_neq0' =>/andP[/eqP ]; case Heq: (_ == _) => //= _ _.
                                                                                move/eqP: Heq ->; move: Hneq Hfind; clear.
                                                                                move=> Hvalue.
                                                                                move: n hash';clear n; elim => [//=|n IHn] [[//=| hash hashes] Hhashes].
                                                                                rewrite (tuple_eta (Tuple Hhashes)) //=.

                                                                                rewrite /FixedList.ntuple_head !theadE  !ntuple_tailE.

                                                                                have->: (thead (Tuple Hhashes)) = hash; first by [].

                                                                                case: hash Hhashes => [[k' v']|] Hhashes //=.

                                                                                case Heq: (k' == value)=>//=.

                                                                                - {
                                                                                    move/eqP: Heq ->.
                                                                                    move/Bool.negb_true_iff: Hvalue -> => //=.
                                                                                      by rewrite ntuple_head_consE eq_refl.                      
                                                                                  }

                                                                                - {

                                                                                    move=> Hin; move: (Hin).
                                                                                    move=>/IHn Heq'.
                                                                                    case Hkeq: (k' == x) => //=.
                                                                                    - {
                                                                                        move/eqP:Hkeq <-; rewrite Heq //=; move: Hin.
                                                                                        rewrite/FixedList.ntuple_tail/behead_tuple.
                                                                                        move: (behead_tupleP _) => //= H1.
                                                                                        move: (behead_tupleP _) => //= H2.
                                                                                          by rewrite (proof_irrelevance _ H2 H1) //=.                          
                                                                                      }
                                                                                    - {
                                                                                          by rewrite ntuple_head_consE Heq ntuple_tail_consE.
                                                                                      }
                                                                                  }

                                                                                - {

                                                                                    rewrite eq_sym in Hvalue; move/Bool.negb_true_iff: (Hvalue) -> => //=.
                                                                                    rewrite/FixedList.ntuple_tail/behead_tuple.
                                                                                    move: (behead_tupleP _) => //= H1.
                                                                                    move: (behead_tupleP _) => //= H2.
                                                                                      by rewrite (proof_irrelevance _ H2 H1) //=.                          
                                                                                  }
                                                                              }

                                                                          }
                                                                      }
      }
      
  Qed.            


  



  Lemma bloomfilter_add_multiple_preserve x xs l m hshs hshs' bf bf'
        (Huniq: uniq (x :: xs))
        (Hlen: length xs == l) 
        (Hfree: hashes_have_free_spaces hshs  ((l+m).+1))
        (Huns:      all (bloomfilter_value_unseen hshs) (x :: xs)):
    ((d[ bloomfilter_add_multiple hshs bf xs]) (hshs', bf') != (0 %R)) ->
    (hashes_have_free_spaces hshs' (m.+1)) && (bloomfilter_value_unseen hshs' x).
  Proof.

    (* First clean up the proof *)
    move=> //=.
    rewrite -all_predI /predI //=.

    move: m hshs Hfree Huns bf bf' hshs'; rewrite/hash_vec.
    move/eqP: Hlen <-; clear l.
    have all_cons P y ys : all P (y :: ys) =  P y && all P ys. by [].
    move=> m hshs Hfree; rewrite all_cons => /andP []; move: x m hshs Huniq Hfree; clear all_cons.
    rewrite/hashes_have_free_spaces/hash_has_free_spaces/bloomfilter_value_unseen/hash_unseen.

    (* proof has been cleaned up *)

    elim: xs => [//= | y ys IHy] x m hshs Huniq /allP Hfree /allP Huns Hx  bf bf' hshs'.
    - rewrite Dist1.dE=>/eqP;case Heq: (_ == _)=>//=;move:Heq;rewrite xpair_eqE=>/andP[/eqP->_] _.
      apply /allP=> hsh Hin //=; apply/andP; split.
        by apply Hfree.
          by apply Huns.
    - move: Hx; have all_cons P z zs : all P (z :: zs) =  P z && all P zs. by [].
      rewrite all_cons => /andP [/allP Hfindy /allP Hfindys].

      have H1: uniq (x :: ys).
        by move: Huniq => //=/andP [Hcons /andP [_ ->]]; move: Hcons; rewrite !in_cons Bool.negb_orb=>/andP[_ ->].
        have H2: all (fun hsh : HashState n => FixedList.fixlist_length hsh + (length ys + m.+1).+1 <= n) hshs.
          by apply/allP => vec Hvec; move: (Hfree vec Hvec) => //=; rewrite addSn !addnS.
          have H3: all (fun hsh : HashState n => FixedMap.fixmap_find x hsh == None) hshs.
            by apply /allP.
            have H4: all (fun b : B => all (fun hsh : HashState n => FixedMap.fixmap_find b hsh == None) hshs) ys.    
              by apply/allP.
              move: (IHy x m.+1 hshs H1 H2 H3 H4); clear IHy H1 H2 H3 H4 => IHy.
              move=>/eqP//=; rewrite DistBind.dE prsumr_ge0 => [[[hs1 bf1]]|]; last by move=>a;dispatch_Rgt.
              move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[/eqP/(IHy bf bf1 hs1) ].
              clear IHy all_cons bf Hfree Huns Hkgt0 Hfindys .
              move=>H1 H2; move: H2 H1; rewrite //=DistBind.dE.
              rewrite prsumr_ge0 => [[[hs2 vec1]]|]; last by move=>a;dispatch_Rgt.
              move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ] //=; rewrite Dist1.dE.
              case Heq: (_ == _)=>//=; move: Heq;rewrite xpair_eqE=>/andP[/eqP -> _] Hint _.
              clear hshs'; elim: k hs1 hs2 vec1 Hint; clear hshs Hfindy k.
    - by move=> hs1 hs2 vec1 //=; rewrite Dist1.dE;case Heq:(_==_)=>//=;move:Heq;rewrite xpair_eqE=>/andP[/eqP ->] //=.          
    - move=> k IHk hs1 hs2 vec1 //=.  
      rewrite DistBind.dE prsumr_ge0=>[[[hs3 vec2]]|]; last by move=>a; dispatch_Rgt.
      move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ].
      rewrite (tuple_eta hs1) ntuple_tailE //=.
      move=>/ (IHk _ _ _); clear IHk => IHk.

      rewrite DistBind.dE prsumr_ge0 => [[[state1 ind1]]|]; last by move=>a;dispatch_Rgt.
      move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ]//=.
      rewrite theadE Dist1.dE => Hhash;case Heq:(_==_)=>//=;move:Heq;rewrite xpair_eqE.
      move=>/andP [/eqP -> /eqP _] _.
      move=>/andP [/andP [Hlen Hfree]] =>/IHk //= ->; rewrite Bool.andb_true_r.
      move: Hhash; rewrite/hash/hashstate_find.

      case: (FixedMap.fixmap_find _ _) => [val //=|]. 

    - rewrite Dist1.dE //=; case Heq:(_==_)=>//=;move:Heq;rewrite xpair_eqE.
      move=>/andP [/eqP -> _] _; apply/andP; split => //=.
        by move:Hlen; rewrite addnS =>/ltnW.
    - move=> //=;rewrite DistBind.dE prsumr_ge0 => [[ind2]|];last by move=>a;dispatch_Rgt.
      move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ]//=.
      rewrite DistBind.dE prsumr_ge0 => [[ind3]|];last by move=>a;dispatch_Rgt.
      move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ]//= _.
      rewrite !Dist1.dE;case Heq:(_==_)=>//=;move/eqP:Heq => -> _; clear ind2.
      case Heq: (_ == _)=>//=;move:Heq;rewrite xpair_eqE=>/andP[/eqP -> /eqP <-] _;clear ind3.
      apply/andP;split;last first.
    - rewrite /hashstate_put.
      move: Huniq => //=/andP[];rewrite in_cons Bool.negb_orb=>/andP[Hneq _ _].
        by rewrite fixmap_find_neq //=.
    - move: Hlen.
      clear.
      rewrite !addnS -addSn addnC -ltn_subRL => Hlen.
      rewrite addnC -ltn_subRL.
      apply (@leq_ltn_trans  (FixedList.fixlist_length (thead hs1)).+1) => //=.
      clear Hlen; move: (thead _) => [ls Hls]; clear hs1.
      elim: n ls Hls => [//=|]; clear n => n IHn [//=|l ls] Hls //=.
      have->: (FixedList.ntuple_head (Tuple Hls)) = l; first by [].
      case: l Hls => [[k' v']|] Hls; last first; last case Heq: (_ == _).
    - by move: Hls (eq_ind _ _ _ _ _) => //=.
    - by move: Hls (eq_ind _ _ _ _ _) => //= Hls Hls'.
      rewrite /FixedList.ntuple_tail; move: (behead_tupleP _) => //= Hls'.
      move: (IHn ls Hls') => IHn'.
      rewrite/FixedList.fixlist_length/FixedList.ntuple_cons.
        by case Hput: (hashstate_put _) => [ms Hms] //=; move: IHn';rewrite Hput.
  Qed.
  

  



  Lemma bloomfilter_addn_Nuns  ind bf (hashes: hash_vec) x :
    bloomfilter_get_bit ind bf ->
    (d[ res <-$ bloomfilter_add x hashes bf;
          (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true = (0 %R).
  Proof.

    move=> Htnth //=.

    rewrite DistBind.dE; apply prsumr_eq0P => a _ ; first by dispatch_Rgt.
    move: a => [hashes' bf'].
    rewrite DistBind.dE rsum_Rmul_distr_r; apply prsumr_eq0P => a _; first by dispatch_Rgt.
    move: a => [hashes'' hvec] //=.

    rewrite !Dist1.dE xpair_eqE.

    case Hgth: (_ == _) => //=; rewrite ?mul1R; last by rewrite !mul0R.
    case Hhashes: (_ == _) => //=; rewrite ?Bool.andb_true_l; last by rewrite !mulR0.
    case Hbf: (_ == _) => //=; rewrite ?mulR1; last by rewrite mulR0.

    move/eqP: Hgth.
    move/eqP: Hbf ->.
    rewrite/bloomfilter_get_bit.
      by rewrite bloomfilter_add_internal_preserve //=.

  Qed.
  

  
  Lemma bloomfilter_addn_insert_multiple hashes l (ind: 'I_Hash_size.+1) (bf: BloomFilter) (values: seq B):
    length values == l ->
    hashes_have_free_spaces hashes l ->
    all (bloomfilter_value_unseen hashes) values ->
    uniq values ->
    ~~ bloomfilter_get_bit ind bf ->
    (d[ res <-$ bloomfilter_add_multiple hashes bf values;
          (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true =
    ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k * l)).

    elim: l ind bf values hashes => [|l IHl] ind bf values hashes0 .
    - case: values => //= _ _ _ _ Htnth; rewrite muln0 //= DistBind.dE rsum_split //=.

      transitivity (
          \sum_(a in [finType of k.-tuple (HashState n)])
           \sum_(b in [finType of BloomFilter])
           (((a == hashes0) &&  (b == bf) %R) *R* (Dist1.d (~~ bloomfilter_get_bit ind b)) true)
        ).
        by apply eq_bigr => a _; apply eq_bigr => b _; rewrite !Dist1.dE //= xpair_eqE.

        transitivity ((true == (~~ bloomfilter_get_bit ind bf) %R)).   
        rewrite (bigID (fun a => a == hashes0)) //= big_pred1_eq.
        have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.

        apply H.
    - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by dispatch_Rgt.
      apply prsumr_eq0P => b _; first by dispatch_Rgt.
        by rewrite mul0R.

        rewrite (bigID (fun b => b == bf)) //= big_pred1_eq.

        apply H.
    - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by dispatch_Rgt.
        by rewrite Bool.andb_false_r //= mul0R.
          by rewrite !eq_refl //= mul1R Dist1.dE.
            by rewrite Htnth.
    - rewrite mulnS.

      case: values => [//= | x xs] Hlen Hfree Huns Huniq Hnb.
      rewrite bloomfilter_add_multiple_unfold.
      rewrite RealField.Rdef_pow_add.
      erewrite <- (IHl ind bf xs hashes0) => //=.
      rewrite mulRC //= !DistBind.dE rsum_Rmul_distr_r; apply eq_bigr => [[hshs' bf']] _.
      case Hnz: (d[ bloomfilter_add_multiple hashes0 bf xs ] (hshs', bf') == (0 %R));
        first by move/eqP: Hnz ->; rewrite !mul0R mulR0.
      move/Bool.negb_true_iff: Hnz => Hnz.

      move: Hfree; rewrite -(addn0 l) => Hfree.
      move: (bloomfilter_add_multiple_preserve Huniq Hlen Hfree Huns Hnz) => /andP [].
      rewrite /hashes_have_free_spaces/bloomfilter_value_unseen => Hfree' Huns'.
      apply Logic.eq_sym; rewrite mulRA mulRC mulRA mulRC; apply f_equal; apply Logic.eq_sym.
      case Htnth': (~~ bloomfilter_get_bit ind bf').
    - have <-: (Rdefinitions.IZR 1) = (BinNums.Zpos BinNums.xH); first by [].
      erewrite <-  (@bloomfilter_addn hshs' ind bf' x) => //=.
    - by rewrite Dist1.dE //= mul1R !DistBind.dE //=; apply eq_bigr => [[hshs'' bf'']] _.


    - move: Hfree'; rewrite /hashes_not_full/hash_has_free_spaces => /allP Hlt; apply/allP => cell Hcell; rewrite /hash_not_full.
        by move: (Hlt cell Hcell); rewrite addn1 //=.
    - move /Bool.negb_false_iff: Htnth' => Htnth'; rewrite Dist1.dE // mul0R.
        by rewrite bloomfilter_addn_Nuns //=.


        move/allP: Hfree => Hfree; apply/allP => cell Hcell.        
        move: (Hfree cell Hcell); rewrite /hash_has_free_spaces.
          by rewrite addnS => /ltnW.

          move /allP: Huns => Huns; apply/allP => x' Hx'.
          apply Huns => //=.
            by rewrite in_cons Hx' Bool.orb_true_r.
              by move: Huniq => //= /andP [].
  Qed.
  
  (* TODO: No False Negatives *)

  Lemma bloomfilter_add_internal_indep l bf' x xs :
    tnth (bloomfilter_state bf') x ->
    uniq (x :: xs) ->
    length (x::xs) < Hash_size.+1 ->

    \sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
     (((tnth (bloomfilter_state (bloomfilter_add_internal inds bf')) x &&
             all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs) %R) *R*
      (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) =
    ((\sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
       (((tnth (bloomfilter_state (bloomfilter_add_internal inds bf')) x) %R) *R*
        (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) *R*
     (\sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
       ((( all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs) %R) *R*
        (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))).
  Proof.
    have H x1 y1 z1: y1 = (0 %R) -> x1 = z1 -> x1 +R+ y1 = z1. by move=> -> ->; rewrite addR0.
    elim: l bf' x xs=> [//=|l IHl] bf' x xs.
    -  move=> Htnth /andP[Hnin Huniq] Hlen; rewrite unlock=>//=.
       have: (index_enum [finType of 0.-tuple 'I_Hash_size.+1]) = [tuple]::[::].
       rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
       rewrite -enumT //=; rewrite/(enum _)//=.
       rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
       move: (FinTuple.size_enum 0 (ordinal_finType Hash_size.+1))=> //=; rewrite expn0.
       move: (FinTuple.enum _ _)=>[|[[|//=] Hz] []]//= _.
         by move: (@tuple0  'I_Hash_size.+1 (Tuple Hz)) <- =>//=.
         move=> -> //=.
         rewrite !addR0.
           by case: (tnth _ _) => //=;rewrite?mul1R?mul0R//=;case: (all _ _)=>//=;rewrite?mul1R.

    - move=> Htnth Huniq Hlength.
      rewrite rsum_tuple_split rsum_split=>//=.

      transitivity (
          \sum_(a in 'I_Hash_size.+1)
           (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
            \sum_(b in [finType of l.-tuple 'I_Hash_size.+1])
             ((tnth (bloomfilter_state
                       (bloomfilter_add_internal b (bloomfilter_set_bit a bf'))) x &&
                    all [eta tnth (bloomfilter_state
                                     (bloomfilter_add_internal b (bloomfilter_set_bit a bf')))]
                    xs %R) *R*
              ( (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
        ).
      apply eq_bigr => a _; rewrite rsum_Rmul_distr_l; apply eq_bigr => b _.
      rewrite mulRA mulRC mulRA mulRC; apply f_equal.
        by rewrite mulRC; apply f_equal.

        transitivity (
            \sum_(a in 'I_Hash_size.+1)
             (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
              (\sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                ((tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf'))) x %R) *R*
                 (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
               \sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                      xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))
             )
          ).
        apply eq_bigr=> a _; apply f_equal.
        rewrite IHl; last first; try by [].


        case Haeq: (x == a); first by
            rewrite /bloomfilter_set_bit/bloomfilter_state FixedList.tnth_set_nth_eq //=.
          by rewrite FixedList.tnth_set_nth_neq //=;  move/Bool.negb_true_iff: Haeq.

          have: (\sum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                  ((tnth (bloomfilter_state
                            (bloomfilter_add_internal inds bf')) x %R) *R*
                   (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                    (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) =
                 \sum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                  (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                   (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))
                ).
          apply eq_bigr=> inds _.
          rewrite -{2}(mulR1 (Rdefinitions.Rinv _ *R* _)).
          rewrite mulRC; apply f_equal.
            by rewrite bloomfilter_add_internal_preserve //=.
            move=> ->; rewrite bigsum_card_constE.
            
            transitivity (
                Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                \sum_(a in 'I_Hash_size.+1)
                 ((\sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                    ((tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf'))) x %R) *R*
                     (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
                   \sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                    ((all
                        [eta tnth
                             (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                        xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
              ).
            rewrite rsum_Rmul_distr_l.
              by apply eq_bigr=> a _.

              transitivity (
                  Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                  \sum_(a in 'I_Hash_size.+1)
                   ((\sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                      ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))   *R*
                     \sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                      ((all
                          [eta tnth
                               (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                          xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
                ).
              apply f_equal; apply eq_bigr=> a _.
              rewrite mulRC; apply Logic.eq_sym; rewrite mulRC; apply f_equal; apply Logic.eq_sym.
              apply eq_bigr=> inds _.
              rewrite bloomfilter_add_internal_preserve.
                by rewrite mul1R.

                rewrite/bloomfilter_state/bloomfilter_set_bit.
                case Haeq:(x == a); first by rewrite FixedList.tnth_set_nth_eq //=.
                  by move/Bool.negb_true_iff: Haeq=>Haeq; rewrite FixedList.tnth_set_nth_neq//=.


                  transitivity (
                      Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                      \sum_(a in 'I_Hash_size.+1)
                       ((((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                          ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))   *R*
                         \sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                          ((all
                              [eta tnth
                                   (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                              xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
                    ).
                  apply f_equal; apply eq_bigr => a _.
                    by rewrite bigsum_card_constE //=.
                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        ((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                         ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))   *R*
                        \sum_(a in 'I_Hash_size.+1)
                         ((\sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
                      ).
                    rewrite !rsum_Rmul_distr_l; apply eq_bigr=> a _.
                      by rewrite mulRA; apply f_equal.

                      transitivity (
                          Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                          (((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                            ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))   *R*
                           \sum_(a in 'I_Hash_size.+1)
                            ((\sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                               ((all
                                   [eta tnth
                                        (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                   xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))) 
                        )).
                        by rewrite -mulRA.
                        apply Logic.eq_sym.  

                        transitivity (
                            Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                            (((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R) *R*
                              (
                                (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) *R*
                             \sum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                              ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs %R) *R*
                               (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                                (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
                          ).
                        rewrite -mulRA mulRC -mulRA -mulRA; apply f_equal. 
                        rewrite !rsum_Rmul_distr_l !rsum_Rmul_distr_r mulRC !rsum_Rmul_distr_r.
                        apply eq_bigr=> a _.
                        rewrite mulRC -mulRA -mulRA -mulRA -mulRA; apply f_equal.
                        rewrite mulRC -mulRA mulRC -mulRA  -mulRA; apply f_equal.
                          by rewrite mulRC -mulRA; apply f_equal.
                          apply f_equal.                 
                          transitivity (
                              ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
                              (((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R)) *R*
                               \sum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                                ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs %R) *R*
                                 (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                                  (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
                            ).
                            by rewrite -mulRA mulRC -mulRA; apply f_equal; rewrite mulRC.
                            apply Logic.eq_sym.    

                            transitivity (
                                ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
                                (((#|[finType of l.-tuple 'I_Hash_size.+1]| %R)) *R*
                                 \sum_(a in 'I_Hash_size.+1)
                                  ((\sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                                     ((all
                                         [eta tnth
                                              (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                         xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))) 
                              )).
                              by rewrite -mulRA mulRC -mulRA; apply f_equal; rewrite mulRC.
                              apply f_equal; apply Logic.eq_sym.    
                              transitivity (
                                  Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                                  (((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R)) *R*
                                   \sum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                                    ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs %R) *R*
                                     ( (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
                                ).
                              apply Logic.eq_sym; rewrite mulRA mulRC mulRA mulRC; apply f_equal.
                              rewrite rsum_Rmul_distr_r; apply eq_bigr=> inds _.
                                by rewrite mulRC -mulRA; apply f_equal; rewrite mulRC.
                                rewrite rsum_tuple_split rsum_split !rsum_Rmul_distr_l; apply eq_bigr=> a _.
                                rewrite !rsum_Rmul_distr_l; apply eq_bigr=> inds _ //=.
                                transitivity ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))] xs %R) *R*
                                              (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                                               ((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R) *R*
                                                ( (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))).
                                rewrite mulRC -mulRA mulRC -mulRA -mulRA; apply f_equal.
                                  by rewrite mulRC -mulRA; apply f_equal; rewrite mulRC.
                                  apply Logic.eq_sym.    

                                  transitivity (
                                      (all [eta tnth (bloomfilter_state
                                                        (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))] xs
                                           %R) *R* 
                                      ((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                                       ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))                 
                                    ).
                                    by rewrite mulRC -mulRA; apply f_equal; rewrite mulRC //=.
                                    apply f_equal.
                                    rewrite !card_tuple //=.
                                    rewrite expnSr card_ord natRM; apply Logic.eq_sym.

                                    transitivity (
                                        ((Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Hash_size.+1 %R)) *R*
                                         (((Hash_size.+1 ^ l %R)) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))                           ).
                                      by rewrite -mulRA -mulRA; apply f_equal; rewrite mulRC -mulRA;
                                        apply f_equal; rewrite mulRC.
                                      rewrite Raxioms.Rinv_l; first by rewrite mul1R.
                                        by apply RIneq.not_0_INR =>//=.
  Qed.
  
  Lemma bloomfilter_add_insert_contains l (bf: BloomFilter) (inds: l.-tuple 'I_Hash_size.+1 ) (ps: seq 'I_Hash_size.+1) : all (fun p => p \in inds) ps -> all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf)) ps.
  Proof.                  
    move=>/allP HinP; apply/allP => [p Hp].
      by rewrite /bloomfilter_get_bit/bloomfilter_state bloomfilter_add_internal_hit //=; move: (HinP p Hp).
  Qed.


  Lemma bloomfilter_addn_insert_multiple_inv hashes l (ind: 'I_Hash_size.+1) (bf: BloomFilter) (values: seq B):
    length values == l ->
    hashes_have_free_spaces hashes l ->
    all (bloomfilter_value_unseen hashes) values ->
    uniq values ->
    ~~ bloomfilter_get_bit ind bf ->
    (d[ res <-$ bloomfilter_add_multiple hashes bf values;
          (let '(_, bf') := res in ret bloomfilter_get_bit ind bf')]) true =
    (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k * l))).
  Proof.

    move=> Hlen Hhashes Huns Huniq Hnth.

    transitivity (
        (d[ res <-$ bloomfilter_add_multiple hashes bf values;
            ret (fun res' => (let '(_, bf') := res' in bloomfilter_get_bit ind bf')) res]) true
      ).
    - by rewrite //= !DistBind.dE; apply/eq_bigr=>[[hs' bf']] _ //=.
      rewrite -(prsumr_neg1 ).

      transitivity (
          (1 -R- (d[ res <-$ bloomfilter_add_multiple hashes bf values;
                     (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true)
        ).
    - by rewrite //= !DistBind.dE; apply f_equal; apply/eq_bigr=>[[hs' bf']] _ //=.
        by rewrite (@bloomfilter_addn_insert_multiple _ l).       
  Qed.





  Theorem bloomfilter_addn_bits
          hashes b (inds: seq 'I_Hash_size.+1) (bf: BloomFilter) (value: B):
    b < k ->
    length inds == b ->
    hashes_have_free_spaces hashes 1 ->
    (bloomfilter_value_unseen hashes value)  ->
    uniq inds ->
    all (fun ind => ~~ bloomfilter_get_bit ind bf) inds ->
    (d[ res <-$ bloomfilter_add value hashes bf;
          (let '(_, bf') := res in ret (all (bloomfilter_get_bit^~ bf') inds))]) true = 
    \sum_(i in tuple_finType k (ordinal_finType Hash_size.+1))
     ((((inds \subseteq i) == true) %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k)).    Proof.
                                                                                       have H x1 y1 z1: y1 = (0 %R) -> x1 = z1 -> x1 +R+ y1 = z1; first by move=> -> ->; rewrite addR0.
                                                                                       rewrite //= DistBind.dE => Hb Hlen Hfree Huns Huniq Hall.
                                                                                       under big a _ rewrite DistBind.dE //= !rsum_Rmul_distr_r //=.
                                                                                       under big a _ rewrite  !rsum_Rmul_distr_r //=.
                                                                                       rewrite rsum_split //=.
                                                                                       under big a _ under big b0 _  rewrite Dist1.dE eq_sym.
                                                                                       under big a _  rewrite exchange_big.
                                                                                       rewrite exchange_big rsum_split//=.
                                                                                       under big a _ under big b0 _ under big i _ under big i0 _ rewrite Dist1.dE xpair_eqE.
                                                                                       under big a _ under big b0 _ rewrite (bigID (fun i => i == a)) big_pred1_eq //=.
                                                                                       under big a _ rewrite addRA_rsum.
                                                                                       rewrite addRA_rsum.
                                                                                       erewrite H; last by []; last first.
                                                                                       {
                                                                                         do 2!(apply prsumr_eq0P; intros; first by intros; dispatch_Rgt).
                                                                                         apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by intros; dispatch_Rgt.
                                                                                         apply prsumr_eq0P; intros; first by intros; dispatch_Rgt.
                                                                                           by rewrite //= !mulR0.
                                                                                       }

                                                                                       under big i _ under big i0 _ rewrite (bigID (fun j => j == (bloomfilter_add_internal i0 bf))) big_pred1_eq //=.
                                                                                       under big i _ rewrite addRA_rsum //=.
                                                                                       rewrite addRA_rsum.
                                                                                       erewrite H; last by []; last first.
                                                                                       {
                                                                                         do 2!(apply prsumr_eq0P; intros; first by intros; dispatch_Rgt).
                                                                                         apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by intros; dispatch_Rgt.
                                                                                           by rewrite Bool.andb_false_r //= !mulR0.
                                                                                       }
                                                                                       under big i _ under big i0 _ rewrite !eq_refl //= mulR1.
                                                                                       under big i _ under big i0 _ rewrite mulR1.
                                                                                       rewrite exchange_big //=.

                                                                                       under big i0 _ rewrite (bigID (fun i => i == Tuple (hash_vec_insert_length value hashes i0))) big_pred1_eq //=.
                                                                                       rewrite addRA_rsum.
                                                                                       erewrite H; last by []; last first.
                                                                                       {
                                                                                         do 1!(apply prsumr_eq0P; intros; first by intros; dispatch_Rgt).
                                                                                         apply prsumr_eq0P => i Hneq; first by intros; dispatch_Rgt.
                                                                                           by rewrite neg_hash_vecP //=; first rewrite !mulR0.
                                                                                       }
                                                                                       under big i _ rewrite hash_vecP //=.

                                                                                       have Hpred_eq i: (all (bloomfilter_get_bit^~ (bloomfilter_add_internal i bf)) inds = all (fun ind => ind \in i) inds).
                                                                                       {
                                                                                         apply eq_in_all => ind Hinds.
                                                                                         case HinI: (ind \in i); first by rewrite /bloomfilter_get_bit bloomfilter_add_internal_hit //=.

                                                                                         apply/Bool.negb_true_iff; rewrite /bloomfilter_get_bit bloomfilter_add_internal_miss //=;
                                                                                                                           first by move/allP: Hall => /(_ ind Hinds) .
                                                                                           by rewrite HinI.
                                                                                       }


                                                                                       under big i _ rewrite Hpred_eq //=.

                                                                                         by [].
                                                                                     Qed.



  Definition bloomfilter_new : BloomFilter.
    apply mkBloomFilter.
    apply Tuple with (nseq Hash_size.+1 false).
      by rewrite size_nseq.
  Defined.

  Lemma bloomfilter_new_empty_bits b : ~~ bloomfilter_get_bit b bloomfilter_new .
  Proof.
    clear k n Hkgt0.
    rewrite/bloomfilter_get_bit/bloomfilter_new //=.
    elim: Hash_size b => [[[|//=] Hm]|//= n IHn] //=.
    move=> [[| b] Hb]; rewrite /tnth //=.
    move: (Hb); move/ltn_SnnP: Hb => Hb' Hb;move: (IHn (Ordinal Hb'));rewrite /tnth //=.
    clear.

    move: (size_nseq n.+1 _)  => Hprf.
    move:(tnth_default _ _) (tnth_default _ _); clear Hb => b1 b2.

    have ->: (false :: nseq n false) = (nseq n.+1 false); first by [].
    move: Hb'; rewrite -Hprf; clear Hprf.
    move: (n.+1); clear n; elim: b => [//= n'|]; first by case: (nseq n' _).
    move=>  b IHb.
    case => [//=| n].
      by move=>//=/ltn_SnnP/(IHb n) IHb' H; apply IHb'.
  Qed.

  Lemma bloomfilter_new_empty bs : length bs > 0 -> ~~ bloomfilter_query_internal bs bloomfilter_new .
  Proof.
    clear k n Hkgt0.
    case: bs => [//=| b1 [//=| b2 bs]] Hlen; first by rewrite Bool.andb_true_r; apply bloomfilter_new_empty_bits.
    rewrite Bool.negb_andb; apply/orP; left; apply bloomfilter_new_empty_bits.
  Qed.


  Lemma bloomfilter_add_multiple_unwrap_internal bf
        hashes l value (values: seq B) inds:
    length values == l ->
    hashes_have_free_spaces hashes (l.+1) ->
    all (bloomfilter_value_unseen hashes) (value::values) ->
    \sum_(a in [finType of k.-tuple (HashState n) * BloomFilter])
     ((d[ bloomfilter_add_multiple (Tuple (hash_vec_insert_length value hashes inds)) bf
                                   values]) a *R*
      (d[ let (hashes2, bf) := a in res' <-$ bloomfilter_query value hashes2 bf; ret res'.2]) true) =
    \sum_(a in [finType of k.-tuple (HashState n) * BloomFilter])
     ((d[ bloomfilter_add_multiple (Tuple (hash_vec_insert_length value hashes inds)) bf
                                   values]) a *R*
      (bloomfilter_query_internal inds a.2 == true %R)).
  Proof.
    move: hashes; rewrite/hash_vec => hashes.
    move=>  Hlen Hfree Hall; apply eq_bigr => [[hshs' bf']] _.
    case Hzro: ((d[ bloomfilter_add_multiple (Tuple (hash_vec_insert_length value hashes inds)) bf values])
                  (hshs', bf') == 0); first by move/eqP:Hzro -> ; rewrite !mul0R.
    move/Bool.negb_true_iff: Hzro => Hzro.
    apply f_equal.
    rewrite //= /bloomfilter_query_internal //=.
    rewrite DistBind.dE rsum_split //=.
    under big a _ under big b _ rewrite mulRC Dist1.dE eq_sym.
    under big a _ rewrite -rsum_pred_demote big_pred1_eq DistBind.dE rsum_split //=.
    under big a _ under big a0 _ under big b _ rewrite mulRC Dist1.dE xpair_eqE boolR_distr -mulRA.
    rewrite exchange_big //=; under big a0 _ rewrite exchange_big; under big b _ rewrite -rsum_pred_demote big_pred1_eq //=.
    move=>//=.
    rewrite eqb_id; under big a0 _ under big b _ rewrite eq_sym !eqb_id.
    have Hallleq: all
                    (fun hsh : FixedList.fixlist [eqType of hash_keytype * hash_valuetype] n =>
                       FixedList.fixlist_length hsh + 1 <= n) hashes.
    {
      move: Hfree;rewrite/hashes_have_free_spaces/hash_has_free_spaces=>/allP Hfree;apply/allP=>ind Hind.
        by move: (Hfree ind Hind); rewrite addn1 addnS =>/ltn_weaken.    
    }

    move: (@hash_vec_contains_value_base _ _ value hashes inds Hallleq) => Hcontains'.
    move: (@bloomfilter_add_multiple_find_preserve value inds (Tuple (hash_vec_insert_length value hashes inds)) hshs' bf bf' values Hcontains' Hzro) => Hcontains''.
    under big a0 _ under big b _ rewrite (@hash_vec_find_simpl n k value hshs' _ inds _ Hcontains'') //=.

    under big a0 _ under big b _ rewrite mulRC andbC boolR_distr -!mulRA.
    under big a0 _ rewrite -rsum_pred_demote big_pred1_eq.
      by rewrite -rsum_pred_demote big_pred1_eq.
  Qed.



  Lemma bloomfilter_set_bit_conv bf b b':
    (bloomfilter_set_bit b (bloomfilter_set_bit b' bf)) =
    (bloomfilter_set_bit b' (bloomfilter_set_bit b bf)).
  Proof.

    rewrite/bloomfilter_set_bit/bloomfilter_state; apply f_equal.
    case: bf; rewrite/BitVector=>bf .
      by rewrite  fixedlist_set_nthC.
  Qed.

  Lemma bloomfilter_add_multiple_cat bf b others:
    (bloomfilter_add_internal others (bloomfilter_add_internal b bf)) =
    (bloomfilter_add_internal (others ++ b) bf).
  Proof.

    elim: others bf => [//=|other others Hothers] bf //= .
    rewrite -Hothers; apply f_equal; clear Hothers others.
    elim: b bf => [//=| b bs Hbs] bf //=.
    rewrite  bloomfilter_set_bit_conv.
      by rewrite Hbs.
  Qed.

  

  Lemma bloomfilter_add_multiple_unwrap_base 
        hashes l (values: seq B) others inds:
    uniq values ->
    length values == l ->
    hashes_have_free_spaces (hashes: k.-tuple (HashState n)) (l) ->
    all (bloomfilter_value_unseen hashes) (values) ->
    \sum_(a in [finType of (k.-tuple (HashState n) * BloomFilter)]%type)
     ((d[ bloomfilter_add_multiple hashes bloomfilter_new values]) a *R*
      ((all (bloomfilter_get_bit^~ (bloomfilter_add_internal others a.2)) inds == true) %R)) =
    \sum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
     ((inds \subseteq hits ++ others) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l * k)).
  Proof.

    elim: l others values inds => [//=| l IHl] others [//=|//= value values] inds Huniq Hlen Hfree Hunseen.

    - {
        under big a _ rewrite Dist1.dE.
        rewrite -rsum_pred_demote big_pred1_eq //=.
        rewrite mul0n rsum_empty //= mulR1.

        rewrite eqb_id RIneq.INR_IZR_INZ; do?apply f_equal.
        apply eq_in_all => ind _; clear.


        case Hin: (ind \in others) => //=.
          by apply bloomfilter_add_internal_hit => //=.

          apply/Bool.negb_true_iff.
          apply bloomfilter_add_internal_miss => //=.
            by apply bloomfilter_new_empty_bits.
              by move/Bool.negb_true_iff: Hin.
      }
    - {

        move=>//=.

        move: (@subseq_imd ([finType of 'I_Hash_size.+1]) l k (fun hits => inds \subseteq hits ++ others)) => //=.
        rewrite card_ord => ->.

        have Hsusp b bs:  (inds \subseteq (b ++ bs) ++ others) = (inds \subseteq bs ++ (others ++ b)); first
          by rewrite -subseq_consA subseq_consC -subseq_consA.

        under big b _ under big bs _ rewrite Hsusp.
        under big b _ rewrite -(IHl (others ++ b) values inds) //=.
        under big a _ rewrite DistBind.dE rsum_Rmul_distr_r rsum_split //=.

        under big a _ under big a0 _ under big b _ rewrite DistBind.dE !rsum_Rmul_distr_l rsum_split //=.
        under big a _ under big a0 _ under big b _ under big a1 _ under big b0 _ rewrite Dist1.dE.

        rewrite exchange_big; under big a0 _ rewrite exchange_big; under big b _ rewrite exchange_big; under big a1 _ rewrite exchange_big;  (under big a _ under big c _  rewrite mulRA mulRC mulRA mulRC mulRA mulRC mulRA mulRA mulRC -mulRA); under big b0 _ rewrite -rsum_pred_demote big_pred1_eq.

        (under big a0 _ (under big b _ rewrite exchange_big); rewrite exchange_big); rewrite exchange_big.

        apply eq_bigr => b _ .

        rewrite rsum_Rmul_distr_l rsum_split //= [\sum_(a in _) (\sum_(b in _) (_ *R* _))]exchange_big.
        rewrite [\sum_(i in [finType of k.-tuple (HashState n)]) (\sum_(i0 in [finType of BloomFilter]) _)]exchange_big ; apply eq_bigr => bf' _.
        apply eq_bigr => hshs' _.


        rewrite -!rsum_Rmul_distr_l.

        rewrite mulRC -mulRA  mulRC -mulRA mulRC.
        apply Logic.eq_sym => //=.

        rewrite  -mulRA  mulRC -mulRA mulRC -mulRA.

        rewrite  bloomfilter_add_multiple_cat; apply f_equal.

        case Hzr0: ((d[ bloomfilter_add_multiple hashes bloomfilter_new values]) (hshs', bf') == 0);
          first by move/eqP: Hzr0 ->;rewrite mulR0 mul0R //=.
        move/Bool.negb_true_iff: Hzr0 => Hzr0.
        rewrite mulRC; apply f_equal; apply Logic.eq_sym.

        clear IHl.

        have H1:   (uniq (value :: values)); first by [].
        have H2: length values == l; first by move: Hlen =>/eqP [->].
        have H3: hashes_have_free_spaces hashes (l + 0).+1; first by rewrite addn0.
        have H4: all (bloomfilter_value_unseen hashes) (value :: values); first by [].
        move: (@bloomfilter_add_multiple_preserve
                 value
                 values l 0 hashes hshs' bloomfilter_new bf'
                 H1 H2 H3 H4 Hzr0
              ) => /andP [Hfree' Huns'].

        move: (@hash_vec_simpl n k hshs' value b (fun _ => 1) Huns')=> //=.
        (under big a _ rewrite mulR1); by move=>->; rewrite mulR1 //=.

          by move/andP: Huniq => [].

          move/allP: Hfree => Hfree; apply/allP => ind Hind; move: (Hfree ind Hind).
            by rewrite/hash_has_free_spaces; rewrite addnS =>/ltnW.
              by move/andP: Hunseen => [].
      }
  Qed.


  Lemma bloomfilter_add_multiple_unwrap 
        hashes l value (values: seq B) inds:
    uniq (value::values) ->
    length values == l ->
    hashes_have_free_spaces (hashes: k.-tuple (HashState n)) (l.+1) ->
    all (bloomfilter_value_unseen hashes) (value::values) ->
    \sum_(a in [finType of k.-tuple (HashState n) * BloomFilter])
     ((d[ bloomfilter_add_multiple (Tuple (hash_vec_insert_length value hashes inds)) bloomfilter_new
                                   values]) a *R*
      (d[ let (hashes2, bf) := a in res' <-$ bloomfilter_query value hashes2 bf; ret res'.2]) true) =
    \sum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
     ((inds \subseteq hits) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l * k)).
  Proof.      


    rewrite/bloomfilter_query //= => Huniq Hlen Hfree Hunseen.
    rewrite (@bloomfilter_add_multiple_unwrap_internal _ _ l) => //=.
    rewrite //= /bloomfilter_query_internal.

    move: Huniq => //=/andP[Hnin Huniq].
    move: (@bloomfilter_add_multiple_unwrap_base
             (Tuple (hash_vec_insert_length value hashes inds)) l values [::] inds Huniq Hlen
          ) => //=.
    under big a _ rewrite cats0.
    move=>-> //=.

    - {
        move: Hfree; rewrite/hashes_have_free_spaces/hash_has_free_spaces//=; clear.
        move=>/allP Hfree; apply/allP => [ //= hsh' /mapP [[hsh ind] /mem_zip/andP [Hhsh Hind] ->]].
        rewrite/hashstate_put //=.
        move: (Hfree hsh Hhsh); clear.      
        rewrite/FixedList.fixlist_length => //=.
        move=> H; apply/ fixedlist_add_incr;move: H.
          by rewrite addnS.
      }
    - {
        move/andP: Hunseen Hnin => [Huns ]; clear.
        rewrite/bloomfilter_value_unseen //=; move=>/allP Hfree Hnin.
        apply/allP => [//= value' Hvalue]; move: (Hfree value' Hvalue)=>/allP  Hfree'.
        apply/allP => //= [ hsh' /mapP [[hsh ind] /mem_zip/andP [Hhsh Hind] ->]].
        move: (Hfree' hsh Hhsh ).
        move/memPn: Hnin => /(_ value' Hvalue); clear; rewrite /hash_unseen/hashstate_put.
          by move=> Hnew Hfind; apply fixmap_find_neq => //=.
      }
  Qed.    
  

  
  

  

  



  Theorem bloomfilter_collision_rsum
          hashes l value (values: seq B):
    length values == l ->
    hashes_have_free_spaces hashes (l.+1) ->
    all (bloomfilter_value_unseen hashes) (value::values) ->
    uniq (value::values) ->
    d[ 
        res1 <-$ bloomfilter_query value hashes (bloomfilter_new);
          let (hashes1, init_query_res) := res1 in
          res2 <-$ bloomfilter_add_multiple hashes1 (bloomfilter_new) values;
            let (hashes2, bf) := res2 in
            res' <-$ bloomfilter_query value hashes2 bf;
              ret (res'.2)
      ] true =
    \sum_(inds in [finType of k.-tuple ('I_Hash_size.+1)])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (\sum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
        ((( inds \subseteq hits) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l * k)))))).
  Proof.
    have H x y z: (y = (0%R)) -> x = z -> x +R+ y = z. by move => -> ->; rewrite addR0.

    move=>//= Hlen Hfree /andP[Huns Halluns]/andP[Hnin Huniq].

    rewrite DistBind.dE.

    (under big a _ rewrite DistBind.dE  rsum_Rmul_distr_r rsum_split exchange_big //=).


    rewrite exchange_big //=.
    (under big j _ rewrite exchange_big//=).

    under big j _ rewrite (bigID (fun i => i == Tuple (hash_vec_insert_length value hashes j))) big_pred1_eq hash_vecP //=.

    have Hfail j: 
      \sum_(i | i != Tuple (hash_vec_insert_length value hashes j))
       \sum_(i0 in ([finType of k.-tuple (HashState n) * bool]))
       ((d[ let (hashes1, _) := i0 in
            res2 <-$ bloomfilter_add_multiple hashes1 bloomfilter_new values;
            (let (hashes2, bf) := res2 in res' <-$ bloomfilter_query value hashes2 bf; ret res'.2)])
          true *R*
        ((d[ hash_vec_int value hashes]) (i, j) *R*
         (Dist1.d (i, bloomfilter_query_internal j bloomfilter_new)) i0)) = (0%R).
    {
      apply prsumr_eq0P => i Hni; first by dispatch_Rgt.
      apply prsumr_eq0P => i0 _; first by dispatch_Rgt.
      rewrite neg_hash_vecP //=  mul0R ?mulR0 //=.
    }



    under big j _ rewrite Hfail addR0 //=.
    apply eq_bigr => inds _.
    under big i _ rewrite Dist1.dE //=.
    rewrite rsum_split //=.

    under big a _ under big b _ rewrite xpair_eqE.
    move: (size_tuple inds) Hkgt0 => {1}<- Hiff.
    move/Bool.negb_true_iff: (bloomfilter_new_empty Hiff) => Hfalse.
    under big a _ under big b _ rewrite Hfalse //=.

    rewrite (bigID (fun a => a == Tuple (hash_vec_insert_length value hashes inds))) big_pred1_eq//=.
    apply H; first by apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; rewrite !mulR0 bigsum_card_constE mulR0; try ( right).


    under big b _ rewrite eq_refl //=.

    rewrite (bigID (fun b => b == false)) big_pred1_eq //=.

    apply H; first by rewrite (eq_bigl (fun i => i == true)); first rewrite big_pred1_eq //= !mulR0; last by case.
    rewrite mulR1 mulRC; apply f_equal.

    rewrite DistBind.dE.

    erewrite  bloomfilter_add_multiple_unwrap => //=.
      by apply/andP; split=>//=.
        by apply/andP; split=>//=.
  Qed.


  Lemma subseq_conv l:
    \sum_(inds in [finType of k.-tuple ('I_Hash_size.+1)])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (\sum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
        ((( inds \subseteq hits) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l * k)))))) =
    ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l.+1 * k) *R*
     \sum_(a in ordinal_finType (l * k))
      (((((a %R) ^R^ k) *R* (Factorial.fact a %R)) *R* ('C(l * k, a) %R)) *R* stirling_no_2 (l * k) a)).
  Proof.

    under big inds _ rewrite rsum_Rmul_distr_l.
    rewrite exchange_big.

    under big inds _ under big inds' _ rewrite mulRA mulRC.

    under big inds _ rewrite -rsum_Rmul_distr_l; under big inds' _ rewrite mulRC.

    have Hbool inds' inds: (inds' \subseteq inds %R) = (inds' \subseteq inds); first by rewrite RIneq.INR_IZR_INZ.

    under big inds _ under big ps _ rewrite -Hbool.
    under big inds _ rewrite -rsum_pred_demote.
    (under big inds _ rewrite rsum_subseq_mult_undup_eq rsum_subseq_mult //=); last first.
      by apply undup_uniq.
      move=>//=.

      

      move:  (second_stirling_number_sum l k Hash_size
                                         (fun len => (((len %R) *R* Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k))
             ) => //= ->.

      have H len: ((((len %R) *R* Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k) *R*
                   (((('C(l * k, len) %R) *R* (Factorial.fact len %R)) *R* stirling_no_2 (l * k) len) *R*
                    (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l * k))) = (
                    (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l.+1 * k)) *R* (
                      ((len %R) ^R^ k) *R*
                      (Factorial.fact len %R) *R*
                      ('C (l * k, len) %R) *R*
                      (stirling_no_2 (l * k) len)
                  )).

      {
        rewrite expRM -mulRA.
        apply Logic.eq_sym.
        rewrite mulRC -!mulRA; apply f_equal.
        rewrite mulRC; apply Logic.eq_sym; rewrite mulRC -!mulRA; apply f_equal.
        rewrite mulRC mulRA mulRA mulRC mulRA mulRC.
        rewrite mulRC mulRA; apply Logic.eq_sym.
        rewrite mulRA mulRA mulRC -!mulRA; do?apply f_equal.
        rewrite mulSnr //=.
          by rewrite Rfunctions.pow_add.    
      }

      under big len _ rewrite H.


        by rewrite -rsum_Rmul_distr_l.
  Qed.




  Theorem bloomfilter_collision_prob
          hashes l value (values: seq B):
    length values == l ->
    hashes_have_free_spaces hashes (l.+1) ->
    all (bloomfilter_value_unseen hashes) (value::values) ->
    uniq (value::values) ->
    d[ 
        res1 <-$ bloomfilter_query value hashes (bloomfilter_new);
          let (hashes1, init_query_res) := res1 in
          res2 <-$ bloomfilter_add_multiple hashes1 (bloomfilter_new) values;
            let (hashes2, bf) := res2 in
            res' <-$ bloomfilter_query value hashes2 bf;
              ret (res'.2)
      ] true =
    ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l.+1 * k) *R*
     \sum_(a in ordinal_finType (l * k))
      (((((a %R) ^R^ k) *R* (Factorial.fact a %R)) *R* ('C(l * k, a) %R)) *R* stirling_no_2 (l * k) a)).
  Proof.
    intros; rewrite (@bloomfilter_collision_rsum _ l) => //=.
      by rewrite  subseq_conv.
  Qed.

End BloomFilter.

(* Local Variables: *)
(* company-coq-local-symbols: (("\\subseteq" . ?⊆)) *)
(* End: *)


