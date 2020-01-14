From mathcomp.ssreflect Require Import
     ssreflect ssrbool ssrnat eqtype fintype
     choice ssrfun seq path bigop finfun finset binomial.

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path.

From infotheo Require Import
     ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From ProbHash.Utils
     Require Import InvMisc seq_ext seq_subset rsum_ext stirling tactics.

From ProbHash.Computation
     Require Import Comp Notationv1.

From ProbHash.Core
     Require Import Hash HashVec FixedList FixedMap AMQ AMQHash.

Module Type BlockedAMQSpec.

  (** number of blocks(amqs) in Blocked AMQ - 1 *)
  Parameter n:nat.

End BlockedAMQSpec.

Module BlockedAMQHash (Spec:  BlockedAMQSpec) (AmqHash: AMQHASH) <: AMQHASH.
  Module AmqHashProperties := AMQHashProperties AmqHash.

  Module BasicMetaHashSpec <: HashSpec.
    Definition B := AmqHash.AMQHashKey.
    Definition Hash_size := Spec.n.
  End BasicMetaHashSpec.

  Module BasicMetaHash <: AMQHASH := BasicHash (BasicMetaHashSpec).
  Module BasicMetaHashProperties := AMQHashProperties BasicMetaHash.

  Definition AMQHashKey := AmqHash.AMQHashKey.
  Definition AMQHashParams :=
    (BasicMetaHash.AMQHashParams * AmqHash.AMQHashParams)%type.
  

  Definition AMQHashValue p :=
    [finType of (BasicMetaHash.AMQHashValue p.1 * AmqHash.AMQHashValue p.2)%type].

  Definition AMQHash p :=
    [finType of
             BasicMetaHash.Hash.HashState p.1 *
     Spec.n.+1.-tuple (AmqHash.AMQHash p.2)
    ].

  Section AMQHash.
    Variable p: AMQHashParams. 

    Definition AMQHash_probability p :=
      (BasicMetaHash.AMQHash_probability p.1 *R* AmqHash.AMQHash_probability p.2).

    Lemma AMQHash_hash_prob_valid:
      \sum_(v in  AMQHashValue p) (AMQHash_probability p) = 1.
    Proof.
      rewrite/AMQHashValue/AMQHash_probability rsum_split //=.
      rewrite -big_distrlr //=.
      rewrite BasicMetaHash.AMQHash_hash_prob_valid mul1R.
      rewrite AmqHash.AMQHash_hash_prob_valid //=.
    Qed.
    
    Definition AMQHash_hashstate_put
               (hashstate: AMQHash p) (key: AMQHashKey) (value: AMQHashValue p): AMQHash p :=
      (BasicMetaHash.AMQHash_hashstate_put hashstate.1 key value.1 ,
       set_tnth
         hashstate.2
         (AmqHash.AMQHash_hashstate_put (tnth hashstate.2 value.1) key value.2)
         value.1
      ).

    (* boolean properties of hash states*)
    Definition AMQHash_hashstate_available_capacity (hashstate: AMQHash p) (l: nat): bool :=
      BasicMetaHash.AMQHash_hashstate_available_capacity
        hashstate.1 l
        && all (fun hsh => AmqHash.AMQHash_hashstate_available_capacity hsh l) hashstate.2.
    
    Definition AMQHash_hashstate_valid (hashstate: AMQHash p) : bool :=
      BasicMetaHash.AMQHash_hashstate_valid
        hashstate.1 
        && all (fun hsh => AmqHash.AMQHash_hashstate_valid hsh) hashstate.2.

    Definition AMQHash_hashstate_contains
               (hashstate: AMQHash p) (key: AMQHashKey) (value: AMQHashValue p) : bool :=
      (BasicMetaHash.AMQHash_hashstate_contains hashstate.1 key value.1 && 
                                                (AmqHash.AMQHash_hashstate_contains (tnth hashstate.2 value.1) key value.2)
      ).

    Definition AMQHash_hashstate_unseen (hashstate: AMQHash p) (key: AMQHashKey) : bool :=
      (BasicMetaHash.AMQHash_hashstate_unseen hashstate.1 key && 
                                              (all (fun hsh => AmqHash.AMQHash_hashstate_unseen hsh key) hashstate.2)
      ).

    (* probabilistic hash operation*)
    Definition AMQHash_hash
               (hashstate: AMQHash p) (key: AMQHashKey) : Comp [finType of (AMQHash p * AMQHashValue p)] :=
      res <-$ BasicMetaHash.Hash.hash _ key hashstate.1;
        let (meta_hash_state',value1) := res in
        let block_hash_state := tnth hashstate.2 value1 in
        res' <-$ AmqHash.AMQHash_hash block_hash_state key;
          let (block_hash_state',ind') := res' in
          let block_hashes := set_tnth
                                hashstate.2
                                block_hash_state'
                                value1 in
          let hash_state' := (meta_hash_state', block_hashes) in
          ret (hash_state', (value1,ind')).

    (* properties of deterministic hash state operations *)
    Section DeterministicOperations.

      Variable hashstate: AMQHash p.


      Lemma AMQHash_hashstate_available_capacityW:
        forall n m, m <= n ->
                    AMQHash_hashstate_valid hashstate ->
                    AMQHash_hashstate_available_capacity hashstate n ->
                    AMQHash_hashstate_available_capacity hashstate m.
      Proof.
        move=> n m Hnm.
        move=>/andP [H1 H2] /andP[H1' H2']; apply/andP; split.
        - by apply BasicMetaHash.AMQHash_hashstate_available_capacityW with (n:=n) => //=.
        - apply /allP => v Hv; move/allP: H2' => /(_ v Hv) H2'; move/allP: H2 => /(_ v Hv) H2.
            by apply AmqHash.AMQHash_hashstate_available_capacityW with (n:=n) => //=.
      Qed.
      
      Lemma AMQHash_hashstate_available_capacity_decr: forall l key value,
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate l.+1 ->
          AMQHash_hashstate_available_capacity (AMQHash_hashstate_put hashstate key value) l.
      Proof.
        move => l key value.
        move=> /andP [H1 /allP H2] /andP [H1' /allP H2']; apply/andP;split.
        - by apply BasicMetaHash.AMQHash_hashstate_available_capacity_decr with (l:=l) => //=.
        - apply/allP => v /tnthP [ind ->]; clear v.
          case Hindeq: (ind == value.1).
          move/eqP:Hindeq ->; rewrite tnth_set_nth_eq //=.
          apply AmqHash.AMQHash_hashstate_available_capacity_decr => //=.
          apply H2; apply mem_tnth.
          apply H2'; apply mem_tnth.
          rewrite tnth_set_nth_neq; last by move/Bool.negb_true_iff:Hindeq.
          apply AmqHash.AMQHash_hashstate_available_capacityW with (n:=l.+1) => //=.
          apply H2; apply mem_tnth.
          apply H2'; apply mem_tnth.
      Qed.
      
      Lemma  AMQHash_hashstate_add_contains_preserve:
        forall (key key': AMQHashKey) (value value': AMQHashValue p),
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 -> 
          key != key' -> AMQHash_hashstate_contains hashstate key value ->
          AMQHash_hashstate_contains (AMQHash_hashstate_put  hashstate key' value') key value.
      Proof.
        move=> key key' value value' /andP[H1 /allP H2] /andP[H1' /allP H2'] Hneq /andP[H1''  H2''].
        apply/andP;split.
        - by apply BasicMetaHash.AMQHash_hashstate_add_contains_preserve => //=.
        - rewrite/AMQHash_hashstate_put.
          case Hvaleq: (value.1 == value'.1).
        - rewrite tnth_set_nth_eq //=.
          apply AmqHash.AMQHash_hashstate_add_contains_preserve => //=.
          apply H2; apply mem_tnth.
          apply H2'; apply mem_tnth.
            by move/eqP:Hvaleq <-.
        - rewrite tnth_set_nth_neq //=; last by move/Bool.negb_true_iff:Hvaleq.
      Qed.
      
      Lemma  AMQHash_hashstate_add_contains_base: forall (key: AMQHashKey) (value: AMQHashValue p),
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 ->
          AMQHash_hashstate_contains (AMQHash_hashstate_put  hashstate key value) key value.
      Proof.
        move=> key  value /andP[H1 /allP H2] /andP[H1' /allP H2'].
        apply/andP;split.
        - by apply BasicMetaHash.AMQHash_hashstate_add_contains_base => //=.
        - rewrite/AMQHash_hashstate_put.
          rewrite tnth_set_nth_eq //=.
          apply AmqHash.AMQHash_hashstate_add_contains_base => //=.
          apply H2; apply mem_tnth.
          apply H2'; apply mem_tnth.
      Qed.
      
      Lemma AMQHash_hashstate_add_valid_preserve: forall (key: AMQHashKey) (value: AMQHashValue p), 
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 -> 
          AMQHash_hashstate_valid (AMQHash_hashstate_put  hashstate key value).
      Proof.
        move=> key  value /andP[H1 /allP H2] /andP[H1' /allP H2'].
        apply/andP;split.
        - by apply BasicMetaHash.AMQHash_hashstate_add_valid_preserve => //=.
        - apply/allP => v /tnthP [ind ->]; clear v.
          case Hindeq: (ind == value.1).
          move/eqP:Hindeq ->; rewrite tnth_set_nth_eq //=.
          apply AmqHash.AMQHash_hashstate_add_valid_preserve => //=.
          apply H2; apply mem_tnth.
          apply H2'; apply mem_tnth.
          rewrite tnth_set_nth_neq; last by move/Bool.negb_true_iff:Hindeq.
          apply H2; apply mem_tnth.
      Qed.
      

      Lemma AMQHash_hashstate_unseenE: forall (hashstate': AMQHash p) (key key': AMQHashKey) (value': AMQHashValue p),
          key != key' ->
          AMQHash_hashstate_unseen hashstate key ->
          hashstate' = AMQHash_hashstate_put hashstate key' value' ->
          AMQHash_hashstate_unseen hashstate' key.
      Proof.
        move=> hashstate' key key' value' Hneq /andP[H1 /allP H2]  ->; clear hashstate'.
        apply/andP;split.
        - apply BasicMetaHash.AMQHash_hashstate_unseenE with
              (hashstate := hashstate.1)
              (key':=key') (value':=value'.1)
          => //=.
        - apply/allP => v /tnthP [ind ->]; clear v.
          case Hindeq: (ind == value'.1).
          move/eqP:Hindeq ->; rewrite tnth_set_nth_eq //=.
          apply AmqHash.AMQHash_hashstate_unseenE with
              (hashstate:=tnth hashstate.2 value'.1) (key':=key') (value':=value'.2)=> //=.
          apply H2; apply mem_tnth.
          rewrite tnth_set_nth_neq; last by move/Bool.negb_true_iff:Hindeq.
          apply H2; apply mem_tnth.
      Qed.

    End DeterministicOperations.

    
    Lemma  AMQHash_hash_unseen_insert_eqE:
      forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value: AMQHashValue p),
        AMQHash_hashstate_unseen hashstate key -> hashstate' = AMQHash_hashstate_put hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value) = AMQHash_probability p.
    Proof.
      move=> hs hs' key [value1 value2] /andP[H1 /allP H2] ->; comp_normalize.
      exchange_big_inwards ltac:(rewrite BasicMetaHashProperties.AMQHash_hash_unseen_simplE; try by []).
      under_all ltac:(rewrite mulRA [BasicMetaHash.AMQHash_probability p.1 *R* _]mulRC -!mulRA).
      under eq_bigr => value' _. {
        move: (H2 _ (mem_tnth value' hs.2)) => H2'.
        rewrite exchange_big //=; under eq_bigr => value'' _.
        rewrite index_enum_simpl AmqHashProperties.AMQHash_hash_unseen_simplE; try by [].
        rewrite mulRA !xpair_eqE !boolR_distr //=.
          by over. by over.
      }
      move=> //=.
      comp_simplify_n 2.
        by rewrite !eq_refl //= mul1R mulR1 //=/AMQHash_probability mulRC.
    Qed.
    

    Lemma  AMQHash_hash_unseen_insert_neqE:
      forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value: AMQHashValue p),
        AMQHash_hashstate_unseen hashstate key -> hashstate' != AMQHash_hashstate_put hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value) = 0.
    Proof.
      move=> hs hs' key [value1 value2] /andP[H1 /allP H2] Hneq; comp_normalize.
      exchange_big_inwards ltac:(rewrite BasicMetaHashProperties.AMQHash_hash_unseen_simplE; try by []).
      under_all ltac:(rewrite mulRA [BasicMetaHash.AMQHash_probability p.1 *R* _]mulRC -!mulRA).
      under eq_bigr => value' _. {
        move: (H2 _ (mem_tnth value' hs.2)) => H2'.
        rewrite exchange_big //=; under eq_bigr => value'' _.
        rewrite index_enum_simpl AmqHashProperties.AMQHash_hash_unseen_simplE; try by [].
        rewrite mulRA !xpair_eqE !boolR_distr //=.
          by over. by over.
      }
      comp_simplify_n 2.
      move: hs' Hneq => [hs'1 hs'2] //=; rewrite/AMQHash_hashstate_put xpair_eqE Bool.negb_andb
                                    =>/orP[] /Bool.negb_true_iff -> //=;
        by rewrite ?(mul0R , mulR0).
    Qed.

    Lemma AMQHash_hash_seen_insertE:
      forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value value': AMQHashValue p),
        AMQHash_hashstate_contains hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value') =
        ((hashstate' == hashstate) && (value' == value)).
    Proof.
      move=> [hs1 hs2] [hs'1 hs'2] key [value1 value2] [value'1 value'2] //= /andP[ //= H1  H2]; comp_normalize.
      under_all ltac:(
        rewrite (@BasicMetaHash.AMQHash_hash_seen_insertE _ _ _ _ value1); try by []
      ).
      under_all ltac:(rewrite  -RIneq.INR_IZR_INZ  boolR_distr).
      comp_simplify_n 2.
      under_all ltac:(
        rewrite (@AmqHash.AMQHash_hash_seen_insertE _ _ _ _ value2); try by []
      ).
      under_all ltac:(rewrite  -RIneq.INR_IZR_INZ  boolR_distr).
      comp_simplify_n 2.
      rewrite !xpair_eqE .
      rewrite -RIneq.INR_IZR_INZ //=; apply f_equal.
      apply f_equal.
      rewrite -!andbA; do ?apply f_equal.
      rewrite andbC; rewrite [RHS]andbC; do ?apply f_equal; apply Logic.eq_sym.
      apply eq_from_tnth => ind.
      case Hvalueq: (ind == value1).
      rewrite tnth_set_nth_eq => //=; first by move/eqP:Hvalueq ->.
      rewrite tnth_set_nth_neq => //=; last by move/Bool.negb_true_iff:Hvalueq.
    Qed.
    
  End AMQHash.    

End BlockedAMQHash.


Module BlockedAMQ
       (Spec:  BlockedAMQSpec) (AmqHash: AMQHASH) (Amq: AMQ AmqHash).

  Module MetaHash := (BlockedAMQHash Spec AmqHash).

  Module AMQ <: AMQ MetaHash.

    Definition AMQStateParams := Amq.AMQStateParams.

    Definition AMQState (p: AMQStateParams) : finType :=
      [finType of (Spec.n.+1).-tuple (Amq.AMQState p)].


    Section AMQ.
      Variable p: AMQStateParams.
      Variable h: MetaHash.AMQHashParams.

      Definition AMQ_add_internal
                 (state: AMQState p) (value: MetaHash.AMQHashValue h) : AMQState p :=
        set_tnth state
                 (Amq.AMQ_add_internal (tnth state value.1) value.2) value.1.

      Definition AMQ_query_internal
                 (state: AMQState p)  (value: MetaHash.AMQHashValue h) : bool :=
        (Amq.AMQ_query_internal (tnth state value.1) value.2).

      Definition AMQ_available_capacity
                 (h: MetaHash.AMQHashParams) (state: AMQState p) (l: nat) : bool :=
        all (fun hsh => Amq.AMQ_available_capacity h.2 hsh l) state.

      Definition AMQ_valid (state: AMQState p) : bool :=
        all (fun hsh => Amq.AMQ_valid hsh) state.

      Definition AMQ_new: AMQState p := @nseq_tuple (Spec.n.+1) _ (Amq.AMQ_new p).

      Lemma AMQ_new_nqueryE: forall vals, ~~ AMQ_query_internal  AMQ_new vals.
      Proof.
        move=> vals; rewrite/AMQ_query_internal tnth_nseq_eq; apply Amq.AMQ_new_nqueryE.
      Qed.

      Lemma AMQ_new_validT: AMQ_valid AMQ_new.
      Proof.
        apply/allP => v /tnthP [ind ->]; clear v.
        rewrite tnth_nseq_eq; apply Amq.AMQ_new_validT.
      Qed.

      Section DeterministicProperties.
        Variable amq: AMQState p.

        Lemma AMQ_available_capacityW: forall  n m,
            AMQ_valid amq -> m <= n ->
            AMQ_available_capacity h amq n ->
            AMQ_available_capacity h amq m.
        Proof.
          move=>n m /allP Hval Hnm /allP Hcap; apply/allP => v Hv.
          apply Amq.AMQ_available_capacityW with (n:=n) => //=.
          apply Hval => //=.
          apply Hcap => //=.
        Qed.

        Lemma AMQ_add_query_base: forall (amq: AMQState p) inds,
            AMQ_valid amq -> AMQ_available_capacity h amq 1 ->
            AMQ_query_internal (AMQ_add_internal amq inds) inds.
        Proof.
          move=> amq' inds /allP Hvalid /allP Hcap.
          rewrite/AMQ_query_internal/AMQ_add_internal.
          rewrite tnth_set_nth_eq //=.
          apply Amq.AMQ_add_query_base.
          apply Hvalid; apply mem_tnth.
          apply Hcap; apply mem_tnth.
        Qed.

        Lemma AMQ_add_query_preserve: forall (amq: AMQState p) inds inds',
            AMQ_valid amq -> AMQ_available_capacity h amq 1 ->
            AMQ_query_internal amq inds ->
            AMQ_query_internal (AMQ_add_internal amq inds') inds.
        Proof.
          move=> amq' ind ind' /allP Hvalid /allP Hcap.
          rewrite/AMQ_query_internal/AMQ_add_internal => Hquery.
          case Hind: (ind.1 == ind'.1).
          - move/eqP:(Hind) <-;rewrite tnth_set_nth_eq //=;apply Amq.AMQ_add_query_preserve =>//=.
            apply Hvalid; apply mem_tnth.
            apply Hcap; apply mem_tnth.
          - move/Bool.negb_true_iff: Hind => Hind.
              by rewrite tnth_set_nth_neq //=.
        Qed.

        Lemma AMQ_add_valid_preserve: forall (amq: AMQState p) inds,
            AMQ_valid amq -> AMQ_available_capacity h amq 1 ->
            AMQ_valid (AMQ_add_internal amq inds).
        Proof.
          move=> amq' ind /allP Hvalid /allP Hcap.
          apply/all_tnthP => ind'.
          rewrite/AMQ_add_internal.
          case Hindeq: (ind.1 == ind').
          - move/eqP:(Hindeq) <-; rewrite tnth_set_nth_eq //=; apply Amq.AMQ_add_valid_preserve => //=.
            apply Hvalid; apply mem_tnth.
            apply Hcap; apply mem_tnth.
          - move/Bool.negb_true_iff: Hindeq => Hind.
            rewrite tnth_set_nth_neq //=; last by rewrite eq_sym.
            apply Hvalid; apply mem_tnth.
        Qed.

        Lemma AMQ_add_capacity_decr: forall (amq: AMQState p) inds l,
            AMQ_valid amq -> AMQ_available_capacity h amq l.+1 ->
            AMQ_available_capacity h (AMQ_add_internal amq inds) l.
        Proof.
          move=> amq' ind l /allP Hvalid /allP Hcap.
          apply/all_tnthP => ind'.
          rewrite/AMQ_add_internal.
          case Hindeq: (ind.1 == ind').
          - move/eqP:(Hindeq) <-; rewrite tnth_set_nth_eq //=; apply Amq.AMQ_add_capacity_decr => //=.
            apply Hvalid; apply mem_tnth.
            apply Hcap; apply mem_tnth.
          - move/Bool.negb_true_iff: Hindeq => Hind.
            rewrite tnth_set_nth_neq //=; last by rewrite eq_sym.
            apply Amq.AMQ_available_capacityW with (n:=l.+1) => //=.
            apply Hvalid; apply mem_tnth.
            apply Hcap; apply mem_tnth.
        Qed.
      End DeterministicProperties.
    End AMQ.

  End AMQ.



  Module BlockedAMQProperties (AmqProperties: AMQProperties AmqHash Amq) :
    AMQProperties MetaHash AMQ.

    Module AmqOperations := AMQOperations (MetaHash) (AMQ).
    Export AmqOperations.


    Definition AMQ_false_positive_probability (h: AMQHashParams) (s: AMQStateParams) (n:nat): Rdefinitions.R :=
      \sum_(i < n.+1)
       (('C(n, i) %R) *R*
        ((BasicMetaHash.AMQHash_probability (h.1)) ^R^ i) *R*
        ((1 -R- (BasicMetaHash.AMQHash_probability (h.1))) ^R^ (n - i)) *R*
        (AmqProperties.AMQ_false_positive_probability (h.2) s i)
       )
    .

    Section Properties.
      Variable h : AMQHashParams.
      Variable s: AMQStateParams.

      Variable hashes: AMQHash h.

      Section NoFalseNegatives.
        
        Variable amq: AMQState s.

        Lemma AMQ_no_false_negatives:
          forall (l:nat_eqType) (x:AMQHashKey) (xs: seq AMQHashKey),
            uniq (x :: xs) -> length xs == l ->
            AMQ_valid amq -> AMQ_available_capacity h amq l.+1 ->
            AMQHash_hashstate_valid hashes ->
            AMQHash_hashstate_available_capacity hashes l.+1 ->
            all (AMQHash_hashstate_unseen hashes) (x::xs) ->
            (d[ res1 <-$ AMQ_add amq hashes x;
                  let '(hsh1, amq1) := res1 in
                  res2 <-$ AMQ_add_multiple hsh1 amq1 xs;
                    let '(hsh2, amq2) := res2 in
                    res3 <-$ AMQ_query amq2 hsh2 x;
                      ret (snd res3) ] true) = (1 %R).
        Proof.
            by apply AmqOperations.AMQ_no_false_negatives.
        Qed.

      End NoFalseNegatives.

      Lemma AMQ_add_multipl_foldl  f j (vs: seq (AMQHashValue h)) (i : AmqHash.AMQHashValue h.2) a key_1 key_2:
        f = (fun a => foldl (fun amq vl => @AMQ_add_internal _ h amq vl) a vs) ->
        j != key_2 -> (AMQ_query_internal
                         (f (AMQ_add_internal a (j, i)))
                         (key_2, key_1)) =
                      (@AMQ_query_internal s _
                                           (f a)
                                           (key_2, key_1)).
      Proof.
        move=>-> Hneq; clear f.
        rewrite /AMQ_add_internal.
        have Hs pp qq: (pp, qq).1 = pp; last rewrite !Hs; last clear Hs; first by [].
        have Hs pp qq: (pp, qq).2 = qq; last rewrite !Hs; last clear Hs; first by [].
        suff H f:
          AMQ_query_internal
            (foldl
               (fun (amq : AMQState s) (vl : AMQHashValue h) =>
                  set_tnth amq (f (tnth amq vl.1) vl.2) vl.1)
               (set_tnth a (f (tnth a j) i) j) vs) (key_2, key_1) =
          AMQ_query_internal
            (foldl
               (fun (amq : AMQState s) (vl : AMQHashValue h) =>
                  set_tnth amq (f (tnth amq vl.1) vl.2) vl.1) a vs)
            (key_2, key_1).
        eapply H.
        elim: vs f a j i key_1 key_2 Hneq  => [| [v_1 v_2] vs Hvs] f a j i key_1 key_2 Hneq.
        - {
            rewrite /AMQ_query_internal/AMQ_add_internal //.
            rewrite tnth_set_nth_neq //=; last by rewrite eq_sym.
          }
        -{
            case Hv1: (v_1 == key_2); last by
                move/Bool.negb_true_iff: Hv1 => Hv1; by do ?rewrite Hvs //=.
            move/eqP: Hv1 ->; clear v_1.

            have Hfold f' y ys y' :
              foldl f' y' (y::ys) = foldl f' (f' y' y) ys; last rewrite !Hfold; first by [].
            rewrite tnth_set_nth_neq; last by rewrite eq_sym.
            have Hs pp qq: (pp, qq).1 = pp; last rewrite !Hs; last clear Hs; first by [].
            have Hs pp qq: (pp, qq).2 = qq; last rewrite !Hs; last clear Hs; first by [].

            have ->:
                 (set_tnth (set_tnth a (f (tnth a j) i) j)
                           (f (tnth a key_2) v_2) key_2) =
            (set_tnth (set_tnth a (f (tnth a key_2) v_2) key_2)
                      (f (tnth a j) i) j). {
              move: (f (tnth a j) i) (f (tnth a key_2) v_2) => s1 s2.
              move: a; rewrite/AMQState => a.
              apply eq_from_tnth => v.
              case Hveq: (v == key_2).
              move/eqP: Hveq ->; rewrite tnth_set_nth_eq; clear v; last by [].
              rewrite tnth_set_nth_neq; last by rewrite eq_sym.
                by rewrite tnth_set_nth_eq.
                move/Bool.negb_true_iff: Hveq => Hveq.
                rewrite tnth_set_nth_neq; last by [].
                case Hvej: (v == j).
                move/eqP:Hvej ->; rewrite tnth_set_nth_eq; last by[].
                  by rewrite tnth_set_nth_eq.
                  move/Bool.negb_true_iff: Hvej => Hvej.
                  rewrite tnth_set_nth_neq; last by [].
                  rewrite tnth_set_nth_neq; last by [].
                    by rewrite tnth_set_nth_neq.
            }

            move: (Hvs f (set_tnth a (f (tnth a key_2) v_2) key_2)
                       j i key_1 key_2 Hneq).
            rewrite tnth_set_nth_neq; last by [].
              by move=> -> //=.
          }
      Qed.

      
      Lemma AMQ_add_multipl_foldl_foldr  f i (vs: seq (AMQHashValue h)) a key_1 key_2:
        f = (fun a => foldl (fun amq vl => @AMQ_add_internal _ h amq vl) a vs) ->
        (@AMQ_query_internal _ h
                             (f (foldr (fun hash' : _ => (AMQ_add_internal (h:=h))^~ hash') a
                                       (filter (fun hash' : _ => hash'.1 != key_2) i))) (key_2, key_1)) =
        (@AMQ_query_internal s _ (f a) (key_2, key_1)).
      Proof.
        move=> ->; clear f.
        elim: i vs a key_1 key_2 => [| [x1 x2] xs Hxs] vs a key_1 key_2 //=.
        case Hxeq: (x1 != key_2).
        - {
            rewrite (@AMQ_add_multipl_foldl
                       (fun a => foldl (fun amq vl => @AMQ_add_internal _ h amq vl) a vs) x1 vs x2
                       (foldr
                          (fun hash' : 'I_BasicMetaHashSpec.Hash_size.+1 * AmqHash.AMQHashValue h.2 =>
                             (AMQ_add_internal (h:=h))^~ hash') a
                          (filter (fun hash' : _ => hash'.1 != key_2) xs) )
                       key_1 key_2 (Logic.eq_refl _) Hxeq
                    ).
              by rewrite Hxs //=.
          }
        - {
              by rewrite Hxs //=.
          }
      Qed.
      
      Lemma AMQ_add_mulitpl_filter (i1:AMQHashValue h) (i: seq _) (a:AMQState s):
        AMQ_query_internal
          (foldr (fun hash' : 'I_BasicMetaHashSpec.Hash_size.+1 * AmqHash.AMQHashValue h.2 =>
                    (AMQ_add_internal (h:=h))^~ hash') a i ) i1 =
        AMQ_query_internal
          (foldr (fun hash' : 'I_BasicMetaHashSpec.Hash_size.+1 * AmqHash.AMQHashValue h.2 =>
                    (AMQ_add_internal (h:=h))^~ hash') a
                 (filter (fun hash' : _ => hash'.1 == i1.1) i)) i1.
      Proof.
        move: i1 => [key_1 key_2].
        rewrite -!foldl_rev //=.
        rewrite -filter_rev; move: (rev i); clear i => i.
        elim: i a key_1 key_2 =>  [| [x1 x2] xs IHl] a key_1 key_2 //=.
        case Hxeq: (x1 != key_1) => //=.
        {
          move/Bool.negb_true_iff:(Hxeq) ->.
          move: (@AMQ_add_multipl_foldl
                   (fun a => (foldl (AMQ_add_internal (h:=h)) a xs)) x1 xs x2 a  key_2 key_1
                   (Logic.eq_refl _) Hxeq
                ) ->.
            by eapply IHl => //=.
        }
        {
          move/Bool.negb_true_iff: Hxeq; rewrite Bool.negb_involutive => Hxeq; rewrite Hxeq.
            by move=> //=.
        }
      Qed.

      Lemma AMQ_query_simplify a key xs:
        @AMQ_query_internal s h
                            (foldr
                               (fun hash' : 'I_BasicMetaHashSpec.Hash_size.+1 * AmqHash.AMQHashValue h.2 =>
                                  (AMQ_add_internal (h:=h))^~ hash') a
                               (filter (fun hash' => hash'.1 == key.1) xs)) key =
        Amq.AMQ_query_internal
          (foldr (fun hash' : AmqHash.AMQHashValue h.2 =>
                    (Amq.AMQ_add_internal (h:=h.2))^~ hash') ((tnth a key.1))
                 (map (fun x => x.2) (filter (fun hash' => hash'.1 == key.1) xs))) key.2.
      Proof.
        rewrite -!foldl_rev //=; rewrite -!map_rev -!filter_rev.
        move: (rev xs); clear xs => xs.
        elim: xs a key => [| x xs Hxs] a key.
        - by rewrite //= /AMQ_query_internal.
        - {
            case Hxeq: (x.1 == key.1) => //=; rewrite Hxeq.
            - {
                rewrite Hxs //=; rewrite/AMQ_add_internal.
                rewrite tnth_set_nth_eq //=; last by rewrite eq_sym.
                  by move/eqP: Hxeq ->.
              }
            - by rewrite Hxs //=; rewrite/AMQ_add_internal.
          }
      Qed.

      Lemma hash_size_map_filter l ind (i: l.-tuple ('I_BasicMetaHashSpec.Hash_size.+1 * AmqHash.AMQHashValue h.2)%type):
        size (map (fun x => x.2) (filter (fun hash' => hash'.1 == ind) i)) < l.+1.
      Proof.
        rewrite size_map.
        move: i => [xs /eqP Hi] //=; rewrite -Hi.
        rewrite !length_sizeP.
          by apply filter_leq_size.
      Qed.

      Lemma AMQHash_rsum_subs_eq (A:finType)  l len ind f
            (xs : l.-tuple 'I_BasicMetaHashSpec.Hash_size.+1)
            (Hxs: size [seq x | x <- xs & x == ind] == len):
        \sum_(a in [finType of l.-tuple A])
         (f [seq x.2 | x <- zip xs a & x.1 == ind]) =
        ((#| A | ^R^ (l - len)) *R*
         \sum_(i0 in [finType of len.-tuple A]) (f i0)).
      Proof.
        move: xs f len Hxs => [].
        elim: l => [| l IHl] [| x xs] Hxs f //=.
        - {
              by move=> len /eqP <-; rewrite !rsum_empty //= mul1R.
          }
        - {
            case Hxeq: (x == ind).
            - {
                move=> [//=|len] Hsize.
                rewrite subSS; apply Logic.eq_sym.
                rewrite rsum_tuple_split rsum_split //=.
                rewrite rsum_Rmul_distr_l.
                have H1: size xs == l; first by move: Hxs => //= /eqP [].
                have H2: size [seq x0 | x0 <- Tuple H1 & x0 == ind] == len; first
                  by move: Hsize => //=/eqP [].
                under eq_bigr => i _. {
                  rewrite -(@IHl xs H1 (fun b => f (i :: b)) len H2).
                    by over.
                }
                move=> //=.
                rewrite rsum_tuple_split rsum_split //=.
                apply eq_bigr => a _.
                apply eq_bigr => ass _.
                  by rewrite Hxeq //=.
              }
            - {
                move=> len Hsize.
                rewrite rsum_tuple_split rsum_split //=.
                rewrite Hxeq.
                have H1: size xs == l; first by move: Hxs => //= /eqP [].
                have H2: size [seq x0 | x0 <- Tuple H1 & x0 == ind] == len; first
                  by move: Hsize => //=/eqP [].
                move: (@IHl xs H1 f len H2) => //= Heq.
                under eq_bigr do rewrite Heq.
                rewrite -big_distrl //= mulRC; apply Logic.eq_sym.
                rewrite mulRC; apply f_equal.
                rewrite bigsum_card_constE.
                rewrite RIneq.INR_IZR_INZ -expRS.
                apply f_equal; rewrite -subSn//=.
                clear -H1 Hsize.
                move/eqP: Hsize <-.
                move/eqP: H1 <-.
                elim: xs => //= x xs Hxs //=.
                case: (x == ind) => //=.
                  by apply leq_trans with (n:=size xs) => //=.
              }
          }
      Qed.

      Theorem AMQ_false_positives_rate: forall  (l:nat) value (values: seq _),
          length values == l ->

          AMQHash_hashstate_valid hashes ->
          AMQHash_hashstate_available_capacity hashes (l.+1) ->


          AMQ_available_capacity h (AMQ_new s) l.+1 ->
          all (AMQHash_hashstate_unseen hashes) (value::values) ->
          uniq (value::values) ->
          d[ 
              res1 <-$ AMQ_query (AMQ_new s) hashes value;
                let (hashes1, init_query_res) := res1 in
                res2 <-$ AMQ_add_multiple hashes1 (AMQ_new s) values;
                  let (hashes2, amq) := res2 in
                  res' <-$ AMQ_query amq  hashes2 value;
                    ret (res'.2)
            ] true = AMQ_false_positive_probability h s l.
      Proof.
        move=> l value values Hlen Hvalid Hcap Hcap_new Hunseen Huniq.
        rewrite (@AMQ_false_positives_simplify_normalize _ _ _ l) //=.
        under_all ltac:(rewrite  AMQ_add_mulitpl_filter).
        under_all ltac:(rewrite  AMQ_query_simplify).
        rewrite /AMQ_false_positive_probability.
        rewrite rsum_split //=.
        rewrite {1}/AMQHash_probability.
        under eq_bigr do under eq_bigr do rewrite -!mulRA.
        under eq_bigr do rewrite -rsum_Rmul_distr_l.
        suff H' ind:
          \sum_(b in AmqHash.AMQHashValue h.2)
           (AmqHash.AMQHash_probability h.2 *R*
            \sum_(i in [finType of l.-tuple ('I_BasicMetaHashSpec.Hash_size.+1 * AmqHash.AMQHashValue h.2)%type])
             ((AMQHash_probability h ^R^ l) *R*
              (Amq.AMQ_query_internal
                 (foldr (fun hash' : AmqHash.AMQHashValue h.2 => (Amq.AMQ_add_internal (h:=h.2))^~ hash')
                        (tnth (AMQ_new s) ind) [seq x.2 | x <- i & x.1 == ind]) b %R))) =
          \sum_(i < l.+1)
           (((('C(l, i) %R) *R* (BasicMetaHash.AMQHash_probability h.1 ^R^ i)) *R*
             ((BinNums.Zpos BinNums.xH -R- BasicMetaHash.AMQHash_probability h.1) ^R^ l - i)) *R*
            AmqProperties.AMQ_false_positive_probability h.2 s i).
        under eq_bigr => ind _ do rewrite (H' ind).
        {
          rewrite -big_distrl //=.
            by rewrite  BasicMetaHash.AMQHash_hash_prob_valid mul1R.
        }
        under eq_bigr => b _. {
          rewrite (@partition_big
                     _ _ _ _ _ _
                     (fun (i: [finType of l.-tuple
                                       ('I_BasicMetaHashSpec.Hash_size.+1 *
                                        AmqHash.AMQHashValue h.2)%type]) =>
                        Ordinal ( hash_size_map_filter ind i)) predT 
                  ) //=.
            by over.
        }
        under eq_bigr do rewrite rsum_Rmul_distr_l.
        rewrite exchange_big //=; apply eq_bigr => len _.
        have H (i: 'I_Spec.n.+1) (l':nat) (Hl: l' <= l)  :
          \sum_(i1 in [finType of AmqHash.AMQHashValue h.2])
           (AmqHash.AMQHash_probability h.2 *R*
            \sum_(i0 in [finType of l'.-tuple (AmqHash.AMQHashValue h.2)])
             ((AmqHash.AMQHash_probability h.2 ^R^ l') *R*
              (Amq.AMQ_query_internal
                 (foldr (fun hash' : AmqHash.AMQHashValue h.2 => (Amq.AMQ_add_internal (h:=h.2))^~ hash')
                        (Amq.AMQ_new s) i0) i1 %R))) = AmqProperties.AMQ_false_positive_probability h.2 s l'. {
          have Hvalid': AmqHash.AMQHash_hashstate_valid (tnth hashes.2 i); first
            by move: Hvalid => //=/andP[_ /allP H1]; apply H1; apply mem_tnth.

          have Hcap': AmqHash.AMQHash_hashstate_available_capacity (tnth hashes.2 i) l'.+1; first
            by apply AmqHash.AMQHash_hashstate_available_capacityW with (n:=l.+1)
          => //=; move: Hcap => //=/andP[ _ /allP H2]; apply H2; apply mem_tnth.

          have Hcap'': Amq.AMQ_available_capacity h.2 (Amq.AMQ_new s) l'.+1; first
            by apply Amq.AMQ_available_capacityW with (n:=l.+1)
          => //=; first apply Amq.AMQ_new_validT; last move:Hcap_new;rewrite/AMQ_available_capacity=>//=/andP[].
          have Huns: all (AmqHash.AMQHash_hashstate_unseen (tnth hashes.2 i)) (value :: (take l' values)). {
            move=>//=;apply/andP;split.
              by move:Hunseen=>//=;rewrite/AMQHash_hashstate_unseen
                             =>/andP[/andP[_ /allP Hv] _];apply Hv;apply mem_tnth.
                by move:Hunseen=>//=;rewrite/AMQHash_hashstate_unseen=>/andP[_ /allP Hv];
                  apply/allP => v /mem_take/Hv/andP[_/allP Hv']; apply Hv'; apply /mem_tnth.
          }
          have Hlen': length (take l' values) == l'; first by rewrite -length_sizeP size_takel //= length_sizeP;move/eqP:Hlen ->.

          have Huniq': uniq (value :: take l' values). {
            move=> //=; apply/andP;split.
              by apply/memPn => v /mem_take Hv; move: Huniq => //=/andP[/memPn Hn _]; apply Hn.
              move: Huniq=>//=/andP[Hnin Huniq].
              move: Hl;rewrite leq_eqVlt=>/orP[/eqP->|Hltn].
              rewrite take_oversize//=length_sizeP;move/eqP:Hlen->=>//=.
              apply uniq_take=>//=;first rewrite?length_sizeP;first move/eqP:Hlen=>->//=.
          }
          move: (@AmqProperties.AMQ_false_positives_rate
                   h.2 s (tnth hashes.2 i) l' value (take l' values)
                   Hlen' Hvalid' Hcap' Hcap'' Huns Huniq').
          rewrite (@AmqProperties.AmqOperations.AMQ_false_positives_simplify_normalize
                     h.2 s (tnth hashes.2 i) l') //=.
        }

        have: 'I_Spec.n.+1; first apply Ordinal with (m:=0) => //=.
        move=>/H;clear H=>H.
        apply Logic.eq_sym.
        rewrite -(@H len).
        rewrite rsum_Rmul_distr_l -index_enum_simpl; apply eq_bigr => ind' _.
        rewrite mulRA [_ *R* AmqHash.AMQHash_probability h.2]mulRC -!mulRA.
        apply f_equal; apply Logic.eq_sym=>//=.
        rewrite rsum_zip_tuple_split //=.
        rewrite rsum_pred_demote rsum_split //=.
        rewrite -index_enum_simpl.
        have H' (T:eqType) m  (a: m.-tuple _) (b: m.-tuple T):
          (size [seq x.2 | x <- zip a b & x.1 == ind]) == len = (size [seq x | x <- a & x == ind] == len). {
          rewrite size_map.
          rewrite (@filter_zip_L _ _  m).
          rewrite size1_zip //=.
          move: a len => [xs Hxs] [len Hlen'] //=.
          suff:
            (@filter (ordinal (S Spec.n))
                     (@PredOfSimpl.coerce (ordinal (S Spec.n)) (@pred1 (ordinal_eqType (S Spec.n)) ind))
                     xs) = [seq x | x <- xs & x == ind]; first by move=><-//=.
          clear Hlen' Hxs => //=.
            by rewrite map_id.
            move: a b len => [xs Hxs] [ys Hys] [len Hlen'] //=.
            clear Hlen'  => //=.
            rewrite leq_eqVlt; apply/orP; left; apply/eqP.
            elim: xs m ys Hxs Hys  => //= x xs Hxs  [| m] [| y ys] Hxs' Hys //=.
            case Hxeq: (x == ind) => //=.
              by rewrite (Hxs m ys) //=.
                by rewrite (Hxs m ys) //=.
                  by move: a => [a Ha] //=; apply/eqP.
                    by move: b => [b Hb] //=; apply/eqP.
        }

        under_all ltac:(rewrite eqnE).
        under eq_bigr => a _ do under eq_bigr => b _ do rewrite H'; clear H'.
        under eq_bigr do rewrite -rsum_Rmul_distr_l.
        rewrite -rsum_pred_demote.
        under eq_bigr => a _ do under eq_bigr => b _ do rewrite expRM -!mulRA.
        under eq_bigr do rewrite -rsum_Rmul_distr_l.
        rewrite /BasicMetaHash.AMQHash_probability.
        rewrite /BasicMetaHash.AMQHashValue.

        rewrite  (@binomial_summation
                    _ _ _ _ _
                    (\sum_(i0 in [finType of len.-tuple (AmqHash.AMQHashValue h.2)])
                      ((AmqHash.AMQHash_probability h.2 ^R^ len) *R*
                       (Amq.AMQ_query_internal
                          (foldr
                             (fun hash' : AmqHash.AMQHashValue h.2 => (Amq.AMQ_add_internal (h:=h.2))^~ hash')
                             (Amq.AMQ_new s) i0) ind' %R)))) => //=.

        move=> vs Hvs.
        move: (@AmqHash.AMQHash_hash_prob_valid h.2).
        rewrite bigsum_card_constE => Hvld.
        case Hz0: ((#|AmqHash.AMQHashValue h.2| %R) == BinNums.Z0).
        move/eqP: Hz0 Hvld => ->; rewrite mul0R //= =>/eqP //=; rewrite eq_sym=>/eqP/Nsatz.R_one_zero //=.
        move/Bool.negb_true_iff: Hz0=>/eqP Hnz0.
        move: Hvld; rewrite -(@RIneq.Rinv_r (#|AmqHash.AMQHashValue h.2| %R) Hnz0).
        move=>/(eqR_mul2l Hnz0) ->.
        rewrite -!rsum_Rmul_distr_l.
        rewrite (@AMQHash_rsum_subs_eq _ l len ind
                                       (fun a =>
                                          ((Amq.AMQ_query_internal
                                              (foldr (fun hash' : AmqHash.AMQHashValue h.2
                                                      => (Amq.AMQ_add_internal (h:=h.2))^~ hash')
                                                     (tnth (AMQ_new s) ind) a) ind' %R))
                )) //=.
        rewrite mulRA.
        have: ((Rdefinitions.Rinv (#|AmqHash.AMQHashValue h.2| %R) ^R^ l) *R*
               (#|AmqHash.AMQHashValue h.2| ^R^ l - len)) =
              ((Rdefinitions.Rinv (#|AmqHash.AMQHashValue h.2| %R) ^R^ len)).
        {
          clear -Hnz0; move: len => [m Hm] //=; rewrite -{1}(@subnK m l) //=.
          rewrite -{1}plusE RealField.Rdef_pow_add.
          rewrite -mulRA [_ *R*(#|AmqHash.AMQHashValue h.2| ^R^ l - m)]mulRC mulRA.
          rewrite -Rfunctions.Rinv_pow.
          rewrite [((#|AmqHash.AMQHashValue h.2| %R) ^- (l - m)) *R* _]mulRC.
          rewrite RIneq.INR_IZR_INZ.
          rewrite mulRV //=.
          rewrite mul1R //=.
            by apply expR_neq0; rewrite -RIneq.INR_IZR_INZ; apply/eqP.
              by [].
        }
        move=>-> //=.
        apply f_equal; apply eq_bigr => a Ha.
        rewrite tnth_nseq_eq//=.
          by move: len => [m Hl] //=.
      Qed.

    End Properties.
  End  BlockedAMQProperties.
End BlockedAMQ.

