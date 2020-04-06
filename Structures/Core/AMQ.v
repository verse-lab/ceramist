From mathcomp.ssreflect Require Import
     ssreflect ssrbool ssrnat eqtype fintype
     choice ssrfun seq path bigop finfun finset binomial.

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path.

From infotheo Require Import
      fdist ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From ProbHash.Utils
     Require Import InvMisc  seq_ext seq_subset rsum_ext stirling tactics.

From ProbHash.Computation
     Require Import Comp Notationv1.

From ProbHash.Core
     Require Import Hash HashVec FixedList FixedMap AMQHash.

Module Type AMQ (AMQHash: AMQHASH).


  Parameter AMQStateParams : Type.
  Parameter AMQState : AMQStateParams -> finType.


  Section AMQ.
    Variable p: AMQStateParams.
    Variable h: AMQHash.AMQHashParams.

    Parameter AMQ_add_internal: AMQState p -> AMQHash.AMQHashValue h -> AMQState p.
    Parameter AMQ_query_internal: AMQState p -> AMQHash.AMQHashValue h -> bool.
    Parameter AMQ_available_capacity: AMQHash.AMQHashParams -> AMQState p -> nat -> bool.
    Parameter AMQ_valid: AMQState p -> bool.

    Axiom AMQ_new: AMQState p.
    Axiom AMQ_new_nqueryE: forall vals, ~~ AMQ_query_internal  AMQ_new vals.
    Axiom AMQ_new_validT: AMQ_valid AMQ_new.

    Section DeterministicProperties.
      Variable amq: AMQState p.

      Axiom AMQ_available_capacityW: forall  n m,
          AMQ_valid amq -> m <= n ->
          AMQ_available_capacity h amq n ->
          AMQ_available_capacity h amq m.

      Axiom AMQ_add_query_base: forall (amq: AMQState p) inds,
          AMQ_valid amq -> AMQ_available_capacity h amq 1 ->
          AMQ_query_internal (AMQ_add_internal amq inds) inds.

      Axiom AMQ_add_query_preserve: forall (amq: AMQState p) inds inds',
          AMQ_valid amq -> AMQ_available_capacity h amq 1 ->
          AMQ_query_internal amq inds ->
          AMQ_query_internal (AMQ_add_internal amq inds') inds.

      Axiom AMQ_add_valid_preserve: forall (amq: AMQState p) inds,
          AMQ_valid amq -> AMQ_available_capacity h amq 1 ->
          AMQ_valid (AMQ_add_internal amq inds).

      Axiom AMQ_add_capacity_decr: forall (amq: AMQState p) inds l,
          AMQ_valid amq -> AMQ_available_capacity h amq l.+1 ->
          AMQ_available_capacity h (AMQ_add_internal amq inds) l.

    End DeterministicProperties.
  End AMQ.
End AMQ.

Module AMQOperations (AmqHash: AMQHASH) (Amq: AMQ AmqHash).

  Export AmqHash.
  Export Amq.

  Module AmqHashProperties := (AMQHashProperties AmqHash).
  Import AmqHashProperties.

  Section Operations.

    Variable h : AMQHashParams.
    Variable s: AMQStateParams.

    Definition AMQ_add (amq: AMQState s)   (hashes: AMQHash h) (value: AMQHashKey) :
      Comp [finType of (AMQHash h) * AMQState s] :=
      hash_res <-$ (AMQHash_hash  hashes value);
        let (new_hashes, hash_vec) := hash_res in
        let new_amq := AMQ_add_internal amq hash_vec in
        ret (new_hashes, new_amq).

    Definition AMQ_query (amq: AMQState s)   (hashes: AMQHash h) (value: AMQHashKey) :
      Comp [finType of (AMQHash h) * bool] :=
      hash_res <-$ (AMQHash_hash  hashes value);
        let (new_hashes, hash_vec) := hash_res in
        let new_amq := AMQ_query_internal amq hash_vec in
        ret (new_hashes, new_amq).
    

    Definition AMQ_add_multiple  hsh_0 bf_0 values :=
      @foldr _ (Comp [finType of AMQHash h * AMQState s])
             (fun val hsh_bf =>
                res_1 <-$ hsh_bf;
                  let (hsh, bf) := res_1 in
                  AMQ_add bf hsh val) (ret (hsh_0, bf_0)) values.
  End Operations.

  Section Properties.
    Variable h : AMQHashParams.
    Variable s: AMQStateParams.

    Variable hashes: AMQHash h.
    Variable amq: AMQState s.

    Lemma AMQ_add_multiple_properties_preserve  ( cbf': AMQState s)  values inds' l m:
      length values == l -> AMQ_valid amq ->  AMQ_available_capacity h amq (l + m) ->
      (P[ AMQ_add_multiple hashes amq values === (inds', cbf')] != 0) ->
      AMQ_valid cbf' && AMQ_available_capacity h cbf' m.
    Proof.
      move=>/eqP <-; clear l.
      elim: values m amq cbf' inds' => [| x xs Hxs] m cbf cbf' inds' Hvalid Havail //=; comp_normalize;
                                         first by move=>/bool_neq0_true; rewrite xpair_eqE=>/andP[_ /eqP -> ]; apply/andP => //=.
      exchange_big_outwards 2 => //=; comp_simplify_n 1; comp_possible_decompose.
      move=> cbf'' inds'' Hind Haddm Hhash /bool_neq0_true/eqP ->.
      move: Havail => //=; rewrite addSn -addnS => Havail.
      move: (@Hxs m.+1 cbf inds'' cbf'' Hvalid Havail Haddm); clear Hxs Haddm => /andP [Hvalid' Hfree'].
      apply/andP;split.
      apply AMQ_add_valid_preserve => //=; apply AMQ_available_capacityW with (n:= m.+1) => //=.
      apply AMQ_add_capacity_decr => //=.
    Qed.

  End Properties.

  Section Query.
    Variable h : AMQHashParams.
    Variable s: AMQStateParams.

    Variable hashes: AMQHash h.
    Variable amq: AMQState s.

    Lemma AMQ_add_multiple_query_preserve  ( amq': AMQState s)  values inds inds' l:
      length values == l -> AMQ_valid amq ->  AMQ_available_capacity h amq l -> AMQ_query_internal amq inds ->
      (P[ AMQ_add_multiple hashes amq values === (inds', amq')] != 0) ->
      @AMQ_query_internal _ h amq' inds.
    Proof.
      move=>/eqP <-; clear l.
      elim: values amq amq' inds inds' => [| x xs Hxs] cbf cbf' inds inds' Hvalid Havail Hquery //=; comp_normalize;
                                            first by move=>/bool_neq0_true; rewrite xpair_eqE =>/andP [ _ /eqP ->].
      exchange_big_outwards 2 => //=; comp_simplify_n 1; comp_possible_decompose.
      move=> cbf'' inds'' Hind Haddm Hhash /bool_neq0_true/eqP ->.
      move: Havail => //=; rewrite -addn1 => Havail.
      move: (@AMQ_add_multiple_properties_preserve h s hashes cbf inds'' xs cbf'' (length xs) 1 (eq_refl (length xs)) Hvalid Havail Haddm) => /andP [Hvalid' Hcap'].
      apply AMQ_add_query_preserve => //=.
      eapply Hxs with (amq:= cbf) (inds':= cbf'') => //=.
        by apply AMQ_available_capacityW with (n:= length xs + 1) => //=; last  rewrite addn1.
    Qed.
    
  End Query.

  Section HashProperties.
    Variable h : AMQHashParams.
    Variable s: AMQStateParams.

    Variable hashes: AMQHash h.
    Variable amq: AMQState s.

    Lemma AMQ_add_multiple_hash_properties_preserve  ( amq': AMQState s)  x xs  inds' l m 
          (Hlen: length xs == l) (Huniq: uniq (x :: xs)) (Hfree: AMQHash_hashstate_available_capacity hashes  ((l+m))) (Hvalid: AMQHash_hashstate_valid hashes)
          (Huns: all (AMQHash_hashstate_unseen hashes) (x :: xs)):
      (P[ AMQ_add_multiple hashes amq xs === (inds', amq')] != 0) ->
      (AMQHash_hashstate_available_capacity inds' (m)) && (AMQHash_hashstate_unseen inds' x) && (AMQHash_hashstate_valid inds').
    Proof.
      move: Hlen Hvalid Huniq Hfree Huns; move=>/eqP <-; clear l.
      elim: xs x m amq amq' hashes inds' => [| y ys Hxs] x m cbf cbf' hshs hshs' Hvalid Huni Hcap Huns //=; comp_normalize.
      - by move=>/bool_neq0_true; rewrite xpair_eqE =>/andP [ /eqP -> _]; move: Hcap Huns => //=; rewrite add0n => ->/andP[->] //=.
      - exchange_big_outwards 2 => //=; comp_simplify_n 1; comp_possible_decompose.
        move=> hsh'' cbf'' y' Haddm Hhash /bool_neq0_true/eqP Hcbf.
        have H1: uniq (y :: ys); first by move: Huni => //= /andP[ _ -> ].
        have H1': uniq (x :: ys);
          first by move: Huni => //= /andP[ ]; rewrite in_cons Bool.negb_orb => /andP[ _ ->] /andP[ _ ->].
        have H2: AMQHash_hashstate_available_capacity hshs (length ys + m.+1);
          first by move: Hcap => //=; rewrite addSn -addnS.
        have H3: all (AMQHash_hashstate_unseen hshs) (y :: ys);
          first by move: Huns => //=/andP[ _ ->].
        have H3': all (AMQHash_hashstate_unseen hshs) (x :: ys);
          first by move: Huns => //=/andP[ -> /andP [ _ ->]  ].
        move: (@Hxs y m.+1 cbf cbf'' hshs hsh'' Hvalid H1 H2 H3 Haddm) => /andP [/andP [Hcap' Huns'] Hvalid'].
        move: (@Hxs x m.+1 cbf cbf'' hshs hsh'' Hvalid H1' H2 H3' Haddm) => /andP [/andP [_ Hunsx'] _].
        case Heq: (hshs' != AMQHash_hashstate_put hsh'' y y').
      - by move: (AMQHash_hash_unseen_insert_neqE Huns' Heq) Hhash => -> //= /eqP //=.
      - move/Bool.negb_false_iff: Heq => /eqP ->.
        apply /andP; split; first apply/andP; first split => //=.
          by apply  AMQHash_hashstate_available_capacity_decr => //=.
          apply AMQHash_hashstate_unseenE with (hashstate:=hsh'') (key' := y) (value':=y') => //=.
            by move: Huni => //=/andP[]; rewrite in_cons Bool.negb_orb => /andP[].
            apply AMQHash_hashstate_add_valid_preserve => //=.
            apply AMQHash_hashstate_available_capacityW with (n:=m.+1) => //=.
    Qed.
  End HashProperties.

  Section HashProperties.
    Variable h : AMQHashParams.
    Variable s: AMQStateParams.

    Variable hashes: AMQHash h.
    Variable amq: AMQState s.


    Lemma AMQ_add_multiple_hash_contains_preserve  ( amq': AMQState s)  x ind xs  inds' l 
          (Hlen: length xs == l) (Huniq: uniq (x :: xs))
          (Hfree: AMQHash_hashstate_available_capacity hashes  l)
          (Hvalid: AMQHash_hashstate_valid hashes)
          (Huns: all (AMQHash_hashstate_unseen hashes) xs)
          (Hseen:  AMQHash_hashstate_contains hashes x ind):
      (P[ AMQ_add_multiple hashes amq xs === (inds', amq')] != 0) ->
      (AMQHash_hashstate_contains inds' x ind).
    Proof.
      move: Hlen Hvalid Huniq Hfree Huns Hseen; move=>/eqP <-; clear l.
      elim: xs x amq amq' hashes inds' => [| y ys Hxs] x  cbf cbf' hshs hshs' Hvalid Huni Hcap Huns Hcont //=; comp_normalize.
      - by move=>/bool_neq0_true; rewrite xpair_eqE =>/andP [ /eqP -> _]; move: Hcap Hcont => //=; rewrite add0n => ->/andP[->] //=.
      - exchange_big_outwards 2 => //=; comp_simplify_n 1; comp_possible_decompose.
        move=> hsh'' cbf'' y' Haddm Hhash /bool_neq0_true/eqP Hcbf.
        have H1: uniq (y :: ys); first by move: Huni => //= /andP[ _ -> ].
        have H1': uniq (x :: ys);
          first by move: Huni => //= /andP[ ]; rewrite in_cons Bool.negb_orb => /andP[ _ ->] /andP[ _ ->].

        have H2: (AMQHash_hashstate_available_capacity hshs (length ys)). {
            by move: Hcap => //=; apply AMQHash_hashstate_available_capacityW.          
        }

        have H3: (all (AMQHash_hashstate_unseen hshs) ys). {
            by move: Huns => //= /andP[].
        }
        move: Hhash (@Hxs x cbf cbf'' hshs hsh'' Hvalid H1' H2 H3 Hcont  Haddm).
        have Huniys: (uniq (y :: ys)); first by move: Huni => //=.
        move: Hcap => //= Hcap.
        move:(@AMQ_add_multiple_hash_properties_preserve h s hshs cbf cbf''  y ys hsh'' (length ys) 1 (eq_refl (length ys)) Huniys);
          rewrite addn1 =>/(_ Hcap Hvalid Huns Haddm) => /andP[/andP[Hcap' Hunsy] Hvalidhsh'].
        case Hneq: (hshs' != AMQHash_hashstate_put hsh'' y y').
        {
          - move: Huns => //=/andP[Hyun Huns].
              by move: (AMQHash_hash_unseen_insert_neqE Hunsy  Hneq) -> => /eqP //=.
        }
        {
          - move/Bool.negb_true_iff: Hneq; rewrite Bool.negb_involutive => /eqP -> Hn0 Hcontains.  
            apply AMQHash_hashstate_add_contains_preserve => //=.
              by move: Huni => //= /andP []; rewrite in_cons Bool.negb_orb => /andP[].
        }        
    Qed.

  End HashProperties.

  Section FalseNegatives.
    Variable h : AMQHashParams.
    Variable s: AMQStateParams.

    Theorem AMQ_no_false_negatives (hashes: AmqHash.AMQHash h)  (amq: AMQState s) l x xs:
      uniq (x :: xs) -> length xs == l ->
      AMQ_valid amq -> AMQ_available_capacity h amq l.+1 ->

      AmqHash.AMQHash_hashstate_valid hashes ->
      AmqHash.AMQHash_hashstate_available_capacity hashes l.+1 ->

      all (AmqHash.AMQHash_hashstate_unseen hashes) (x::xs) ->
      (d[ res1 <-$ AMQ_add amq hashes x;
            let '(hsh1, amq1) := res1 in
            res2 <-$ AMQ_add_multiple hsh1 amq1 xs;
              let '(hsh2, amq2) := res2 in
              res3 <-$ AMQ_query amq2 hsh2 x;
                ret (snd res3) ] true) = (1 %R).
    Proof.
      move=> Huniq Hlen Hamqvalid Hamqavail Hvalid Havail Hall.
      comp_normalize; comp_simplify_n 2.
      exchange_big_outwards 5 => //=; comp_simplify_n 1.
      exchange_big_outwards 4 => //=; comp_simplify_n 1.
      have ->: ((index_enum (AMQHash h))) = (index_enum [finType of AMQHash h]); first by clear;  rewrite index_enum_simpl //=.
      move: Hall => //=/andP[Hallx Hall].
      exchange_big_outwards 2 => //=; exchange_big_inwards ltac:(rewrite AmqHashProperties.AMQHash_hash_unseen_simplE //= mulRA [(AmqHash.AMQHash_probability h) *R* _]mulRC -!mulRA).

      under eq_bigr => hshs' _. {
        under eq_bigr => amq' _; first under eq_bigr => ind _; first under eq_bigr => hshs'' _;
                                                                                        first under eq_rsum_ne0  => ind' Hn0.

        have Hvalidamqin: (AMQ_valid (AMQ_add_internal amq ind)). {
          apply AMQ_add_valid_preserve=>//=.          
            by apply AMQ_available_capacityW with (n:=l.+1)=>//=.
        }
        have Hvalidin: (AmqHash.AMQHash_hashstate_valid (AmqHash.AMQHash_hashstate_put hashes x ind)).
        {
          apply AmqHash.AMQHash_hashstate_add_valid_preserve => //=.
            by apply AmqHash.AMQHash_hashstate_available_capacityW with (n:=l.+1)=>//=.
        }
        have Havailamqin: (AMQ_available_capacity h (AMQ_add_internal amq ind) l); first
          by apply AMQ_add_capacity_decr => //=.

        have Hqueryamqin: (AMQ_query_internal (AMQ_add_internal amq ind) ind). {
          apply AMQ_add_query_base => //=.
            by apply AMQ_available_capacityW with (n:=l.+1)=>//=.
        }

        have Hin: (AMQHash_hashstate_contains hshs' x ind). {
          eapply (@AMQ_add_multiple_hash_contains_preserve)
            with (hashes:=(AmqHash.AMQHash_hashstate_put hashes x ind))
                 (amq:=(AMQ_add_internal amq ind))
                 (amq':=amq')
                 (xs:=xs)
          => //=.
          {
            - apply AMQHash_hashstate_available_capacity_decr => //=.
                by move/eqP: Hlen Havail => ->.
          }
          {
            apply/allP => v Hv.
            apply AmqHash.AMQHash_hashstate_unseenE with
                (key':=x) (value':=ind) (hashstate:=hashes) => //=.
              by move: Huniq => //=/andP[/memPn Hvv _]; move: (Hvv v Hv).
                by move/allP: Hall => /(_ v Hv).
          }
          apply AmqHash.AMQHash_hashstate_add_contains_base => //=.
            by apply AmqHash.AMQHash_hashstate_available_capacityW with (n:=l.+1).
        }
        rewrite (@AmqHash.AMQHash_hash_seen_insertE _ _ _ _ _ _ Hin) => //=.
        rewrite mulRA [_ *R* (_ && _)]mulRC -!mulRA.

        rewrite -RIneq.INR_IZR_INZ boolR_distr.
          by over. by over. by over. by over. by over.
      }
      comp_normalize.
      under_all ltac:(rewrite mulRC -!mulRA ).
      under eq_bigr => i _. {
        under eq_bigr => i0 _ ; first under eq_bigr => i1 _.
        rewrite exchange_big => //=; under eq_bigr => i3 _.
        rewrite -(@rsum_pred_demote [finType of AmqHash.AMQHash h]) big_pred1_eq; over => //=.
        rewrite index_enum_simpl //=.
        rewrite -(@rsum_pred_demote [finType of AmqHash.AMQHashValue h]) big_pred1_eq.
          by over. by over. by over.
      }
      under_all ltac:(rewrite mulRC [(_ %R) *R* _]mulRC -!mulRA).
      under eq_bigr => hshs' _. { 
        under eq_bigr => amq' _; first under eq_rsum_ne0 => ind Hn0.
        have Hvalidamqin: (AMQ_valid (AMQ_add_internal amq ind)). {
          apply AMQ_add_valid_preserve=>//=.          
            by apply AMQ_available_capacityW with (n:=l.+1)=>//=.
        }
        have Hvalidin: (AmqHash.AMQHash_hashstate_valid (AmqHash.AMQHash_hashstate_put hashes x ind)).
        {
          apply AmqHash.AMQHash_hashstate_add_valid_preserve => //=.
            by apply AmqHash.AMQHash_hashstate_available_capacityW with (n:=l.+1)=>//=.
        }
        have Havailamqin: (AMQ_available_capacity h (AMQ_add_internal amq ind) l); first
          by apply AMQ_add_capacity_decr => //=.

        have Hqueryamqin: (AMQ_query_internal (AMQ_add_internal amq ind) ind). {
          apply AMQ_add_query_base => //=.
            by apply AMQ_available_capacityW with (n:=l.+1)=>//=.
        }

        have Hqueryint: (AMQ_query_internal amq' ind). {

          apply AMQ_add_multiple_query_preserve
            with (hashes:=(AmqHash.AMQHash_hashstate_put hashes x ind))
                 (values:= xs)
                 (amq:=(AMQ_add_internal amq ind))
                 (amq':=amq')
                 (inds':=hshs')
                 (l:=l)
          => //=.
        }
        rewrite Hqueryint eq_refl //= mul1R.

          by over.
            by over.
              by over.
      }
      move=>//=.

      exchange_big_outwards 2 => //=.
      under eq_bigr do under eq_bigr do rewrite -big_distrl //=.
      under eq_bigr do rewrite -big_distrl //=.
      under eq_bigr do rewrite mulRC.
      under eq_bigr => i Hi.
      rewrite -index_enum_simpl.
      suff ->:  \sum_(i0 in  AmqHash.AMQHash h)
           \sum_(i1 in   AMQState s)
           P[ AMQ_add_multiple
                (AmqHash.AMQHash_hashstate_put hashes x i)
                (AMQ_add_internal amq i) xs === 
                (i0, i1)] = 1;
        last first; last rewrite mulR1; last by over.
        by rewrite -rsum_split //=; apply FDist.f1.
        move=> //=.
          by rewrite AmqHash.AMQHash_hash_prob_valid.
    Qed.
  End FalseNegatives.

  Section Normalize.
    Variable h : AMQHashParams.
    Variable s: AMQStateParams.

    Theorem AMQ_add_multiple_normalize (hashes: AmqHash.AMQHash h)  (amq: AMQState s) l xs f:
      uniq (xs) -> length xs == l ->
      AMQ_valid amq -> AMQ_available_capacity h amq l ->

      AmqHash.AMQHash_hashstate_valid hashes ->
      AmqHash.AMQHash_hashstate_available_capacity hashes l ->

      all (AmqHash.AMQHash_hashstate_unseen hashes) (xs) ->

      \sum_(hashes' in [finType of AMQHash h])
       \sum_(amq' in [finType of AMQState s])
       (P[ AMQ_add_multiple hashes amq xs === (hashes',amq') ] *R* (f hashes' amq'))
      =
      \sum_(hash_result in [finType of l.-tuple (AMQHashValue h)])
       ((AMQHash_probability h ^R^ l) *R*
        (f
           (foldr (fun (pair: AMQHashKey * AMQHashValue h)  hashes' =>
                     let (x,hash') := pair in
                     AMQHash_hashstate_put hashes' x hash') hashes (zip xs hash_result))
           (foldr (fun hash' amq' =>
                     AMQ_add_internal amq' hash') amq hash_result)
           )).
      Proof.
        elim: l xs hashes amq  f => [| l IHl ] [| x xs]  hashes amq f
                                               Huniq Hlen Hvalid Hcap Hhashvalid Hhashcap Huns //=.
        - {
            rewrite rsum_empty //=; comp_normalize;
            under_all ltac:(rewrite !xpair_eqE !boolR_distr -!mulRA).
            rewrite index_enum_simpl;
              exchange_big_inwards ltac:(rewrite -index_enum_simpl -rsum_pred_demote big_pred1_eq).
              by rewrite -index_enum_simpl -rsum_pred_demote big_pred1_eq //=.
          }
        - {
            comp_normalize.
            under_all ltac:(rewrite mulRC mulRA [_ *R* (_ %R)]mulRC ).
            under_all ltac:(rewrite !xpair_eqE !boolR_distr -!mulRA).
            exchange_big_inwards ltac:(rewrite -index_enum_simpl -rsum_pred_demote big_pred1_eq).
            exchange_big_inwards ltac:(rewrite -index_enum_simpl -rsum_pred_demote big_pred1_eq).
            under eq_bigr => i _. {
              under eq_bigr => i0 _.

              rewrite exchange_big //=; under eq_bigr => i2 _ do rewrite -rsum_Rmul_distr_l.
              under eq_rsum_ne0 => i2 Haddm.
               move: (Haddm) => /AMQ_add_multiple_hash_properties_preserve H1.
               move: (@H1 x l 1 Hlen Huniq); rewrite !addn1; clear H1 => H1.
               move: (H1 Hhashcap Hhashvalid Huns); clear H1 => /andP [/andP [Hcap' Huns'] Hvalid'].
               rewrite index_enum_simpl AMQHash_hash_unseen_simplE//=.

               by over. by over. by over.
            }
            exchange_big_outwards 2 => //=.
            under_all ltac:(rewrite mulRA [_ *R* AMQHash_probability h]mulRC -!mulRA).
            under eq_bigr do under eq_bigr do rewrite -rsum_Rmul_distr_l.
            under eq_bigr do rewrite -rsum_Rmul_distr_l.
            rewrite -rsum_Rmul_distr_l.

            under eq_bigr => hash' _. {
              rewrite index_enum_simpl.
              under eq_bigr do rewrite index_enum_simpl.
              rewrite (IHl) //=; first by over.
                by move: Huniq => //=/andP[].
                  by apply AMQ_available_capacityW with (n:=l.+1).
                    by apply AMQHash_hashstate_available_capacityW with (n:=l.+1).
                      by move: Huns => //=/andP[].
            }

            move=> //=.
            under eq_bigr do rewrite -rsum_Rmul_distr_l;  rewrite -rsum_Rmul_distr_l.
            rewrite -rsum_Rmul_distr_l mulRA; apply f_equal.
            by rewrite rsum_tuple_split rsum_split //=.
          }
      Qed.

  End Normalize.

  (** false positive proofs often use the same initial simplification step, which can be
      proven in general as follows: *)
  Section FalsePositiveSimplify.
    Variable h : AMQHashParams.
    Variable s: AMQStateParams.

    Lemma AMQ_false_positives_simplify: forall (hashes: AMQHash h)  l value (values: seq _),
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
          ] true = 
        \sum_(i in [finType of AMQState s])
         \sum_(i0 in [finType of AMQHash h])
         \sum_(i1 in [finType of AMQHashValue h])
           (P[ AMQ_add_multiple (AMQHash_hashstate_put hashes value i1) (AMQ_new s) values ===
            (i0, i)] *R* (AMQHash_probability h *R* (AMQ_query_internal i i1 %R))).
    Proof.
      move=> hashes l value values Hlen Hhashvalid Hhashcap Hcap Huns Huniq.
      comp_normalize.
      under_all ltac:(rewrite !xpair_eqE !boolR_distr).
      comp_simplify_n 2.
      exchange_big_outwards 4 => //=; comp_simplify_n 1.
      exchange_big_outwards 4 => //=; comp_simplify_n 1.

      move: (Huns) => //= /andP [Hunv Hunvs].
      exchange_big_outwards 2 => //=.
      exchange_big_inwards ltac:(rewrite index_enum_simpl AMQHash_hash_unseen_simplE; last by []).
      under_all ltac:(rewrite mulRA [AMQHash_probability h *R* _]mulRC -!mulRA).

      under eq_bigr => i _. {
        under eq_bigr => i0 _; first under eq_bigr => i1 _; first under eq_bigr => i2 _; first under eq_rsum_ne0 => i3 Haddm.
        move: (Haddm) => /AMQ_add_multiple_hash_contains_preserve H1.
        move: (@H1 value i1 l Hlen Huniq); clear H1 => H1.
        have H5:   AMQHash_hashstate_available_capacity hashes 1; first
          by apply AMQHash_hashstate_available_capacityW with (n:=l.+1) => //=.
        have H2: AMQHash_hashstate_available_capacity (AMQHash_hashstate_put hashes value i1) l; first
          by apply AMQHash_hashstate_available_capacity_decr.
        have H3: AMQHash_hashstate_valid (AMQHash_hashstate_put hashes value i1); first
          by apply AMQHash_hashstate_add_valid_preserve.
        have H4: all (AMQHash_hashstate_unseen (AMQHash_hashstate_put hashes value i1)) (values). {
          apply /allP => v Hv; move/allP: Hunvs => /(_ v Hv) H'.
          apply AMQHash_hashstate_unseenE with (hashstate:=hashes)
                                               (key':=value)
                                               (value':=i1) => //=.
            by move: Huniq => //=/andP[/memPn H'' _]; apply H''.
        }
        have H6: AMQHash_hashstate_contains (AMQHash_hashstate_put hashes value i1) value i1; first
           by apply AMQHash_hashstate_add_contains_base => //=.
        move: (H1 H2 H3 H4 H6) => Hcont.
        rewrite (@AMQHash_hash_seen_insertE _ _ _ _ i1) //=.
        rewrite -RIneq.INR_IZR_INZ boolR_distr mulRA [AMQHash_probability h *R* _]mulRC -mulRA.
        by over. by over. by over. by over. by over.
      }
      move=> //=.
      comp_simplify_n 1 => //=.
      rewrite exchange_big //=; comp_simplify_n 1 => //=.
      under_all ltac:(rewrite eq_sym eqb_id).

      rewrite index_enum_simpl;
        under eq_bigr do (rewrite index_enum_simpl; under eq_bigr do rewrite index_enum_simpl).

      exchange_big_outwards 2 => //=.
    Qed.

    Lemma AMQ_false_positives_simplify_normalize: forall (hashes: AMQHash h)  l value (values: seq _),
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
          ] true =
        \sum_(i1 in [finType of AMQHashValue h])
         (AMQHash_probability h *R*
         \sum_(i in [finType of l.-tuple (AMQHashValue h)])
         ((AMQHash_probability h ^R^ l) *R*
         (AMQ_query_internal
            (foldr (fun hash' : AMQHashValue h => (AMQ_add_internal (h:=h))^~ hash') (AMQ_new s) i) i1
          %R))).
      Proof.
      move=> hashes l value values Hlen Hhashvalid Hhashcap Hcap Huns Huniq.
      rewrite (@AMQ_false_positives_simplify _ l) //=.
      rewrite exchange_big//=; exchange_big_outwards 2 => //=.
      under eq_bigr => i1 _. {
        rewrite  (@AMQ_add_multiple_normalize h s  (AMQHash_hashstate_put hashes value i1) (AMQ_new s) l values) //=.

        under eq_bigr do rewrite mulRA.
        have H: ((AMQHash_probability h ^R^ l) *R* AMQHash_probability h) = 
              ((AMQHash_probability h ^R^ l.+1)); first by rewrite//= mulRC.
        under eq_bigr do rewrite H.
        have H5:   AMQHash_hashstate_available_capacity hashes 1; first
          by apply AMQHash_hashstate_available_capacityW with (n:=l.+1) => //=.

        by over.
        by move: Huniq => //=/andP[].
        by apply AMQ_new_validT.
        by apply AMQ_available_capacityW with (n:=l.+1); first  apply AMQ_new_validT.
        by apply AMQHash_hashstate_add_valid_preserve;
          try apply AMQHash_hashstate_available_capacityW with (n:=l.+1) => //=.
        by apply AMQHash_hashstate_available_capacity_decr.
        move: Huns => //=/andP[Hunv Hunvs].
        apply /allP => v Hv; move/allP: Hunvs => /(_ v Hv) H'.
          apply AMQHash_hashstate_unseenE with (hashstate:=hashes)
                                               (key':=value)
                                               (value':=i1) => //=.
           by move: Huniq => //=/andP[/memPn H'' _]; apply H''.
      }
      by under_all ltac:(rewrite -mulRA); under eq_bigr do rewrite -rsum_Rmul_distr_l.
    Qed.
  End FalsePositiveSimplify.

End AMQOperations.

Module Type AMQProperties (AmqHash: AMQHASH) (AbstractAMQ: AMQ AmqHash) .
  Module AmqOperations := AMQOperations (AmqHash)  (AbstractAMQ).
  Export AmqOperations.

  Parameter AMQ_false_positive_probability:  AMQHashParams -> AMQStateParams -> nat -> Rdefinitions.R.

  Section Properties.
    Variable h : AMQHashParams.
    Variable s: AMQStateParams.

    Variable hashes: AMQHash h.

    Section FalseNegatives.

      Variable amq: AMQState s.

      Axiom AMQ_no_false_negatives:
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
    End FalseNegatives.

    Axiom AMQ_false_positives_rate: forall  l value (values: seq _),
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

  End Properties.

End AMQProperties.
