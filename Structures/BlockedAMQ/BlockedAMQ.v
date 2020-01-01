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
     Require Import InvMisc  seq_ext seq_subset rsum_ext stirling tactics.

From ProbHash.Computation
     Require Import Comp Notationv1.

From ProbHash.Core
     Require Import Hash HashVec FixedList FixedMap.

From ProbHash.BloomFilter
     Require Import BloomFilter_Definitions.

From ProbHash.CountingBloomFilter
     Require Import CountingBloomFilter_Definitions.

From ProbHash.QuotientFilter
     Require Import QuotientFilter_Definitions.



Lemma index_enum_simpl y: ((index_enum y)) = (index_enum [finType of y]).
Proof.
    by rewrite /index_enum //= /[finType of _] //=; case: y => //=.
Qed.



Module Type AMQHASH.
  Parameter AMQHashKey : finType.
  Parameter AMQHashParams: Type.
  Parameter AMQHashValue: AMQHashParams -> finType.
  Parameter AMQHash : AMQHashParams -> finType.

  

  Section AMQHash.
    Variable p: AMQHashParams. 
    Parameter AMQHash_probability:  AMQHashParams -> Rdefinitions.R.

    Axiom AMQHash_hash_prob_valid:
      \sum_(v in  AMQHashValue p) (AMQHash_probability p) = 1.


    Parameter AMQHash_hashstate_put : AMQHash p -> AMQHashKey -> AMQHashValue p -> AMQHash p.

    (* boolean properties of hash states*)
    Parameter AMQHash_hashstate_available_capacity : AMQHash p -> nat -> bool.
    Parameter AMQHash_hashstate_valid: AMQHash p -> bool.
    Parameter AMQHash_hashstate_contains: AMQHash p -> AMQHashKey -> AMQHashValue p -> bool.
    Parameter AMQHash_hashstate_unseen: AMQHash p -> AMQHashKey -> bool.

    (* probabilistic hash operation*)
    Parameter AMQHash_hash: AMQHash p -> AMQHashKey -> Comp [finType of (AMQHash p * AMQHashValue p)].

    (* properties of deterministic hash state operations *)
    Section DeterministicOperations.

      Variable hashstate: AMQHash p.


      Axiom AMQHash_hashstate_available_capacityW: forall n m, m <= n ->
                                                               AMQHash_hashstate_valid hashstate ->
                                                               AMQHash_hashstate_available_capacity hashstate n ->
                                                               AMQHash_hashstate_available_capacity hashstate m.

      Axiom AMQHash_hashstate_available_capacity_decr: forall l key value,
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate l.+1 ->
          AMQHash_hashstate_available_capacity (AMQHash_hashstate_put hashstate key value) l.
      
      
      Axiom  AMQHash_hashstate_add_contains_preserve: forall (key key': AMQHashKey) (value value': AMQHashValue p),
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 -> 
          key != key' -> AMQHash_hashstate_contains hashstate key value ->
          AMQHash_hashstate_contains (AMQHash_hashstate_put  hashstate key' value') key value.

      Axiom  AMQHash_hashstate_add_contains_base: forall (key: AMQHashKey) (value: AMQHashValue p),
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 ->
          AMQHash_hashstate_contains (AMQHash_hashstate_put  hashstate key value) key value.

      Axiom AMQHash_hashstate_add_valid_preserve: forall (key: AMQHashKey) (value: AMQHashValue p), 
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 -> 
          AMQHash_hashstate_valid (AMQHash_hashstate_put  hashstate key value).

      Axiom AMQHash_hashstate_unseenE: forall (hashstate': AMQHash p) (key key': AMQHashKey) (value': AMQHashValue p),
          key != key' ->
          AMQHash_hashstate_unseen hashstate key ->
          hashstate' = AMQHash_hashstate_put hashstate key' value' ->
          AMQHash_hashstate_unseen hashstate' key.

    End DeterministicOperations.

    
    Axiom  AMQHash_hash_unseen_insert_eqE: forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value: AMQHashValue p),
        AMQHash_hashstate_unseen hashstate key -> hashstate' = AMQHash_hashstate_put hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value) = AMQHash_probability p.

    Axiom  AMQHash_hash_unseen_insert_neqE: forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value: AMQHashValue p),
        AMQHash_hashstate_unseen hashstate key -> hashstate' != AMQHash_hashstate_put hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value) = 0.

    Axiom AMQHash_hash_seen_insertE: forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value value': AMQHashValue p),
        AMQHash_hashstate_contains hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value') = ((hashstate' == hashstate) && (value' == value)).
    
  End AMQHash.    
End AMQHASH.

Module AMQHashProperties (AMQHash: AMQHASH).

  Import AMQHash.
  Section Properties.
    Variable p: AMQHashParams. 
    
    Lemma AMQHash_hash_unseen_simplE (hashstate: AMQHash p) key value f :
      AMQHash_hashstate_unseen hashstate key ->
      (\sum_(hashstate' in [finType of AMQHash p])
        (d[ AMQHash_hash hashstate key ] (hashstate', value) *R* (f hashstate'))) =
      ((AMQHash_probability p) *R*
       (f (AMQHash_hashstate_put hashstate key value))).
    Proof.
      move=> Hall.
      rewrite (bigID (fun hashstate' => hashstate' == (AMQHash_hashstate_put hashstate key value))) //=.
      rewrite (@big_pred1_eq Rdefinitions.R _ _
                             [finType of AMQHash p]
                             (AMQHash_hashstate_put hashstate key value))//=.
      under eq_bigr => i Hneq do rewrite AMQHash_hash_unseen_insert_neqE //= ?mul0R.
      rewrite AMQHash_hash_unseen_insert_eqE //=.
      rewrite (@bigsum_card_constE [finType of AMQHash p] ) mulR0 addR0 //=.
    Qed.

  End Properties.
End AMQHashProperties.


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

Module AMQOperations (AmqHash: AMQHASH) (Amq: AMQ AmqHash) .

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



Module Type AMQMAP (AmqHash: AMQHASH) (A: AMQ AmqHash) (B: AMQ AmqHash).

  Parameter AMQ_param_map: A.AMQStateParams -> B.AMQStateParams.
  Parameter AMQ_state_map:  forall p: A.AMQStateParams, A.AMQState p -> B.AMQState (AMQ_param_map p).

  Section Map.

    Variable p: A.AMQStateParams.
    Variable h: AmqHash.AMQHashParams.

    Axiom AMQ_map_validE: forall (a: A.AMQState p), A.AMQ_valid a ->
                                                    B.AMQ_valid (AMQ_state_map a).
    Axiom AMQ_map_capacityE: forall (a: A.AMQState p) l, A.AMQ_available_capacity h a l ->
                                                         B.AMQ_available_capacity h (AMQ_state_map a) l.

    Axiom AMQ_map_add_internalE: forall (a: A.AMQState p) val, A.AMQ_valid a -> A.AMQ_available_capacity h a 1 ->
                                                               B.AMQ_add_internal (AMQ_state_map a) val = AMQ_state_map (@A.AMQ_add_internal _ h   a val).

    Axiom AMQ_map_query_internalE: forall (a: A.AMQState p) val, A.AMQ_valid a -> A.AMQ_available_capacity h a 1 ->
                                                                 B.AMQ_query_internal (AMQ_state_map a) val = @A.AMQ_query_internal _ h a val.

    Axiom AMQ_map_newE: forall (a: A.AMQState p), 
        B.AMQ_new (AMQ_param_map p)  = AMQ_state_map (A.AMQ_new p).

  End Map.
End AMQMAP.

Module AMQPropertyMap (AmqHash: AMQHASH) (A: AMQ AmqHash) (B: AMQ AmqHash) (Map: AMQMAP AmqHash A B) (Properties: AMQProperties AmqHash B) <:  AMQProperties AmqHash A.
  Module AmqOperations := AMQOperations (AmqHash) (A).
  Module AmqHashProperties := AMQHashProperties AmqHash.


  Section PropertyMap.
    Variable h: AmqHash.AMQHashParams.
    Variable s: A.AMQStateParams.

    Definition AMQ_false_positive_probability  n :=
      Properties.AMQ_false_positive_probability h (Map.AMQ_param_map s) n.

    Lemma AMQ_map_add_multipleE cbf hashes values f
          (Hvalid: A.AMQ_valid cbf) (Hcap: A.AMQ_available_capacity h cbf (length values)) :
      \sum_(hshs in [finType of AmqHash.AMQHash h]) \sum_(cbf' in [finType of A.AMQState s])
       ((d[ AmqOperations.AMQ_add_multiple hashes cbf values]) (hshs,cbf') *R*
        (f hshs (Map.AMQ_state_map cbf'))) =
      \sum_(hshs in [finType of AmqHash.AMQHash h]) \sum_(bf' in [finType of B.AMQState (Map.AMQ_param_map s)])
       ((d[ Properties.AmqOperations.AMQ_add_multiple hashes (Map.AMQ_state_map cbf) values]) (hshs, bf') *R*
        (f hshs bf')).
    Proof.
      under eq_bigr => hshs' _ do
                             rewrite (@partition_big _ _ _ [finType of (A.AMQState s)] [finType of (B.AMQState _)] _  (@Map.AMQ_state_map s) predT) => //=.
      under eq_bigr => hshs' _ do
                             under eq_bigr => bf _ do
                                                 under eq_bigr => i /eqP Hbi do rewrite Hbi mulRC.
      rewrite exchange_big  [\sum_(a in [finType of AmqHash.AMQHash h]) _]exchange_big; apply eq_bigr => bf _.
      elim: values Hcap  bf f => [|val values IHval] Hcap bf f.
      - {
          apply eq_bigr => hshs' _.
          rewrite (@rsum_pred_demote [finType of A.AMQState s]); under eq_bigr => ? ? do rewrite FDist1.dE xpair_eqE mulRC [_ *R* (_ && _ %R)]mulRC andbC boolR_distr -!mulRA.
          rewrite -rsum_pred_demote big_pred1_eq FDist1.dE xpair_eqE boolR_distr.
          rewrite -mulRA; apply f_equal.
          rewrite [_ *R* f _ _ ]mulRC; apply f_equal.
          apply f_equal => //=.
            by rewrite -eqE eq_sym.
        }
      - {
          apply Logic.eq_sym => //=.
          under (@eq_bigr _ _ _ [finType of AmqHash.AMQHash h]) => hshs' _.
          {
            move: IHval bf f hshs' => //= IHval bf f hshs'.
            rewrite (@FDistBind.dE [finType of (AmqHash.AMQHash h) * (B.AMQState (Map.AMQ_param_map s))]); rewrite rsum_split.
            rewrite (@exchange_big _ _ _ [finType of AmqHash.AMQHash h] [finType of B.AMQState (Map.AMQ_param_map s)]) => //=.

            under (@eq_bigr _ _ _ [finType of B.AMQState (Map.AMQ_param_map s)]) =>  bf' _. {
              suff <-:
                   \sum_(i in [finType of AmqHash.AMQHash h])
                   \sum_(i0 in [finType of _] | Map.AMQ_state_map i0 == bf')
                   (FDistBind.d (d[ AmqHash.AMQHash_hash i val])
                                (fun b : AmqHash.AMQHash h * AmqHash.AMQHashValue h =>
                                   d[ let (new_hashes, hash_vec) := b in
                                      ret (new_hashes, B.AMQ_add_internal bf' hash_vec)]) 
                                (hshs', bf) *R*
                    P[ AmqOperations.AMQ_add_multiple hashes cbf values === (i, i0)]) =
              \sum_(i in AmqHash.AMQHash h)
               (P[ Properties.AmqOperations.AMQ_add_multiple hashes (Map.AMQ_state_map cbf) values === (i, bf')] *R*
                FDistBind.d (d[ AmqHash.AMQHash_hash i val])
                            (fun b : AmqHash.AMQHash h * AmqHash.AMQHashValue h =>
                               d[ let (new_hashes, hash_vec) := b in
                                  ret (new_hashes, B.AMQ_add_internal bf' hash_vec)])
                            (hshs', bf)); first by over.
              have Hcap': A.AMQ_available_capacity h cbf (length values); first by eapply A.AMQ_available_capacityW with (n:= (length values).+1) => //=.
              move: (@IHval Hcap'
                            bf' (fun (i: [finType of AmqHash.AMQHash h]) (bf': [finType of B.AMQState (Map.AMQ_param_map s)]) =>
                                   FDistBind.d (d[ AmqHash.AMQHash_hash i val])
                                               (fun b : AmqHash.AMQHash h * AmqHash.AMQHashValue h =>
                                                  d[ let (new_hashes, hash_vec) := b in
                                                     ret (new_hashes, B.AMQ_add_internal bf' hash_vec)]) (hshs',bf) )) => //=.
              move=>-> //=.
              have ->: ((index_enum (AmqHash.AMQHash h))) = (index_enum [finType of AmqHash.AMQHash h]); last by apply f_equal => //=.
                by rewrite index_enum_simpl.

            }
            under eq_bigr =>  bf' _. {
              rewrite exchange_big //=.
                by over.
            }
              by over.
          } 
          move=> //=; clear IHval.
          apply eq_bigr => hshs' _.
          apply Logic.eq_sym; under eq_bigr => ? ? do rewrite mulRC.
          rewrite -big_distrl //= mulRC.
          rewrite [_ *R* f _ _]mulRC; apply f_equal.
          under eq_bigr => ? ? do rewrite FDistBind.dE; rewrite exchange_big //= rsum_split //=.
          apply Logic.eq_sym.
          under eq_bigr => bf' _ do (rewrite (@rsum_pred_demote [finType of _]); under eq_bigr => hshs'' _ do rewrite (@rsum_Rmul_distr_l [finType of _])).
          exchange_big_outwards 1 => //=.
          exchange_big_outwards 2 => //=.
          have ->: ((index_enum (AmqHash.AMQHash h))) = (index_enum [finType of AmqHash.AMQHash h]); first by clear;  rewrite index_enum_simpl //=.
          have ->: ((index_enum (A.AMQState s))) = (index_enum [finType of A.AMQState s]); first by clear;  rewrite index_enum_simpl //=.
          apply eq_bigr => inds' _; apply eq_bigr => cbf' _. rewrite -eqE.
          under eq_bigr do rewrite mulRC [_ *R* (d[ _ ]) _]mulRC -mulRA.
          rewrite -rsum_Rmul_distr_l; apply Logic.eq_sym.
          under eq_bigr do rewrite mulRC.
          rewrite -big_distrl  //= mulRC.
          case Hzr0: (P[ AmqOperations.AMQ_add_multiple hashes cbf values === (inds', cbf')] == 0); first by move/eqP: Hzr0 => ->; rewrite !mul0R //=.
          apply f_equal.
          under eq_bigr do rewrite FDistBind.dE; rewrite exchange_big //=; apply Logic.eq_sym.
          under eq_bigr do rewrite FDistBind.dE big_distrl //=; rewrite exchange_big; apply eq_bigr => [[hshs'' inds'']] _.
          under eq_bigr do rewrite [(d[ _ ]) _ *R* _ ]mulRC mulRC mulRA //=; rewrite -big_distrl //= mulRC; apply Logic.eq_sym.
          under eq_bigr do rewrite [(d[ _ ]) _ *R* _ ]mulRC  ; rewrite -big_distrl //= mulRC; apply f_equal.
          under eq_bigr do rewrite FDist1.dE xpair_eqE andbC boolR_distr//=; rewrite -big_distrl //= mulRC.
          apply Logic.eq_sym.
          under eq_bigr do rewrite FDist1.dE xpair_eqE andbC boolR_distr//= mulRA;
            rewrite -big_distrl //= mulRC; apply f_equal.
          apply Logic.eq_sym.
          rewrite (@rsum_pred_demote [finType of _]); under eq_bigr do rewrite mulRC; rewrite -rsum_pred_demote big_pred1_eq //=.
          rewrite -rsum_pred_demote (big_pred1 (Map.AMQ_state_map cbf')).
          move/Bool.negb_true_iff: Hzr0 => Hzr0; move: Hcap => //= Hcap.
          move: (@AmqOperations.AMQ_add_multiple_properties_preserve h s hashes cbf cbf' values inds' (length values) 1 (eq_refl (length values))  Hvalid);
            rewrite addn1 => Hprop; move: (Hprop Hcap Hzr0); clear Hprop => /andP[ Hvalid' Hcap'].
            by rewrite -eqE Map.AMQ_map_add_internalE //=; first rewrite eq_sym //=.
              by move=> //=.
        }
    Qed.

    Theorem AMQ_no_false_negatives (hashes: AmqHash.AMQHash h)  (amq: A.AMQState s) l x xs:
      uniq (x :: xs) -> length xs == l ->
      A.AMQ_valid amq -> A.AMQ_available_capacity h amq l.+1 ->

      AmqHash.AMQHash_hashstate_valid hashes ->
      AmqHash.AMQHash_hashstate_available_capacity hashes l.+1 ->

      all (AmqHash.AMQHash_hashstate_unseen hashes) (x::xs) ->
      (d[ res1 <-$ AmqOperations.AMQ_add amq hashes x;
            let '(hsh1, amq1) := res1 in
            res2 <-$ AmqOperations.AMQ_add_multiple hsh1 amq1 xs;
              let '(hsh2, amq2) := res2 in
              res3 <-$ AmqOperations.AMQ_query amq2 hsh2 x;
                ret (snd res3) ] true) = (1 %R).
    Proof.
        by apply (AmqOperations.AMQ_no_false_negatives).
    Qed.

    Theorem AMQ_false_positives_rate
            (hashes: AmqHash.AMQHash h)  l value (values: seq _):
      length values == l ->
      AmqHash.AMQHash_hashstate_valid hashes ->
      AmqHash.AMQHash_hashstate_available_capacity hashes (l.+1) ->
      A.AMQ_available_capacity h (A.AMQ_new s) l.+1 ->
      all (AmqHash.AMQHash_hashstate_unseen hashes) (value::values) ->
      uniq (value::values) ->
      d[ 
          res1 <-$ AmqOperations.AMQ_query (A.AMQ_new s) hashes value;
            let (hashes1, init_query_res) := res1 in
            res2 <-$ AmqOperations.AMQ_add_multiple hashes1 (A.AMQ_new s) values;
              let (hashes2, amq) := res2 in
              res' <-$ AmqOperations.AMQ_query amq  hashes2 value;
                ret (res'.2)
        ] true = AMQ_false_positive_probability  l.
    Proof.
      (* simplify proof a bit *)
      move=> Hlen Hvalid Havail Hcap Hall Huniq.
      comp_normalize; comp_simplify_n 2.
      exchange_big_outwards 5 => //=; comp_simplify_n 1.
      exchange_big_outwards 4 => //=; comp_simplify_n 1.
      under_all ltac:(rewrite eq_sym eqb_id).
      apply Logic.eq_sym.
      rewrite/AMQ_false_positive_probability.
      rewrite -(@Properties.AMQ_false_positives_rate _ _ hashes l value values) => //=.
      comp_normalize; comp_simplify_n 2.
      exchange_big_outwards 5 => //=; comp_simplify_n 1.
      exchange_big_outwards 4 => //=; comp_simplify_n 1.
      under_all ltac:(rewrite eq_sym eqb_id).
      exchange_big_inwards ltac:(idtac); apply Logic.eq_sym; exchange_big_inwards ltac:(idtac).
      exchange_big_inwards ltac:(idtac); apply Logic.eq_sym; exchange_big_inwards ltac:(idtac).
      exchange_big_inwards ltac:(idtac); apply Logic.eq_sym; exchange_big_inwards ltac:(idtac).
      apply eq_bigr => hshs' _.

      move: Hall => //=/andP[Hunval Hall].
      under eq_bigr do under eq_bigr do under eq_bigr do under eq_bigr do
            rewrite index_enum_simpl AmqHashProperties.AMQHash_hash_unseen_simplE//=.
      apply Logic.eq_sym.
      under eq_bigr do under eq_bigr do under eq_bigr do under eq_bigr do
            rewrite index_enum_simpl AmqHashProperties.AMQHash_hash_unseen_simplE//=.
      under_all ltac:(rewrite [(AmqHash.AMQHash_probability _ *R* _)]mulRC -!mulRA).
      under eq_bigr => inds'' _. {
        under eq_bigr => ind' _; first under eq_bigr
        => hsh'' _; first under eq_rsum_ne0 => amq' Hamq.
        have H1: B.AMQ_available_capacity h (B.AMQ_new (Map.AMQ_param_map s)) (l + 1). {
          rewrite Map.AMQ_map_newE //=.
            by apply Map.AMQ_map_capacityE; rewrite addn1.
            exact (A.AMQ_new s).
        }
        move: (@Properties.AmqOperations.AMQ_add_multiple_properties_preserve
                 h (Map.AMQ_param_map s) (AmqHash.AMQHash_hashstate_put hashes value hshs')
                 (B.AMQ_new (Map.AMQ_param_map s)) amq' values hsh'' l 1
                 Hlen (B.AMQ_new_validT _) H1 Hamq
              ) => /andP[Hvalid' Hcap']; clear H1.

        have H1: AmqHash.AMQHash_hashstate_available_capacity
                   (AmqHash.AMQHash_hashstate_put hashes value hshs') l;first
          by apply AmqHash.AMQHash_hashstate_available_capacity_decr =>//=.
        have H2: AmqHash.AMQHash_hashstate_valid
                   (AmqHash.AMQHash_hashstate_put hashes value hshs'). {
          apply AmqHash.AMQHash_hashstate_add_valid_preserve => //=.
            by apply AmqHash.AMQHash_hashstate_available_capacityW with (n:=l.+1) => //=.
        }
        have H3:
                                                                         all
                                                                           (AmqHash.AMQHash_hashstate_unseen
                                                                              (AmqHash.AMQHash_hashstate_put hashes value hshs')) values. {
          move: Huniq Hall => //=/andP[/memPn Hneq Huniq] => /allP Huns.
          apply/allP => v Hv; move: (Huns v Hv) (Hneq v Hv) => Hunsv Hneqv.
            by apply AmqHash.AMQHash_hashstate_unseenE
              with (hashstate:= hashes)
                   (key':= value)
                   (value':=hshs') => //=.
        }
        have H4:
                                                                                                                                            AmqHash.AMQHash_hashstate_contains
                                                                                                                                              (AmqHash.AMQHash_hashstate_put hashes value hshs') value hshs'. {
          apply AmqHash.AMQHash_hashstate_add_contains_base => //=.
            by apply AmqHash.AMQHash_hashstate_available_capacityW with (n:=l.+1) => //=.
        }
        move: (@Properties.AmqOperations.AMQ_add_multiple_hash_contains_preserve
                 h (Map.AMQ_param_map s) (AmqHash.AMQHash_hashstate_put hashes value hshs')
                 (B.AMQ_new (Map.AMQ_param_map s)) amq' value hshs' values hsh'' l
                 Hlen Huniq
                 H1 H2 H3 H4 Hamq
              ) => Hcont'.
        rewrite (@AmqHash.AMQHash_hash_seen_insertE _ _ _ _ hshs') //=.
          by over. by over. by over. by over.
      }
      under_all ltac:(rewrite  -RIneq.INR_IZR_INZ boolR_distr).
      comp_simplify_n 2.
      apply Logic.eq_sym.
      under_all ltac:(rewrite [(AmqHash.AMQHash_probability _ *R* _)]mulRC -!mulRA).
      under eq_bigr => inds'' _. {
        under eq_bigr => ind' _; first under eq_bigr
        => hsh'' _; first under eq_rsum_ne0 => amq' Hamq.
        have H1: A.AMQ_available_capacity h (A.AMQ_new s) (l + 1);first by rewrite addn1.
        move: (@AmqOperations.AMQ_add_multiple_properties_preserve
                 h s (AmqHash.AMQHash_hashstate_put hashes value hshs')
                 (A.AMQ_new s) amq' values hsh'' l 1
                 Hlen (A.AMQ_new_validT _) H1 Hamq
              ) => /andP[Hvalid' Hcap']; clear H1.
        have H1: AmqHash.AMQHash_hashstate_available_capacity
                   (AmqHash.AMQHash_hashstate_put hashes value hshs') l;first
          by apply AmqHash.AMQHash_hashstate_available_capacity_decr =>//=.
        have H2: AmqHash.AMQHash_hashstate_valid
                   (AmqHash.AMQHash_hashstate_put hashes value hshs'). {
          apply AmqHash.AMQHash_hashstate_add_valid_preserve => //=.
            by apply AmqHash.AMQHash_hashstate_available_capacityW with (n:=l.+1) => //=.
        }
        have H3:
                                                                         all
                                                                           (AmqHash.AMQHash_hashstate_unseen
                                                                              (AmqHash.AMQHash_hashstate_put hashes value hshs')) values. {
          move: Huniq Hall => //=/andP[/memPn Hneq Huniq] => /allP Huns.
          apply/allP => v Hv; move: (Huns v Hv) (Hneq v Hv) => Hunsv Hneqv.
            by apply AmqHash.AMQHash_hashstate_unseenE
              with (hashstate:= hashes)
                   (key':= value)
                   (value':=hshs') => //=.
        }
        have H4:
                                                                                                                                            AmqHash.AMQHash_hashstate_contains
                                                                                                                                              (AmqHash.AMQHash_hashstate_put hashes value hshs') value hshs'. {
          apply AmqHash.AMQHash_hashstate_add_contains_base => //=.
            by apply AmqHash.AMQHash_hashstate_available_capacityW with (n:=l.+1) => //=.
        }
        move: (@AmqOperations.AMQ_add_multiple_hash_contains_preserve
                 h s (AmqHash.AMQHash_hashstate_put hashes value hshs')
                 (A.AMQ_new s) amq' value hshs' values hsh'' l
                 Hlen Huniq
                 H1 H2 H3 H4 Hamq
              ) => Hcont'.
        rewrite (@AmqHash.AMQHash_hash_seen_insertE _ _ _ _ hshs') //=.
          by over. by over. by over. by over.
      }
      under_all ltac:(rewrite  -RIneq.INR_IZR_INZ boolR_distr).
      comp_simplify_n 2.
      apply Logic.eq_sym;
        under eq_bigr do rewrite (@Map.AMQ_map_newE _ (A.AMQ_new s)) //=;
              apply Logic.eq_sym.

      have H1: A.AMQ_available_capacity h (A.AMQ_new s) (length values). {
        move/eqP:Hlen ->; apply   A.AMQ_available_capacityW with (n:=l.+1) => //=.
          by apply A.AMQ_new_validT.
      }
      under eq_bigr => hshs'' _. {
        under eq_rsum_ne0 => amq' Hamq.

        have H1': A.AMQ_available_capacity h (A.AMQ_new s) (l + 1). {
            by rewrite addn1.
        }
        move: (@AmqOperations.AMQ_add_multiple_properties_preserve
                 h s (AmqHash.AMQHash_hashstate_put hashes value hshs')
                 (A.AMQ_new s) amq' values hshs'' l 1
                 Hlen (A.AMQ_new_validT _) H1' Hamq
              ) => /andP[Hvalid' Hcap']; clear H1.
        rewrite -Map.AMQ_map_query_internalE => //=.
          by over. by over.
      }
      rewrite index_enum_simpl; under eq_bigr do rewrite index_enum_simpl.
      rewrite (@AMQ_map_add_multipleE
                 (A.AMQ_new s) ((AmqHash.AMQHash_hashstate_put hashes value hshs')) values
                 (fun i i0 =>
                    ((B.AMQ_query_internal i0 hshs' %R) *R* AmqHash.AMQHash_probability h))
                 (A.AMQ_new_validT _)
                 H1
              ) => //=.
      rewrite index_enum_simpl //=; apply eq_bigr => hshs _.
      rewrite -index_enum_simpl //=; apply eq_bigr => amq' _.
        by rewrite (Map.AMQ_map_newE (A.AMQ_new s)); apply Map.AMQ_map_capacityE => //=.
    Qed.
    
  End PropertyMap.

End AMQPropertyMap.


Module BasicHash (Spec:HashSpec) <: AMQHASH.


  Module Hash := Hash Spec.
  
  Definition AMQHashKey : finType := Spec.B.

  
  Definition AMQHashParams: Type := nat.
  Definition AMQHashValue  (params: AMQHashParams) : finType :=
    [finType of 'I_Spec.Hash_size.+1].
  Definition AMQHash (n: AMQHashParams) := [finType of Hash.HashState n].

  Section AMQHash.
    Variable p: AMQHashParams. 
    Definition AMQHash_probability (n: AMQHashParams) :=
      Rdefinitions.Rinv (#|AMQHashValue n| %R).

    Section HashProbability.

      Variable h: AMQHashParams.

      Lemma AMQHash_hash_prob_valid:
        \sum_(v in  AMQHashValue h) (AMQHash_probability h) = 1.
      Proof.
        rewrite/AMQHash_probability bigsum_card_constE mulRV //=.
        rewrite RIneq.INR_IZR_INZ card_ord; apply/eqP => //=.
      Qed.

    End HashProbability.

    (* deterministic pure transformations of hash state  *)
    Definition AMQHash_hashstate_find
               (hashstate: AMQHash p) (key: AMQHashKey)
      : option (AMQHashValue p) :=
      Hash.hashstate_find p key hashstate.

    Definition AMQHash_hashstate_put
               (hashstate: AMQHash p) (key: AMQHashKey) (value: AMQHashValue p)
      : AMQHash p :=
      Hash.hashstate_put p key value hashstate.

    (* boolean properties of hash states*)
    Definition AMQHash_hashstate_available_capacity
               (hashstate:AMQHash p) (l:nat) : bool :=
      [length hashstate] + l < p.

    Definition AMQHash_hashstate_valid (hashstate:  AMQHash p) : bool :=
      true.

    Definition AMQHash_hashstate_contains
               (hashstate:  AMQHash p) (key: AMQHashKey) (value: AMQHashValue p)
      : bool :=
      Hash.hashstate_find p key hashstate == Some value.

    Definition AMQHash_hashstate_unseen
               (hashstate:  AMQHash p) (key: AMQHashKey) : bool :=
      Hash.hashstate_find p key hashstate == None.

    (* probabilistic hash operation*)
    Definition AMQHash_hash
               (hashstate: AMQHash p)
               (key: AMQHashKey) : Comp [finType of (AMQHash p * AMQHashValue p)] :=
      Hash.hash p key hashstate.

    (* properties of deterministic hash state operations *)
    Section DeterministicOperations.

      Variable hashstate: AMQHash p.

      Lemma AMQHash_hashstate_contains_findE: forall (key: AMQHashKey) (value: AMQHashValue p) ,
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_contains hashstate key value ->
          AMQHash_hashstate_find  hashstate key = Some value.
      Proof.
        rewrite/AMQHashKey/AMQHashValue/AMQHash_hashstate_valid/AMQHash_hashstate_contains/AMQHash_hashstate_find //=.
          by move=>key value _ /eqP ->.
      Qed.
      

      Lemma AMQHash_hashstate_unseen_nfindE: forall (key: AMQHashKey) (value: AMQHashValue p),
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_unseen hashstate key ->
          AMQHash_hashstate_find  hashstate key = None.
      Proof.
        rewrite/AMQHashKey/AMQHashValue/AMQHash_hashstate_valid/AMQHash_hashstate_contains/AMQHash_hashstate_find/AMQHash_hashstate_unseen //=.
          by move=> key value _ /eqP.
      Qed.
      
      Lemma AMQHash_hashstate_available_capacityW: forall n m, m <= n ->
                                                               AMQHash_hashstate_valid hashstate ->
                                                               AMQHash_hashstate_available_capacity hashstate n ->
                                                               AMQHash_hashstate_available_capacity hashstate m.
      Proof.
        rewrite/AMQHashKey/AMQHashValue/AMQHash_hashstate_valid/AMQHash_hashstate_contains/AMQHash_hashstate_find/AMQHash_hashstate_unseen //=.
        move=> n m Hnm _; rewrite/AMQHash_hashstate_available_capacity.
        move: Hnm; rewrite leq_eqVlt => /orP [/eqP -> //=| Hltn].
        move=> Hlen; eapply ltn_trans with (n:=[length hashstate] + n) => //=.
          by rewrite ltn_add2l.
      Qed.

      Lemma AMQHash_hashstate_available_capacity_decr: forall l key value,
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate l.+1 ->
          AMQHash_hashstate_available_capacity (AMQHash_hashstate_put hashstate key value) l.
      Proof.
        rewrite/AMQHashKey/AMQHashValue/AMQHash_hashstate_valid/AMQHash_hashstate_contains/AMQHash_hashstate_find/AMQHash_hashstate_unseen //=.
        rewrite /AMQHash_hashstate_available_capacity/AMQHash_hashstate_put.
        rewrite /Hash.hashstate_put.
        move=> l key value _.
          by move=>/fixedlist_add_incr => /(_ value key); rewrite addnS.
      Qed.
      
      
      Lemma AMQHash_hashstate_add_contains_preserve: forall (key key': AMQHashKey) (value value': AMQHashValue p),
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 -> 
          key != key' -> AMQHash_hashstate_contains hashstate key value ->
          AMQHash_hashstate_contains (AMQHash_hashstate_put  hashstate key' value') key value.
      Proof.
        rewrite/AMQHashKey/AMQHashValue/AMQHash_hashstate_valid/AMQHash_hashstate_contains/AMQHash_hashstate_find/AMQHash_hashstate_unseen //=.
        rewrite /AMQHash_hashstate_available_capacity/AMQHash_hashstate_put.
        rewrite /Hash.hashstate_find.
        move=> key key' value value' _ Hlen Hkeynew Hfindeq.
        apply fixmap_find_eq => //=.
      Qed.
      
      Lemma AMQHash_hashstate_add_contains_base: forall (key: AMQHashKey) (value: AMQHashValue p),
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 ->
          AMQHash_hashstate_contains (AMQHash_hashstate_put  hashstate key value) key value.
      Proof.
        rewrite/AMQHashKey/AMQHashValue/AMQHash_hashstate_valid/AMQHash_hashstate_contains/AMQHash_hashstate_find/AMQHash_hashstate_unseen //=.
        rewrite /AMQHash_hashstate_available_capacity/AMQHash_hashstate_put.
        move=> key value _ Hlen.
        rewrite (@Hash.hash_find_insert_involutive p key value hashstate) //=.
          by move/ltnW: Hlen.
      Qed.

      Lemma AMQHash_hashstate_add_valid_preserve: forall (key: AMQHashKey) (value: AMQHashValue p), 
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 -> 
          AMQHash_hashstate_valid (AMQHash_hashstate_put  hashstate key value).
      Proof.
        rewrite/AMQHashKey/AMQHashValue/AMQHash_hashstate_valid/AMQHash_hashstate_contains/AMQHash_hashstate_find/AMQHash_hashstate_unseen //=.
      Qed.
      
      Lemma AMQHash_hashstate_unseenE: forall
          (hashstate': AMQHash p) (key key': AMQHashKey)
          (value': AMQHashValue p),
          key != key' ->
          AMQHash_hashstate_unseen hashstate key ->
          hashstate' = AMQHash_hashstate_put hashstate key' value' ->
          AMQHash_hashstate_unseen hashstate' key.
      Proof.
        rewrite/AMQHashKey/AMQHashValue/AMQHash_hashstate_valid/AMQHash_hashstate_contains/AMQHash_hashstate_find/AMQHash_hashstate_unseen //=.
        move=> hashstate' key key' value' Hkey Hfind ->.
        rewrite /AMQHash_hashstate_put/  Hash.hashstate_find/  Hash.hashstate_put.
        apply fixmap_find_neq => //=.
      Qed.
    End DeterministicOperations.
    
    Lemma  AMQHash_hash_unseen_insert_eqE: forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value: AMQHashValue p),
        AMQHash_hashstate_unseen hashstate key -> hashstate' = AMQHash_hashstate_put hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value) = AMQHash_probability p.
    Proof.
      rewrite/AMQHash_hash/AMQHash_hashstate_put/AMQHash_hashstate_unseen.
      move=> //= hsh hsh' key value //= /eqP Huns ->.
      rewrite/Hash.hash Huns //=; comp_normalize.
      comp_simplify; under eq_bigr do rewrite xpair_eqE boolR_distr.
      comp_simplify; rewrite eq_refl //= mul1R //=.
    Qed.

    Lemma  AMQHash_hash_unseen_insert_neqE: forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value: AMQHashValue p),
        AMQHash_hashstate_unseen hashstate key -> hashstate' != AMQHash_hashstate_put hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value) = 0.
    Proof.
      rewrite/AMQHash_hash/AMQHash_hashstate_put/AMQHash_hashstate_unseen.
      move=> //= hsh hsh' key value //= /eqP Huns Hneq.
      rewrite/Hash.hash Huns //=; comp_normalize.
      comp_simplify; under eq_bigr do rewrite xpair_eqE boolR_distr.
        by comp_simplify; move/Bool.negb_true_iff: Hneq ->; rewrite //= mul0R.
    Qed.

    Lemma AMQHash_hash_seen_insertE: forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value value': AMQHashValue p),
        AMQHash_hashstate_contains hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value') = ((hashstate' == hashstate) && (value' == value)).
    Proof.
      rewrite/AMQHash_hash/AMQHash_hashstate_put/AMQHash_hashstate_unseen/AMQHash_hashstate_contains.
      move=> //= hsh hsh' key value value' /eqP Hcont //=.
      rewrite/Hash.hash Hcont //=; comp_normalize.
        by rewrite xpair_eqE //= RIneq.INR_IZR_INZ.
    Qed.

  End AMQHash.    
End BasicHash.



Module BasicHashVec  (Spec:HashSpec) <: AMQHASH.
  Module HashVec := HashVec Spec.

  Definition AMQHashKey : finType := Spec.B.
  Definition AMQHashParams := (nat * nat)%type. (* first elem is n, second is l *)

  Definition AMQHashValue (pair: AMQHashParams) : finType :=
    [finType of (snd pair).+1.-tuple ('I_Spec.Hash_size.+1)].

  Definition AMQHash (pair: AMQHashParams) :=
    [finType of (snd pair).+1.-tuple (HashVec.Hash.HashState (fst pair))].

  Section AMQHash.
    Variable p: AMQHashParams. 
    Definition AMQHash_probability (pair: AMQHashParams) : Rdefinitions.R :=
      ((Rdefinitions.Rinv (Spec.Hash_size.+1)%:R) ^R^ (snd pair).+1).

    Section HashProbability.
      Variable h: AMQHashParams.

      Lemma AMQHash_hash_prob_valid:
        \sum_(v in  AMQHashValue h) (AMQHash_probability h) = 1.
      Proof.
        rewrite/AMQHashValue/AMQHash_probability; rewrite bigsum_card_constE.
        rewrite card_tuple card_ord.
        rewrite -natRexp -expRM mulRV //=; first by rewrite Rfunctions.pow1 mulR1.
          by rewrite RIneq.INR_IZR_INZ; apply/eqP => //=.
      Qed.
    End HashProbability.

    (* deterministic pure transformations of hash state  *)

    Definition AMQHash_hashstate_put
               (hashstate: AMQHash p) (key: AMQHashKey)
               (value: AMQHashValue p) : AMQHash p :=
      Tuple (@HashVec.hash_vec_insert_length
               (fst p) (snd p).+1 key hashstate value).


    (* boolean properties of hash states*)
    Definition AMQHash_hashstate_available_capacity
               (hashstate:AMQHash p) (l:nat) :bool :=
      (@HashVec.hashes_have_free_spaces (snd p).+1 (fst p) hashstate l).

    Definition  AMQHash_hashstate_valid (hashstate: AMQHash p) : bool := true.

    Definition AMQHash_hashstate_contains
               (hashstate: AMQHash p) (key: AMQHashKey)
               (value: AMQHashValue p) : bool :=
      (@HashVec.hash_vec_contains_value (fst p) (snd p).+1 key hashstate value).

    Definition AMQHash_hashstate_unseen
               (hashstate: AMQHash p) (key:AMQHashKey) : bool :=
      (@HashVec.hashes_value_unseen (snd p).+1 (fst p) hashstate key).

    (* probabilistic hash operation*)
    Definition AMQHash_hash
               (hashstate: AMQHash p)
               (key: AMQHashKey) : Comp [finType of (AMQHash p * AMQHashValue p)] :=
      (@HashVec.hash_vec_int (fst p) (snd p).+1 key hashstate).

    (* properties of deterministic hash state operations *)
    Section DeterministicOperations.

      Variable hashstate: AMQHash p.

      Lemma AMQHash_hashstate_available_capacityW: forall n m, m <= n ->
                                                               AMQHash_hashstate_valid hashstate ->
                                                               AMQHash_hashstate_available_capacity hashstate n ->
                                                               AMQHash_hashstate_available_capacity hashstate m.
      Proof.
        rewrite /AMQHash_hashstate_available_capacity/HashVec.hashes_have_free_spaces//=.
        rewrite /HashVec.hash_has_free_spaces//=.
        move=> n m Hnm _ /allP Hvv; apply/allP => v Hv; move: (Hvv v Hv).
        apply leq_trans.
          by rewrite leq_add2l.
      Qed.

      Lemma AMQHash_hashstate_available_capacity_decr: forall l key value,
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate l.+1 ->
          AMQHash_hashstate_available_capacity (AMQHash_hashstate_put hashstate key value) l.
      Proof.
        rewrite /AMQHash_hashstate_available_capacity/HashVec.hashes_have_free_spaces//=.
        rewrite /HashVec.hash_has_free_spaces//=.
        move=> l key value _ /allP Hvv; apply/allP=>v//=.
        move=>/mapP[[v' ind']] /mem_zip/andP [ Hv' Hind'] ->.
        rewrite /HashVec.Hash.hashstate_put.
        apply fixedlist_add_incr.
          by move: (Hvv v' Hv'); rewrite addnS.
      Qed.
      
      
      Lemma  AMQHash_hashstate_add_contains_preserve: forall (key key': AMQHashKey) (value value': AMQHashValue p),
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 -> 
          key != key' -> AMQHash_hashstate_contains hashstate key value ->
          AMQHash_hashstate_contains (AMQHash_hashstate_put  hashstate key' value') key value.
      Proof.
        rewrite /AMQHash_hashstate_available_capacity/HashVec.hashes_have_free_spaces//=.
        move=> key key' value value' _ /allP Hfree Hknew.
        apply HashVec.hash_vec_contains_value_preserve => //=.
      Qed.
      

      Lemma  AMQHash_hashstate_add_contains_base: forall (key: AMQHashKey) (value: AMQHashValue p),
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 ->
          AMQHash_hashstate_contains (AMQHash_hashstate_put  hashstate key value) key value.
      Proof.
        move=> key  value  _  Hfree.
        apply HashVec.hash_vec_contains_value_base => //=.
      Qed.
      

      Lemma AMQHash_hashstate_add_valid_preserve: forall (key: AMQHashKey) (value: AMQHashValue p), 
          AMQHash_hashstate_valid hashstate ->
          AMQHash_hashstate_available_capacity hashstate 1 -> 
          AMQHash_hashstate_valid (AMQHash_hashstate_put  hashstate key value).
      Proof.
          by [].
      Qed.
      

      Lemma AMQHash_hashstate_unseenE: forall (hashstate': AMQHash p) (key key': AMQHashKey) (value': AMQHashValue p),
          key != key' ->
          AMQHash_hashstate_unseen hashstate key ->
          hashstate' = AMQHash_hashstate_put hashstate key' value' ->
          AMQHash_hashstate_unseen hashstate' key.
      Proof.
        move=>hsh key key' value' Hkneq /allP Hunseen ->//=.
        apply/allP => v /mapP [[v' ind']]//=/mem_zip/andP[Hv' Hind']->.
        move: (Hunseen v' Hv').
        apply fixmap_find_neq => //=.
      Qed.
      
    End DeterministicOperations.
    
    Lemma  AMQHash_hash_unseen_insert_eqE: forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value: AMQHashValue p),
        AMQHash_hashstate_unseen hashstate key -> hashstate' = AMQHash_hashstate_put hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value) = AMQHash_probability p.
    Proof.
      move=>hsh hsh' key value Hunseen ->.
      rewrite/AMQHash_hash.
      rewrite HashVec.hash_vecP //=.
    Qed.

    Lemma  AMQHash_hash_unseen_insert_neqE: forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value: AMQHashValue p),
        AMQHash_hashstate_unseen hashstate key -> hashstate' != AMQHash_hashstate_put hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value) = 0.
    Proof.
      move=>hsh hsh' key value Hunseen Hneq.
      rewrite HashVec.neg_hash_vecP //=.
    Qed.

    Lemma AMQHash_hash_seen_insertE: forall (hashstate hashstate': AMQHash p) (key: AMQHashKey) (value value': AMQHashValue p),
        AMQHash_hashstate_contains hashstate key value ->
        d[ AMQHash_hash hashstate key ] (hashstate', value') = ((hashstate' == hashstate) && (value' == value)).
    Proof.
      move=> hsh hsh' key value value' Hcontains.
      rewrite (@HashVec.hash_vec_find_simpl _ _ _ _ _ value)//=.
        by rewrite RIneq.INR_IZR_INZ//=.
    Qed.

  End AMQHash.    
End BasicHashVec.


Module BloomFilterAMQ (Spec: HashSpec).
  Module BasicHashVec := BasicHashVec Spec.
  Module BloomFilterDefinitions :=  BloomFilterDefinitions Spec.

  Export BasicHashVec.
  Export BloomFilterDefinitions.

  Module AMQ <: AMQ BasicHashVec.

    Definition AMQStateParams := True.

    Definition AMQState (val:AMQStateParams) : finType :=
      [finType of BloomFilterDefinitions.BloomFilter ].

    Section AMQ.
      Variable p: AMQStateParams.
      Variable h: BasicHashVec.AMQHashParams.

      Definition AMQ_add_internal
                 (amq: AMQState p)
                 (inds: BasicHashVec.AMQHashValue h) : AMQState p :=
        BloomFilterDefinitions.bloomfilter_add_internal
          inds amq.

      Definition AMQ_query_internal
                 (amq: AMQState p) (inds: BasicHashVec.AMQHashValue h) : bool :=

        BloomFilterDefinitions.bloomfilter_query_internal
          inds amq.
      Definition AMQ_available_capacity (_: BasicHashVec.AMQHashParams) (amq: AMQState p) (l:nat) : bool := true.
      Definition AMQ_valid (amq: AMQState p) : bool := true.

      Definition AMQ_new: AMQState p :=
        BloomFilterDefinitions.bloomfilter_new.

      
      Lemma AMQ_new_nqueryE: forall vals, ~~ AMQ_query_internal  AMQ_new vals.
      Proof.
        move=> //= vals.
        apply BloomFilterDefinitions.bloomfilter_new_empty.
          by rewrite -length_sizeP size_tuple => //=.
      Qed.
      
      Lemma AMQ_new_validT: AMQ_valid AMQ_new.
      Proof.
          by [].
      Qed.
      
      Section DeterministicProperties.
        Variable amq: AMQState p.

        Lemma AMQ_available_capacityW: forall  n m,
            AMQ_valid amq -> m <= n -> AMQ_available_capacity h amq n -> AMQ_available_capacity h amq m.
        Proof.
            by [].
        Qed.
        
        Lemma AMQ_add_query_base: forall (amq: AMQState p) inds,
            AMQ_valid amq -> AMQ_available_capacity h amq 1 ->
            AMQ_query_internal (AMQ_add_internal amq inds) inds.
        Proof.
          move=> //= amq' inds _ _.
          move: inds => [inds Hinds] //=.
          rewrite/AMQ_query_internal/AMQ_add_internal//=; clear Hinds.
          elim: inds  amq' => //= ind inds IHinds amq'.
          apply/andP;split.
            by apply bloomfilter_add_internal_preserve; apply tnth_set_nth_eq.
            apply IHinds.
        Qed.
        
        Lemma AMQ_add_valid_preserve: forall (amq: AMQState p) inds,
            AMQ_valid amq -> AMQ_available_capacity h amq 1 ->
            AMQ_valid (AMQ_add_internal amq inds).
        Proof.
            by [].
        Qed.
        
        Lemma AMQ_add_query_preserve: forall (amq: AMQState p) inds inds',
            AMQ_valid amq -> AMQ_available_capacity h amq 1 -> AMQ_query_internal amq inds ->
            AMQ_query_internal (AMQ_add_internal amq inds') inds.
        Proof.
          move=> amq' inds inds' _ _.
          move=>/allP Hquery; apply/allP => v Hv; move: (Hquery v Hv).
          apply bloomfilter_add_internal_preserve.
        Qed.
        
        Lemma AMQ_add_capacity_decr: forall (amq: AMQState p) inds l,
            AMQ_valid amq -> AMQ_available_capacity h amq l.+1 ->
            AMQ_available_capacity h (AMQ_add_internal amq inds) l.
        Proof.
            by [].
        Qed.
        
        Lemma AMQ_query_valid_preserve: forall (amq: AMQState p) inds,
            AMQ_valid amq -> AMQ_valid (AMQ_add_internal amq inds).
        Proof.
            by [].
        Qed.
        
        Lemma AMQ_query_capacity_preserve: forall (amq: AMQState p) inds l,
            AMQ_valid amq -> AMQ_available_capacity h amq l.+1 -> AMQ_available_capacity h (AMQ_add_internal amq inds) l.
        Proof.
            by [].
        Qed.

      End DeterministicProperties.
    End AMQ.
  End AMQ.

End BloomFilterAMQ.



Module CountingBloomFilterAMQ (Spec: HashSpec).
  Module BasicHashVec := BasicHashVec Spec.
  Module CountingBloomFilterDefinitions :=  CountingBloomFilterDefinitions Spec.

  Export BasicHashVec.
  Export CountingBloomFilterDefinitions.

  Module AMQ <: AMQ BasicHashVec.

    Inductive AMQStateParamsInt :=
    | mkStateParams (n:nat) of  n > 0.

    Definition AMQStateParams := AMQStateParamsInt.

    Definition AMQStateParamsToNat params :=
      match params with
      | mkStateParams n Hn => n
      end.

    Definition AMQState (n: AMQStateParams) : finType :=
      [finType of CountingBloomFilterDefinitions.CountingBloomFilter (AMQStateParamsToNat n)].

    Section AMQ.
      Variable p: AMQStateParams.
      Variable h: BasicHashVec.AMQHashParams.

      Definition AMQ_add_internal
                 (amq: AMQState p)
                 (inds: BasicHashVec.AMQHashValue h) : AMQState p :=
        CountingBloomFilterDefinitions.countingbloomfilter_add_internal
          inds amq.

      Definition AMQ_query_internal
                 (amq: AMQState p) (inds: BasicHashVec.AMQHashValue h) : bool :=

        CountingBloomFilterDefinitions.countingbloomfilter_query_internal
          inds amq.



      Definition AMQ_available_capacity (amq: AMQState p) (l:nat) : bool :=
        CountingBloomFilterDefinitions.countingbloomfilter_free_capacity
          amq (l * h.2.+1).



      Definition AMQ_valid (amq: AMQState p) : bool := true.

      Definition AMQ_new: AMQState p :=
        CountingBloomFilterDefinitions.countingbloomfilter_new (AMQStateParamsToNat p).

      
      Lemma AMQ_new_nqueryE: forall vals, ~~ AMQ_query_internal  AMQ_new vals.
      Proof.
        move=> //= vals.
        apply/allPn; exists (thead vals); first by apply mem_tnth.
        rewrite/AMQ_new/countingbloomfilter_new.
        move: (eq_ind_r _ _ _) => H1.
        move: (@tnth_nseq_eq _ Hash_size.+1  (Ordinal (Hngt0 (AMQStateParamsToNat p))) (thead vals)).
        rewrite/nseq_tuple.
        move: (nseq_tupleP _ _) => H2.
        rewrite (proof_irrelevance _ H1 H2); clear H1.
        rewrite/countingbloomfilter_get_bit //= => -> //=.
      Qed.
      
      Lemma AMQ_new_validT: AMQ_valid AMQ_new.
      Proof.
          by [].
      Qed.
      
      Section DeterministicProperties.
        Variable amq: AMQState p.

        Lemma AMQ_available_capacityW: forall  n m,
            AMQ_valid amq -> m <= n ->
            AMQ_available_capacity amq n ->
            AMQ_available_capacity amq m.
        Proof.
          move=> n m _ Hmn /allP Hcfb; apply/allP => v Hv.
          move: (Hcfb v Hv).
          move: Hmn; rewrite leq_eqVlt => /orP[/eqP -> | Hlmn] //=.
          apply ltn_trans.
          rewrite ltn_add2l ltn_mul2r //=.
        Qed.
        
        Lemma AMQ_add_query_base: forall (amq: AMQState p) inds,
            AMQ_valid amq -> AMQ_available_capacity amq 1 ->
            AMQ_query_internal (AMQ_add_internal amq inds) inds.
        Proof.
          move=> //= amq' inds _ Hcap.
          rewrite/  AMQ_query_internal/AMQ_add_internal.
          apply countingbloomfilter_add_base.
          move: inds => [inds Hinds] //=.
          rewrite/AMQ_query_internal/AMQ_add_internal//=; clear Hinds.
            by case: p => //=.
        Qed.
        
        Lemma AMQ_add_valid_preserve: forall (amq: AMQState p) inds,
            AMQ_valid amq -> AMQ_available_capacity amq 1 ->
            AMQ_valid (AMQ_add_internal amq inds).
        Proof.
            by [].
        Qed.
        
        Lemma AMQ_add_query_preserve: forall (amq: AMQState p) inds inds',
            AMQ_valid amq -> AMQ_available_capacity amq 1 -> AMQ_query_internal amq inds ->
            AMQ_query_internal (AMQ_add_internal amq inds') inds.
        Proof.
          move=> amq' inds inds' _ _.
          apply countingbloomfilter_add_preserve.
            by case p.
        Qed.
        
        Lemma AMQ_add_capacity_decr: forall (amq: AMQState p) inds l,
            AMQ_valid amq -> AMQ_available_capacity amq l.+1 ->
            AMQ_available_capacity (AMQ_add_internal amq inds) l.
        Proof.
          rewrite/AMQ_available_capacity/AMQ_add_internal.
          move=> amq' [inds Hinds] l _.
          move:(@countingbloomfilter_add_capacity_change
                  0 _ h.2.+1 (l * h.2.+1) amq' inds Hinds
               ).
            by rewrite -mulSn => H /H //=.
        Qed.
        
        Lemma AMQ_query_valid_preserve: forall (amq: AMQState p) inds,
            AMQ_valid amq -> AMQ_valid (AMQ_add_internal amq inds).
        Proof.
            by [].
        Qed.
        
        Lemma AMQ_query_capacity_preserve: forall (amq: AMQState p) inds l,
            AMQ_valid amq -> AMQ_available_capacity amq l.+1 -> AMQ_available_capacity (AMQ_add_internal amq inds) l.
        Proof.
          apply AMQ_add_capacity_decr.
        Qed.

      End DeterministicProperties.
    End AMQ.
  End AMQ.
  
End  CountingBloomFilterAMQ.


Module QuotientFilterAMQ (QSpec: QuotientFilterSpec).
  Module QuotientFilterDefinitions := QuotientFilterDefinitions QSpec.

  Module BasicHash := BasicHash  QuotientFilterDefinitions.QuotientHash.

  Export BasicHash.
  Export QuotientFilterDefinitions.

  Module AMQ: AMQ BasicHash.


    Definition AMQStateParams := True.
    Definition AMQState (params: AMQStateParams) : finType :=
      [finType of QuotientFilter].

    Section AMQ.
      Variable p: AMQStateParams.
      Variable h: BasicHash.AMQHashParams.

      Definition AMQ_add_internal
                 (amq: AMQState p) (value: BasicHash.AMQHashValue h):
        AMQState p := quotientfilter_add_internal value amq.
      
      Definition AMQ_query_internal
                 (amq: AMQState p) (key: BasicHash.AMQHashValue h) : bool :=
        quotientfilter_query_internal key amq.

      Definition AMQ_available_capacity
                 (h: BasicHash.AMQHashParams) (amq: AMQState p) (l:nat): bool:=
        quotientfilter_has_free_spaces (h.+1 * l) amq.

      Definition AMQ_valid (amq:AMQState p) : bool :=
        quotientfilter_valid amq.

      Definition AMQ_new: AMQState p := quotientfilter_new.

      Lemma AMQ_new_nqueryE: forall vals, ~~ AMQ_query_internal  AMQ_new vals.
      Proof.
        move=> vals; rewrite/AMQ_query_internal/quotientfilter_query_internal//=.
        rewrite tnth_nseq_eq.
        rewrite/fixlist_contains //=.
        apply/hasPn => v.
        move: (@fixlist_empty_is_empty [eqType of 'I_r.+1] n.+1).
        rewrite/fixlist_is_empty =>/eqP -> //=.
      Qed.
      
      Lemma AMQ_new_validT: AMQ_valid AMQ_new.
      Proof.
          by apply quotientfilter_new_valid.
      Qed.
      
      Section DeterministicProperties.
        Variable amq: AMQState p.

        Lemma AMQ_available_capacityW: forall  n m,
            AMQ_valid amq -> m <= n -> AMQ_available_capacity h amq n -> AMQ_available_capacity h amq m.
        Proof.
          move=> n m Hvalid Hnm /allP Hvv; apply/allP => v Hv; move:(Hvv v Hv) => //=.
          apply leq_trans; rewrite leq_add2l //=.
            by rewrite leq_mul2l Hnm; apply/orP; right.
        Qed.
      End DeterministicProperties.

      Section DeterministicProperties.
        Variable amq: AMQState p.

        Lemma AMQ_add_query_base: forall (amq: AMQState p) inds,
            AMQ_valid amq -> AMQ_available_capacity h amq 1 ->
            AMQ_query_internal (AMQ_add_internal amq inds) inds.
        Proof.
          apply quotientfilter_add_query_base.
        Qed.
        
        Lemma AMQ_add_valid_preserve: forall (amq: AMQState p) inds,
            AMQ_valid amq -> AMQ_available_capacity h amq 1 ->
            AMQ_valid (AMQ_add_internal amq inds).
        Proof.
          rewrite /AMQ_available_capacity muln1/AMQHashValue/AMQ_valid.
          rewrite/quotientfilter_valid/quotientfilter_has_free_spaces.
          move=> [amq'] ind /allP Hvv /allP Hspace; apply /allP => v.
          rewrite/AMQ_add_internal/quotientfilter_add_internal.
          case_eq (quotient_num ind) => quot rem Heq.

          have H f:  quotientfilter_state {|  quotientfilter_state := f |} = f; first by [].
          rewrite !H.
          move=>/tnthP [ quot' ].
          case Hquot: (quot' != quot).
          - rewrite tnth_set_nth_neq; first move=>->; last by [].
            apply Hvv.
              by apply mem_tnth.
          - move/Bool.negb_true_iff: Hquot; rewrite Bool.negb_involutive => /eqP ->.
            rewrite tnth_set_nth_eq; first move=>->; last by [].
            apply fixlist_insert_preserves_top_heavy.
            apply Hvv.
              by apply mem_tnth.
        Qed.

        Lemma AMQ_add_query_preserve: forall (amq: AMQState p) inds inds',
            AMQ_valid amq -> AMQ_available_capacity h amq 1 -> AMQ_query_internal amq inds ->
            AMQ_query_internal (AMQ_add_internal amq inds') inds.
        Proof.
          move=> amq' ind inds' Hvalid Hcap.
            by apply quotientfilter_add_query_preserve.
        Qed.
        
        Lemma AMQ_add_capacity_decr: forall (amq: AMQState p) inds l,
            AMQ_valid amq -> AMQ_available_capacity h amq l.+1 ->
            AMQ_available_capacity h (AMQ_add_internal amq inds) l.
        Proof.
          move=> amq' ind l Hvalid Hcap.
          rewrite /AMQ_available_capacity in Hcap.
          have Hobv: 0 < h.+1 * l.+1; first by rewrite muln_gt0; apply/andP;split => //=.
          move: (@quotientfilter_add_preserve
                   _ Hobv amq'
                   (quotientfilter_add_internal ind amq')
                   ind Hvalid Hcap
                   (Logic.eq_refl
                      (quotientfilter_add_internal ind amq'))
                ) => /andP [_ ].

          rewrite/AMQ_available_capacity.
          rewrite mulnS addnC addnS -pred_Sn.
          move=>/allP Hvv; apply/allP => v Hv; move: (Hvv v Hv).
            by rewrite addnA =>/leq_addr_weaken.
        Qed.
        


      End DeterministicProperties.
    End AMQ.
  End AMQ.
End QuotientFilterAMQ.


Module Type BlockedAMQSpec.

  (** number of blocks(amqs) in Blocked AMQ - 1 *)
  Parameter n:nat.
  Parameter Hngt0: n > 0.

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

      Lemma unzip_tupleP (n : nat) (T U : Type) (xs: seq (T * U)%type):
        size xs == n -> (size (unzip1 xs) == n) && (size (unzip2 xs) == n).
      Proof.
        move=>/eqP<-;clear n.
        by elim: xs => [//=| x xs /andP [Hl Hr]] //=.
      Qed.

      Lemma unzip_tuplePL (n : nat) (T U : Type) (xs: seq (T * U)%type):
        size xs == n -> size (unzip1 xs) == n.
      Proof. by move=>/unzip_tupleP/andP[]. Qed.

      Lemma unzip_tuplePR (n : nat) (T U : Type) (xs: seq (T * U)%type):
        size xs == n -> size (unzip2 xs) == n.
      Proof. by move=>/unzip_tupleP/andP[]. Qed.

      Definition unzip_tuple (n : nat) (T U : Type) (xs: n.-tuple (T * U)%type):
        (n.-tuple T * n.-tuple U)%type :=
        let: (Tuple _ hprf) := xs in (Tuple (unzip_tuplePL hprf), Tuple (unzip_tuplePR hprf)).

      Lemma rsum_zip_tuple_split (A B:finType) l (f: (l.-tuple (A * B)%type) -> Rdefinitions.R) P :
            \sum_(i in [finType of l.-tuple (A * B)%type] | P i) (f i) =
            \sum_(ab in [finType of (l.-tuple A * l.-tuple B)%type] | P (zip_tuple ab.1 ab.2))
             (f (zip_tuple ab.1 ab.2)).
      Proof.
        apply reindex.
        exists (@unzip_tuple l _ _).
        - {
            move=> [[ls Hls] [rs Hrs]] _ //=. 
            move: (unzip_tuplePL _)=> //=.
            move: (unzip_tuplePR _)=> //=.
            rewrite unzip2_zip.
            rewrite unzip1_zip.
            move=> H1; rewrite (proof_irrelevance _ H1 Hrs); clear H1.
            move=> H2; rewrite (proof_irrelevance _ H2 Hls); clear H2.
            by [].
            by move/eqP: Hls ->; move/eqP:Hrs ->.
            by move/eqP: Hls ->; move/eqP:Hrs ->.
          }
        - {
            move=> [zs Hzs] _ //=. 
            rewrite/zip_tuple.
            move: (zip_tupleP _ _)=> //=.
            rewrite zip_unzip => H1.
            by rewrite (proof_irrelevance _ H1 Hzs); clear H1.
          }
      Qed.



      Lemma binomial_summation (m p q:nat)
            (ind: 'I_p.+1) (f: m.-tuple ('I_p.+1) -> Rdefinitions.R) (c: Rdefinitions.R):
        (forall (i:m.-tuple ('I_p.+1)), size [seq x | x <- i & x == ind] == q -> f i = c) ->
        \sum_(i in [finType of  m.-tuple ('I_p.+1)] | size [seq x | x <- i & x == ind] == q)
         ((Rdefinitions.Rinv (#|[finType of 'I_p.+1]| %R) ^R^ m) *R* (f i)) =
        (('C(m, q) %R) *R*
         ((Rdefinitions.Rinv (#|[finType of 'I_p.+1]| %R) ^R^ q) *R*
          (((BinNums.Zpos BinNums.xH -R- Rdefinitions.Rinv (#|[finType of 'I_p.+1]| %R)) ^R^ (m - q)) *R*
           c))).
      Proof.
      Admitted.

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
      

    Admitted.

  End Properties.
End  BlockedAMQProperties.
End BlockedAMQ.

