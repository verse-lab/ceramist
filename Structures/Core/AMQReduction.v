(** * Structures/Core/AMQReduction.v
-----------------

Defines a Coq Module that encapsulates a reduction argument for AMQ
modules, allowing transferring properties from one AMQ to another
provided a suitable mapping is defined. See
Structure/CountingBloomFilter/CountingBloomFilter_Properties.v for an
example use. *)


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
     Require Import Hash HashVec FixedList FixedMap AMQHash AMQ.


(** Module encapsulating the existance of a reduction from AMQ A to AMQ B.  *)
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
