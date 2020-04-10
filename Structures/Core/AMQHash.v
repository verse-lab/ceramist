(** * Structures/Core/AMQHash.v
-----------------

Defines an abstract interface the hash functions used in AMQs,
encoding both the deterministic and probabilistic behaviours of these
operations. Also provides instantiations of this interface for some
standard hash operations. *)

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
     Require Import Hash HashVec FixedList FixedMap.

(** Abstract interface for a hash function used in AMQs  *)
Module Type AMQHASH.
  Parameter AMQHashKey : finType.
  (** Allows the hash types to be parameterised - i.e see BasicHash
  defined later on where the parameters are the capacity of the hash
  function. *)
  Parameter AMQHashParams: Type.
  Parameter AMQHashValue: AMQHashParams -> finType.
  Parameter AMQHash : AMQHashParams -> finType.

  

  Section AMQHash.
    Variable p: AMQHashParams. 
    Parameter AMQHash_probability:  AMQHashParams -> Rdefinitions.R.

    Axiom AMQHash_hash_prob_valid:
      \sum_(v in  AMQHashValue p) (AMQHash_probability p) = 1.


    Parameter AMQHash_hashstate_put : AMQHash p -> AMQHashKey -> AMQHashValue p -> AMQHash p.

    (** ** Boolean properties of hash states*)
    Parameter AMQHash_hashstate_available_capacity : AMQHash p -> nat -> bool.
    Parameter AMQHash_hashstate_valid: AMQHash p -> bool.
    Parameter AMQHash_hashstate_contains: AMQHash p -> AMQHashKey -> AMQHashValue p -> bool.
    Parameter AMQHash_hashstate_unseen: AMQHash p -> AMQHashKey -> bool.

    (** ** Probabilistic hash operation*)
    Parameter AMQHash_hash: AMQHash p -> AMQHashKey -> Comp [finType of (AMQHash p * AMQHashValue p)].

    (**  Properties of deterministic hash state operations *)
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

(** Abstract interface encoding the required properties of AMQ hash
functions.  *)
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

(** * Instantiation of the AMQHash interface for random-oracle based
Hash functions.  *)
Module BasicHash (Spec:HashSpec) <: AMQHASH.

  Module Hash := Hash Spec.
  
  Definition AMQHashKey : finType := Spec.B.

  (** Parameter defines the capacity of the hash function  *)
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

    (** ** Deterministic pure transformations of hash state  *)
    Definition AMQHash_hashstate_find
               (hashstate: AMQHash p) (key: AMQHashKey)
      : option (AMQHashValue p) :=
      Hash.hashstate_find p key hashstate.

    Definition AMQHash_hashstate_put
               (hashstate: AMQHash p) (key: AMQHashKey) (value: AMQHashValue p)
      : AMQHash p :=
      Hash.hashstate_put p key value hashstate.

    (** ** Boolean properties of hash states*)
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

    (** ** Probabilistic hash operation*)
    Definition AMQHash_hash
               (hashstate: AMQHash p)
               (key: AMQHashKey) : Comp [finType of (AMQHash p * AMQHashValue p)] :=
      Hash.hash p key hashstate.

    (** **  Properties of deterministic hash state operations *)
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


(** Instantiation of the AMQ Hash interface for Hash vectors  *)
Module BasicHashVec  (Spec:HashSpec) <: AMQHASH.
  Module HashVec := HashVec Spec.

  Definition AMQHashKey : finType := Spec.B.

  (** Parameters are the capacity of the hash functions (n) and the number of the hash functions (l).  *)
  Definition AMQHashParams := (nat * nat)%type.

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

    (** ** Deterministic pure transformations of hash state  *)

    Definition AMQHash_hashstate_put
               (hashstate: AMQHash p) (key: AMQHashKey)
               (value: AMQHashValue p) : AMQHash p :=
      Tuple (@HashVec.hash_vec_insert_length
               (fst p) (snd p).+1 key hashstate value).


    (** ** Boolean properties of hash states*)
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

    (** ** Probabilistic hash operation*)
    Definition AMQHash_hash
               (hashstate: AMQHash p)
               (key: AMQHashKey) : Comp [finType of (AMQHash p * AMQHashValue p)] :=
      (@HashVec.hash_vec_int (fst p) (snd p).+1 key hashstate).

    (** ** Properties of deterministic hash state operations *)
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
