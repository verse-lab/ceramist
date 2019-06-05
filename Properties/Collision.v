From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path bigop finfun .

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path.

From infotheo
     Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From BloomFilter
     Require Import Parameters Hash Comp Notationv1 BitVector BloomFilter.

(*
Proof idea
----------

1. if hashstate_find value hash_state is None, then the output of the hash function is uniformly distributed from 0..Hash_size.+1
2. folding on a list of values such that all the values are not-equal ensures that hashstate_find value is always None
3. after insert, probability of all hash functions not setting a bit is (1 - 1/(Hash_size.+1))^k.
4. after k inserts,  probability of all hash functions not setting a bit is (1 - 1/(Hash_size.+1))^kn.
5. after k inserts,  probability of all hash functions setting a bit is 1 - (1 - 1/(Hash_size.+1))^kn.



 *)

Section Hash.

Lemma hash_uni n
      (hash_state: HashState n)
      value
      (hash_value: 'I_Hash_size.+1) :
  (hashstate_find _ value hash_state == None) ->
  (P[ ((hash n value hash_state) |> (fun h => ret (snd h ))) === hash_value ] = (Rdefinitions.Rdiv (Raxioms.INR 1)  (Raxioms.INR #|ordinal Hash_size.+1|))).
Proof.

  move=>/eqP Hhsfindnone.
  rewrite /hash Hhsfindnone //=.
  rewrite  DistBindA //=.
  rewrite DistBindp1.
  rewrite (functional_extensionality (fun x : 'I_Hash_size.+1 => DistBind.d (Dist1.d (hashstate_put n value x hash_state, x)) (fun b : HashState n * 'I_Hash_size.+1 => Dist1.d b.2)) (fun x : 'I_Hash_size.+1 => Dist1.d x)); first last.
    by move=> x; rewrite DistBind1f //=.
      by  rewrite DistBindp1 Uniform.dE div1R  //=.
Qed.

End Hash.



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

  About bloomfilter_add.
  About bloomfilter_query.


  Definition bloomfilter_not_full (bf: BloomFilter k n) : bool.
  (* provided the finite maps of all the hash function are not full*)
  Admitted.


  Lemma bloomfilter_addq (bf: BloomFilter k n) (value: B):
    (* provided bf is not full *)
    bloomfilter_not_full bf ->
    (* if bf' is the result of inserting into bf *)
    forall bf',  P[ (bloomfilter_add Hkgt0 value bf) === bf']   = (Raxioms.INR 1) ->
    (* bloomfilter_query for value will always reture true *)
     P[ (bloomfilter_query Hkgt0 value bf') ] = (Raxioms.INR 1).


  .

(* TODO: No False Negatives *)
(* Theorem no_false_negative *)