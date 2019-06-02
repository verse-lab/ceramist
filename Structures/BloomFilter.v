From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.

From mathcomp
Require Import path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From BloomFilter
Require Import Parameters Hash Comp Notationv1 BitVector.


(*
   A fomalization of a bloom filter structure

   k - number of hashes
   n - maximum number of hashes supported
 *)
Record BloomFilter k n := {
       bloomfilter_hashes: k.-tuple (HashState n);
       bloomfilter_state: BitVector
}.


(* The first approximation: a number of axioms *)

Definition bloomfilter_add k n (value: B) (bf: BloomFilter k n) : BloomFilter k n.
  Admitted.

Definition bloomfilter_query k n (value: B) (bf: BloomFilter k n) : bool.
  Admitted.


