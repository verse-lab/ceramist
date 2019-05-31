From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.


From mathcomp.ssreflect
Require Import tuple.

From BloomFilter
Require Import Parameters Comp Notationv1.


(*
   Hash
-----------
Definition of arbitrary hash functions, assuming perfect uniform distribution.

Each hash function is represented using a random variable to simulate random outputs and a map mapping of input types to output values, to ensure repeated hashes of the same value produce the same output.
 *)


Definition Map_keytype := [eqType of B].
Definition Map_valuetype n := [eqType of (ordinal n)].

