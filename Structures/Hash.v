From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.


From mathcomp.ssreflect
Require Import tuple.

From BloomFilter
Require Import Parameters Comp Notationv1 FixedMap.


(*
   Hash
-----------
Definition of arbitrary hash functions, assuming perfect uniform distribution.

Each hash function is represented using a random variable to simulate random outputs and a map mapping of input types to output values, to ensure repeated hashes of the same value produce the same output.
 *)


Definition hashstate_keytype := [eqType of B].
Definition hashstate_valuetype n := [eqType of (ordinal n)].

Definition HashState n := fixmap hashstate_keytype (hashstate_valuetype n) n.

Definition hashstate_find n k (m: HashState n) := fixmap_find k m.

Definition hashstate_put n k v (m: HashState n) := fixmap_put k v m.


Canonical hashstate_of_eqType n := Eval hnf in [eqType of (HashState n)].
Canonical hashstate_of_choiceType n := Eval hnf in [choiceType of (HashState n)].
Canonical hashstate_of_countType n := Eval hnf in [countType of (HashState n)].
Canonical hashstate_of_finType n := Eval hnf in [finType of (HashState n)].



Definition gen_random : Comp [finType of (ordinal Hash_size.+1)].
Admitted.
  (*   := *)
  (* y <-$ [0 ... Hash_size]; *)
  (*   ret y. *)


About gen_random.




