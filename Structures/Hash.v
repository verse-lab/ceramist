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

Each hash function is represented using a random variable to simulate uniformly distributed random outputs
(i.e a perfect hash function) and a map mapping of input types to output values, to ensure repeated hashes
of the same value produce the same output.

 *)


Definition hash_keytype := [eqType of B].
Definition hash_valuetype := [eqType of (ordinal Hash_size.+1)].

Definition HashState n := fixmap hash_keytype hash_valuetype n.

Definition hashstate_find n k (m: HashState n) := fixmap_find k m.

Definition hashstate_put n k v (m: HashState n) := fixmap_put k v m.


Canonical hashstate_of_eqType n := Eval hnf in [eqType of (HashState n)].
Canonical hashstate_of_choiceType n := Eval hnf in [choiceType of (HashState n)].
Canonical hashstate_of_countType n := Eval hnf in [countType of (HashState n)].
Canonical hashstate_of_finType n := Eval hnf in [finType of (HashState n)].

Definition gen_random : Comp [finType of (ordinal Hash_size.+1)] :=
    y <-$ [0 ... Hash_size];
    ret y.


Definition hash n (value: hash_keytype) (hash_state: HashState n) : Comp [finType of ((HashState n) * hash_valuetype)] :=
  match hashstate_find _ value hash_state  with
  | Some(value) => ret (hash_state, value)
  | None =>
    rnd <-$ gen_random;
      new_state <- hashstate_put _ value rnd hash_state;
      ret (new_state, rnd)
  end.




