(** * Structures/Core/Hash.v
-----------------

Definition of arbitrary hash functions, assuming perfect uniform
distribution.  Each hash function is represented using a random
variable to simulate uniformly distributed random outputs (i.e a
perfect hash function) and a map mapping of input types to output
values, to ensure repeated hashes of the same value produce the same
output.
  *)

From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
     Require Import tuple.


From ProbHash.Computation
     Require Import Comp Notationv1.

From ProbHash.Utils
     Require Import  seq_ext.

From ProbHash.Core
     Require Import  FixedList FixedMap.


(** Parameters of a hash function *)
Module Type HashSpec.
  (** Input type being hashed *)
  Parameter B: finType.
  (** size of hash output and bitvector output *)
  Parameter Hash_size: nat.
End HashSpec.

(** Implementation of a  hash function as a random oracle.  *)
Module Hash (Spec : HashSpec).

  Export Spec.
  Definition hash_keytype := [eqType of B].
  Definition hash_valuetype := [eqType of (ordinal Hash_size.+1)].
  Definition HashState n := fixmap hash_keytype hash_valuetype n.
  Definition hashstate_find n k (m: HashState n) := fixmap_find k m.
  Definition hashstate_put n k v (m: HashState n) := fixmap_put k v m.

  Lemma hash_find_insert_involutive n' value x y : 
    FixedList.fixlist_length y + 1 <= n' ->
    hashstate_find n' value (hashstate_put n' value x y) = Some x.
  Proof.
    rewrite /hashstate_find/hashstate_put//=.
    rewrite addnS addn0.
    elim: n' value x  y => [//=|n' IHn'] value x y .
    rewrite (tuple_eta y) //=.
    rewrite/FixedList.ntuple_head/FixedList.ntuple_tail -/behead_tuple  !theadE ?beheadE ?behead_tupleE //=.
    case: (thead y) => [[k' v']|]//=; first case Hkeq: (k' == value) => //=; rewrite ?eq_refl//=.
    rewrite !ntuple_cons_eq //=.
    rewrite !behead_tupleE Hkeq //= => Hlen.
    apply IHn' => //=.
  Qed.

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

End Hash.
