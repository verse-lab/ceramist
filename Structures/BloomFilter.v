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
Record BloomFilter k n := mkBloomFilter {
       bloomfilter_hashes: k.-tuple (HashState n);
       bloomfilter_state: BitVector
}.

Definition BloomFilter_prod k n (bf: BloomFilter k n) := (bloomfilter_hashes bf, bloomfilter_state bf).
Definition prod_BloomFilter k n pair := let: (hashes, state) := pair in @mkBloomFilter k n hashes state.

Lemma bloomfilter_cancel k n : cancel (@BloomFilter_prod k n) (@prod_BloomFilter k n).
Proof.
  by case.
Qed.


Definition bloomfilter_eqMixin k n :=
  CanEqMixin (@bloomfilter_cancel k n).
Canonical bloomfilter_eqType k n :=
  Eval hnf in EqType (@BloomFilter k n) (bloomfilter_eqMixin k n).

Definition bloomfilter_choiceMixin k n:=
  CanChoiceMixin (@bloomfilter_cancel k n).
Canonical bloomfilter_choiceType k n :=
  Eval hnf in ChoiceType (@BloomFilter k n ) (bloomfilter_choiceMixin k n).

Definition bloomfilter_countMixin k n :=
  CanCountMixin (@bloomfilter_cancel k n).
Canonical bloomfilter_countType k n :=
  Eval hnf in CountType (@BloomFilter k n) (bloomfilter_countMixin k n).

Definition bloomfilter_finMixin k n :=
  CanFinMixin (@bloomfilter_cancel k n).
Canonical bloomfilter_finType k n :=
Eval hnf in FinType (@BloomFilter k n) (bloomfilter_finMixin k n).

(* The first approximation: a number of axioms *)

Definition bloomfilter_add k n (value: B) (bf: BloomFilter k n) : Comp [finType of (BloomFilter k n)].
  Admitted.


Fixpoint bloomfilter_add_internal k n (value: B) (bf: BloomFilter k n) : BloomFilter k n.
Proof.
  move: bf => [[xs H_xs] bvec].


Definition bloomfilter_query k n (value: B) (bf: BloomFilter k n) : bool.
  Admitted.


