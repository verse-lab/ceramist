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
     Require Import Parameters Hash Comp Notationv1 BitVector FixedList.


Section BloomFilter.
  (*
   A fomalization of a bloom filter structure and properties

   *)

  (*
    k - number of hashes
   *)
  Variable k: nat.
  (*
    n - maximum number of hashes supported
  *)
  Variable n: nat.


  Record BloomFilter := mkBloomFilter {
                                bloomfilter_hashes: k.-tuple (HashState n);
                                bloomfilter_state: BitVector
                              }.

  Definition BloomFilter_prod (bf: BloomFilter) := (bloomfilter_hashes bf, bloomfilter_state bf).
  Definition prod_BloomFilter  pair := let: (hashes, state) := pair in mkBloomFilter  hashes state.

  Lemma bloomfilter_cancel : cancel (BloomFilter_prod) (prod_BloomFilter).
  Proof.
      by case.
  Qed.


  Definition bloomfilter_eqMixin :=
    CanEqMixin bloomfilter_cancel .
  Canonical bloomfilter_eqType  :=
    Eval hnf in EqType BloomFilter  bloomfilter_eqMixin .

  Definition bloomfilter_choiceMixin :=
    CanChoiceMixin bloomfilter_cancel.
  Canonical bloomfilter_choiceType  :=
    Eval hnf in ChoiceType BloomFilter  bloomfilter_choiceMixin.

  Definition bloomfilter_countMixin :=
    CanCountMixin bloomfilter_cancel.
  Canonical bloomfilter_countType :=
    Eval hnf in CountType BloomFilter  bloomfilter_countMixin.

  Definition bloomfilter_finMixin :=
    CanFinMixin bloomfilter_cancel .
  Canonical bloomfilter_finType :=
    Eval hnf in FinType BloomFilter  bloomfilter_finMixin.

  (* The first approximation: a number of axioms *)
  About set_tnth.


  Definition bloomfilter_set_bit (value: 'I_(Hash_size.+1)) bf : BloomFilter :=
    mkBloomFilter
      (bloomfilter_hashes bf)
    (set_tnth (bloomfilter_state bf) true value).


               Definition bloomfilter_add (value: B) (bf: BloomFilter) : Comp [finType of BloomFilter].
               Admitted.


               Fixpoint bloomfilter_add_internal (value: B) (bf: BloomFilter) : BloomFilter.
               Proof.
                 move: bf => [[xs H_xs] bvec].
                 Admitted.


                 Definition bloomfilter_query (value: B) (bf: BloomFilter ) : bool.
                 Admitted.


End BloomFilter.