From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path bigop finfun .

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From BloomFilter
     Require Import Parameters Hash HashVec Comp Notationv1 BitVector FixedList.



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
  Variable Hkgt0: k >0.

  (*
     list of hash functions used in the bloom filter
   *)



    Record BloomFilter := mkBloomFilter {
                              bloomfilter_state: BitVector
                          }.

  Definition BloomFilter_prod (bf: BloomFilter) :=
    (bloomfilter_state bf).
  Definition prod_BloomFilter  pair := let: (state) := pair in @mkBloomFilter state.

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


  Definition bloomfilter_set_bit (value: 'I_(Hash_size.+1)) bf : BloomFilter :=
    mkBloomFilter
      (set_tnth (bloomfilter_state bf) true value).

  Definition bloomfilter_get_bit (value: 'I_(Hash_size.+1)) bf : bool :=
      (tnth (bloomfilter_state bf) value).

  Fixpoint bloomfilter_add_internal (items: seq 'I_(Hash_size.+1)) bf : BloomFilter :=
    match items with
      h::t => bloomfilter_add_internal t (bloomfilter_set_bit h bf)
    | [::]   => bf
    end.

  Definition bloomfilter_add (value: hash_keytype) (hashes: k.-tuple (HashState n)) (bf: BloomFilter) : Comp [finType of (k.-tuple (HashState n)) * BloomFilter] :=
    hash_res <-$ (hash_vec_int value hashes);
      let (new_hashes, hash_vec) := hash_res in
      let new_bf := bloomfilter_add_internal (tval hash_vec) bf in
      ret (new_hashes, new_bf).

  Definition bloomfilter_query_internal (items: seq 'I_(Hash_size.+1)) bf : bool :=
    all (fun h => bloomfilter_get_bit h bf) items.

  Definition bloomfilter_query (value: hash_keytype) (hashes: k.-tuple (HashState n)) (bf: BloomFilter) : Comp [finType of (k.-tuple (HashState n)) * bool ] :=
    hash_res <-$ (hash_vec_int value hashes);
      let (new_hashes, hash_vec) := hash_res in
      let qres := bloomfilter_query_internal (tval hash_vec) bf in
      ret (new_hashes, qres).

End BloomFilter.
