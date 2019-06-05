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
  Variable Hkgt0: k >0.


  Lemma Hpredkvld: k.-1 < k.
    Proof.
        by  apply InvMisc.ltnn_subS.
    Qed.


  Record BloomFilter := mkBloomFilter {
                            bloomfilter_cnt: 'I_k;
                            bloomfilter_hashes: k.-tuple (HashState n);
                            bloomfilter_state: BitVector
                          }.

  Definition BloomFilter_prod (bf: BloomFilter) :=
    (bloomfilter_cnt bf, bloomfilter_hashes bf, bloomfilter_state bf).
  Definition prod_BloomFilter  pair := let: (cnt, hashes, state) := pair in @mkBloomFilter cnt hashes state.

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
      (bloomfilter_cnt bf)
      (bloomfilter_hashes bf)
      (set_tnth (bloomfilter_state bf) true value).

  Definition bloomfilter_get_bit (value: 'I_(Hash_size.+1)) bf : bool :=
      (tnth (bloomfilter_state bf) value).

  Definition bloomfilter_calculate_hash (index: 'I_k) (input: B) (bf: BloomFilter) : Comp [finType of (BloomFilter * 'I_(Hash_size.+1))] :=
    let: hash_state := tnth (bloomfilter_hashes bf) index in
    hash_out <-$ (@hash _ input hash_state);
      let: (new_hash_state, hash_value) := hash_out in
      ret (mkBloomFilter (bloomfilter_cnt bf) (set_tnth (bloomfilter_hashes bf) new_hash_state index) (bloomfilter_state bf), hash_value).


  Definition bloomfilter_update_state (index: 'I_k) (hash_result: Comp [finType of (BloomFilter * 'I_(Hash_size.+1))]) : Comp [finType of BloomFilter] :=
    result <-$ hash_result;
      let: (new_bf, hash_index) := result in
      ret (bloomfilter_set_bit hash_index new_bf).
                                  

  Definition bloomfilter_check_state (hash_result: Comp [finType of (BloomFilter * 'I_(Hash_size.+1))]) : Comp [finType of bool] :=
    result <-$ hash_result;
      let: (new_bf, hash_index) := result in
      ret (bloomfilter_get_bit hash_index new_bf).


  Definition comp_fst (A B : finType) (cmp: Comp [finType of (A * B)]) :=
    result <-$ cmp;
      let: (a,b) := result in
      ret a.

  Definition comp_snd (A B : finType) (cmp: Comp [finType of (A * B)]) :=
    result <-$ cmp;
      let: (a,b) := result in
      ret b.


  Fixpoint bloomfilter_add_internal (value: B) (bf: BloomFilter) (pos: nat) (Hpos: pos < k) : Comp [finType of BloomFilter].
    case Heqpos': pos => [|pos'].
    (* Case 1: pos is 0 *)
        (* then update bitvector and return *)
        move: (bloomfilter_calculate_hash (Ordinal Hpos) value bf) => /(bloomfilter_update_state (Ordinal Hpos)) updated_state.
        exact updated_state.

    (* Case 2: pos is pos.+1 *)
        move: (Hpos); rewrite Heqpos' -(addn1 pos') => /InvMisc.addr_ltn Hpos'.
        (* then update the bitvector*)
        move: (bloomfilter_calculate_hash (Ordinal Hpos) value bf) => /(bloomfilter_update_state (Ordinal Hpos)) updated_state.
        (* and recurse on a smaller argument *)
        exact (@Bind _ _ updated_state
                      (fun new_bf => 
                                       bloomfilter_add_internal value new_bf pos' Hpos'
                      )
               ).
        Qed.

  Search _ (ordinal _).

  Definition try_incr (count: 'I_k) : 'I_k.
        case_eq (count.+1 < k) =>  H.
        exact (Ordinal H).
        exact count.
    Defined.

  Definition bloomfilter_add (value: B) (bf: BloomFilter) : Comp [finType of BloomFilter] :=
    bf <-$ bloomfilter_add_internal value bf Hpredkvld;
      ret (mkBloomFilter
            (try_incr (bloomfilter_cnt bf))
            (bloomfilter_hashes bf)
            (bloomfilter_state  bf)
          ).



  Fixpoint bloomfilter_query_internal (value: B) (bf: BloomFilter) (pos: nat) (Hpos: pos < k) : Comp [finType of bool].
    case Heqpos': pos => [|pos'].
    (* Case 1: pos is 0 *)
        (* then update bitvector and return *)
        move: (bloomfilter_calculate_hash (Ordinal Hpos) value bf) => /bloomfilter_check_state  updated_state.
        exact updated_state.

    (* Case 2: pos is pos.+1 *)
        move: (Hpos); rewrite Heqpos' -(addn1 pos') => /InvMisc.addr_ltn Hpos'.
        (* then update the bitvector*)
        move: (bloomfilter_calculate_hash (Ordinal Hpos) value bf) => updated_state.
        (* and recurse on a smaller argument *)
        exact (@Bind _ _ updated_state
                      (fun updated_state => 
                         let: (new_bf, hash_index) := updated_state in
                         match (bloomfilter_get_bit hash_index new_bf) with
                           true => bloomfilter_query_internal value new_bf pos' Hpos'
                         | false => ret false
                                       
                         end
                      )
               ).
        Qed.



  Definition bloomfilter_query (value: B) (bf: BloomFilter ) : Comp [finType of bool] := bloomfilter_query_internal value bf Hpredkvld.


End BloomFilter.