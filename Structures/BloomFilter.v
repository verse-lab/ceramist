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

  (*
     list of hash functions used in the bloom filter
   *)


  Lemma Hpredkvld: k.-1 < k.
    Proof.
        by  apply InvMisc.ltnn_subS.
    Qed.


  Lemma Hltn_leq pos pos' (Hpos: pos < k) (Hpos': pos = pos'.+1) : pos' < k.
      by  move: (Hpos); rewrite {1}Hpos' -{1}(addn1 pos') => /InvMisc.addr_ltn .
    Qed.  


  Definition trcons A n (xs: n.-tuple A) (x: A) : (n.+1.-tuple A) :=
    match xs as t return (_ <- t; (n.+1).-tuple A) with
    | @Tuple _ _ x0 x1 =>
        (fun (xs0 : seq A) (Hsz : size xs0 == n) =>
            (Hmap <- (fun Hsz0 : size (xs0 <::< x) = n.+1 => Hrxs <- introT eqP Hsz0; Tuple Hrxs);
            eq_rect_r (fun n' : nat => size (xs0 <::< x) = n'.+1 -> (n.+1).-tuple A) Hmap (elimTF eqP Hsz))
            (size_rcons xs0 x))
            x0 x1
    end.


    Fixpoint hash_vec_int (value: hash_keytype) (hashes:  k.-tuple (HashState n))  (pos: nat) (Hpos: pos < k) : Comp [finType of (k.-tuple (HashState n) * (pos.+1.-tuple 'I_(Hash_size.+1)))] :=
      (
        match pos as pos' return (pos = pos' -> Comp [finType of (k.-tuple (HashState n) * ((pos'.+1).-tuple 'I_(Hash_size.+1)))]) with
        | 0 => (fun Hpos': pos = 0 =>
                 (* retrieve the has function *)
                 let hsh_fun := tnth hashes (Ordinal Hkgt0) in
                 (* hash the value *)
                 hash_vl <-$ hash _ value hsh_fun;
                 (* retrieve the updated hash function and its result *)
                 let (new_hsh_fun, result) := hash_vl in
                 (* update the hash vector with the new hash *)
                 let new_hashes := set_tnth hashes new_hsh_fun 0 in
                 ret (new_hashes, [tuple result]))
        | pos'.+1 => (fun Hpos': pos = pos'.+1 =>
                      (* recurse on smaller value to obtain a new sequence of hashes and results *)
                      hash_vl <-$ (hash_vec_int value hashes  (Hltn_leq Hpos Hpos'));
                      let (new_hashes, result_vec) := hash_vl in

                      (* retrieve the pos-th hash function *)
                      let hsh_fun := tnth new_hashes (Ordinal Hpos) in
                      (* hash the value to obtain a result value *)
                      hash_vl <-$ hash _ value hsh_fun;

                      (* retrieve the updated hash function and hash result *)
                      let (new_hsh_fun, result) := hash_vl in
                      (* update the hash state *)
                      let new_hashes := set_tnth new_hashes new_hsh_fun pos in
                      ret (new_hashes, (@trcons _ _ result_vec result))
                    )
        end
      ) (erefl pos).


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
    hash_res <-$ (hash_vec_int value hashes Hpredkvld);
      let (hashes, hash_vec) := hash_res in
      let new_bf := bloomfilter_add_internal (tval hash_vec) bf in
      ret (hashes, new_bf).


  Fixpoint bloomfilter_query_internal (items: seq 'I_(Hash_size.+1)) bf : bool :=
    match items with
      h::t => if bloomfilter_get_bit h bf then
                bloomfilter_query_internal t bf
             else
                false
    | [::]   => true
    end.

  Definition bloomfilter_query (value: hash_keytype) (hashes: k.-tuple (HashState n)) (bf: BloomFilter) : Comp [finType of (k.-tuple (HashState n)) * bool ] :=
    hash_res <-$ (hash_vec_int value hashes Hpredkvld);
      let (hashes, hash_vec) := hash_res in
      let qres := bloomfilter_query_internal (tval hash_vec) bf in
      ret (hashes, qres).

End BloomFilter.