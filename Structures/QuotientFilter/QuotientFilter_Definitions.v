From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path bigop finfun div.

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From ProbHash.Computation
     Require Import Comp Notationv1.

From ProbHash.Core
     Require Import Hash HashVec FixedList.


Module Type QuotientFilterSpec.

  (*
   q - the number of elements in the quotient - 1
   *)
  Parameter q:nat.
  (*
   r - the number of elements in the remainder - 1
  *)
  Parameter  r:nat.
  (*
   n - maximum number of elements a single fingerprint can hold
  *)
  Parameter  n:nat.

  (* type being hashed in the quotient filter *)
  Parameter  B:finType.

End QuotientFilterSpec.

Module QuotientFilterDefinitions (Spec: QuotientFilterSpec).

  (*
   A fomalization of a simplified form of the quotientfilter structure.
  *)

  Export Spec.
  Module QuotientHash <: HashSpec.

    Definition B := B.

    Definition Hash_size := (q.+1 * r.+1).-1.

    Lemma Hash_size_unwrap : Hash_size = (q.+1 * r.+1).-1.
    Proof. by []. Qed.

  End QuotientHash.

  Module HashVec := (HashVec QuotientHash).

  Export HashVec.


  Definition hash_value_coerce (value: hash_valuetype) : 'I_(q.+1 * r.+1).
      move: value; rewrite/hash_valuetype Hash_size_unwrap //=.
  Defined.

  Lemma hash_value_coerce_eq x y: (hash_value_coerce x) = (hash_value_coerce y) -> x = y.
  Proof.
    rewrite/hash_value_coerce/eq_rect_r.
    by rewrite -eq_rect_eq.
  Qed.
  

  Record QuotientFilter := mkQuotientFilter
                             {
                               quotientfilter_state:
                               (* maps each quotient value *)
                                 (q.+1).-tuple
                                 (* to a variable length list of values *)
                                       (fixlist [eqType of 'I_r.+1] n.+1)
                             }.
  
  Definition Quotientfilter_prod (bf: QuotientFilter) :=
    (quotientfilter_state bf).

  Definition prod_Quotientfilter  pair := let: (state) := pair in @ mkQuotientFilter state.

  Lemma quotientfilter_cancel : cancel (Quotientfilter_prod) (prod_Quotientfilter).
  Proof.
      by case.
  Qed.

  Definition quotientfilter_eqMixin :=
    CanEqMixin quotientfilter_cancel .

  Canonical quotientfilter_eqType  :=
    Eval hnf in EqType QuotientFilter  quotientfilter_eqMixin .

  Definition quotientfilter_choiceMixin :=
    CanChoiceMixin quotientfilter_cancel.

  Canonical quotientfilter_choiceType  :=
    Eval hnf in ChoiceType QuotientFilter  quotientfilter_choiceMixin.

  Definition quotientfilter_countMixin :=
    CanCountMixin quotientfilter_cancel.

  Canonical quotientfilter_countType :=
    Eval hnf in CountType QuotientFilter  quotientfilter_countMixin.

  Definition quotientfilter_finMixin :=
    CanFinMixin quotientfilter_cancel .

  Canonical quotientfilter_finType :=
    Eval hnf in FinType QuotientFilter  quotientfilter_finMixin.


  Definition quotientfilter_new : QuotientFilter :=
    mkQuotientFilter (nseq_tuple q.+1 (fixlist_empty [eqType of 'I_r.+1] n.+1)).

  Lemma quotient_num_quotient (value: 'I_(q.+1 * r.+1)) : (value %% q.+1 < q.+1).
  Proof.
    move: value => [m Hm] //=.
    by apply ltn_pmod.
  Qed.
  
  Lemma quotient_num_remainder (value: 'I_(q.+1 * r.+1)) : (value %/ q.+1 < r.+1).
  Proof.
    move: value => [m Hm] //=.
    by rewrite ltn_divLR //= mulnC.
  Qed.
    

  Definition quotient_num (value: 'I_(q.+1 * r.+1)) : 'I_q.+1 * 'I_r.+1 :=
    (Ordinal (quotient_num_quotient value),
    Ordinal (quotient_num_remainder value)).

  Lemma quotient_num_inj value value':
    quotient_num value = quotient_num value' -> value = value'.
  Proof.
    move: value value' => [value Hvalue] [value' Hvalue'] //=.
    move=> [Hq Hr] //=.
    suff H: value = value'.
    by move: H Hvalue Hvalue' -> => H1 H2;rewrite (proof_irrelevance _ H1 H2).
    rewrite (divn_eq value q.+1).
    rewrite Hr Hq.
    by rewrite -(divn_eq value' q.+1).
  Qed.


  
  Definition quotientfilter_add_internal (value: 'I_(q.+1 * r.+1)) qf : QuotientFilter :=
    let: (quotient,remainder) := quotient_num value in
    let quotient_list := tnth (quotientfilter_state qf) quotient in
    let quotient_list' := fixlist_insert quotient_list remainder in
    mkQuotientFilter
      (set_tnth (quotientfilter_state qf) quotient_list' quotient).


  Definition quotientfilter_add (value: hash_keytype) (hashes: HashState n) (qf: QuotientFilter) :
    Comp [finType of HashState n * QuotientFilter ] :=
    hash_res <-$ (@hash _ value hashes);
      let (new_hashes, hash_vec) := hash_res in
      let qres := quotientfilter_add_internal (hash_value_coerce hash_vec) qf in
      ret (new_hashes, qres).

  Definition quotientfilter_add_multiple  hsh_0 bf_0 values :=
    @foldr _ (Comp [finType of  HashState n * QuotientFilter])
           (fun val hsh_bf =>
              res_1 <-$ hsh_bf;
                let (hsh, bf) := res_1 in
                quotientfilter_add val hsh bf) (ret (hsh_0, bf_0)) values.
  
  Definition quotientfilter_query_internal (value: 'I_(q.+1 * r.+1)) qf : bool :=
    let: (quotient,remainder) := quotient_num value in
    let quotient_list := tnth (quotientfilter_state qf) quotient in
    fixlist_contains remainder quotient_list.

  Definition quotientfilter_query (value: hash_keytype) (hashes: HashState n) (qf: QuotientFilter) :
    Comp [finType of HashState n * bool ] :=
    hash_res <-$ (@hash _ value hashes);
      let (new_hashes, hash_vec) := hash_res in
      let qres := quotientfilter_query_internal (hash_value_coerce hash_vec) qf in
      ret (new_hashes, qres).

  Definition quotientfilter_has_free_spaces l qf :=
    all (fun ls => [length ls] + l <= n ) (quotientfilter_state qf).

  Definition quotientfilter_valid  qf :=
    all (fun ls => fixlist_is_top_heavy ls) (quotientfilter_state qf).

  Lemma fixlist_length_empty (A:eqType) k :
        [length (fixlist_empty A k)] = 0.
  Proof.
    rewrite/fixlist_length/fixlist_empty/fixlist_unwrap //=.
    elim: k => [//=|k IHk //=].
  Qed.
  
    
  Section Theorems.

    Variable l: nat.
    Hypothesis Hl: l > 0.

    Lemma quotientfilter_new_free_spaces :
      quotientfilter_has_free_spaces n (quotientfilter_new).
    Proof.
      rewrite/quotientfilter_has_free_spaces/quotientfilter_new.
      apply/allP => ls; move=>/nseqP [Hls1 Hls2].
      by rewrite Hls1 fixlist_length_empty add0n leqnn.
    Qed.

    Lemma quotientfilter_new_valid :
      quotientfilter_valid (quotientfilter_new).
    Proof.
      rewrite/quotientfilter_has_free_spaces/quotientfilter_new.
      apply/allP => ls; move=>/nseqP [Hls1 Hls2].
      rewrite Hls1.
      apply fixlist_empty_is_top_heavy.
    Qed.

    

    Lemma quotientfilter_add_query_base qf value:
      quotientfilter_valid qf ->
      quotientfilter_has_free_spaces l qf ->
      quotientfilter_query_internal value (quotientfilter_add_internal value qf).
    Proof.
      move: qf => [qf]//=; rewrite/quotientfilter_valid/quotientfilter_has_free_spaces
      => /allP Hvalid  /allP //=  Hall.
      rewrite /quotientfilter_query_internal/quotientfilter_add_internal //.
      move: (quotient_num value) => [quotient remainder] //.
      rewrite tnth_set_nth_eq //.
      apply fixlist_insert_contains; [ apply Hvalid; apply mem_tnth| ].
      move: (Hall _ (mem_tnth quotient qf)); rewrite -ltnS.
      move=>/InvMisc.addr_ltn //=.
    Qed.
    
    Lemma quotientfilter_add_preserve qf qf' value:
      quotientfilter_valid qf ->
      quotientfilter_has_free_spaces l qf ->
      qf' = (quotientfilter_add_internal value qf) ->
      quotientfilter_valid qf' && quotientfilter_has_free_spaces l.-1 qf'.
    Proof.
      move: qf qf' => [qf] //= [qf']//=; rewrite/quotientfilter_valid/quotientfilter_has_free_spaces
      => /allP Hvalid /allP Hall.
      rewrite/quotientfilter_add_internal; move: (quotient_num _) => [quotient remainder].
      move=>/eqP; rewrite inj_eq; last by (rewrite /injective => x y Hxy; injection Hxy).
      move=>/eqP ->.
      have Hsim x: quotientfilter_state ({| quotientfilter_state := x |}) = x; first by [].
      rewrite !Hsim; clear Hsim.
      apply/andP;split; apply/all_tnthP
      => ind; case Heq: (ind == quotient); 
           try (move/Bool.negb_true_iff: Heq => Heq; rewrite tnth_set_nth_neq; last by []);
           try (rewrite tnth_set_nth_eq; last by[]);
           try apply fixlist_insert_preserves_top_heavy;
      try (by apply Hvalid; apply mem_tnth).
      rewrite fixlist_insert_length_incr.
      rewrite matrix.mx'_cast; last by move: (Ordinal Hl).
      rewrite addSn //=; apply Hall; apply mem_tnth.
      move: (Hall _ (mem_tnth quotient qf)); rewrite -ltnS => /InvMisc.addr_ltn //=.
      rewrite matrix.mx'_cast; last (by move: (Ordinal Hl)); rewrite -ltnS.
      apply InvMisc.ltn_subl1; apply Hall; apply mem_tnth.
    Qed.

    Lemma quotientfilter_add_query_preserve qf value value' :
      quotientfilter_query_internal value qf ->
      quotientfilter_query_internal value (quotientfilter_add_internal value' qf).
    Proof.
      move: qf => [qf].
      rewrite /quotientfilter_query_internal; move: (quotient_num value) => [quotient remainder].
      rewrite /fixlist_contains; move=> /hasP [val Hval Hvaleq].
      rewrite /quotientfilter_add_internal.
      move: (quotient_num value') => [quotient' remainder'].
      have Hsim x: quotientfilter_state ({| quotientfilter_state := x |}) = x; first by [].
      move: Hval; rewrite !Hsim; clear Hsim => Hval.
      case Hquoteient_eq: (quotient' == quotient); last first.
      - {
          apply/hasP; exists remainder; last by [].
          rewrite tnth_set_nth_neq; first by move: Hval; move/eqP: Hvaleq => -> .
          by move/Bool.negb_true_iff: Hquoteient_eq; rewrite eq_sym.
        }
      - {
          rewrite tnth_set_nth_eq; last by rewrite eq_sym.
          rewrite fixlist_has_eq; apply/orP; left; apply/hasP; exists remainder; last by [].
          by move/eqP: Hvaleq Hval => ->; move/eqP:Hquoteient_eq ->.
        }
    Qed.
    
    Lemma quotientfilter_add_query_eq qf value value' :
      ~~ quotientfilter_query_internal value qf ->
      quotientfilter_query_internal value (quotientfilter_add_internal value' qf) ->
      value = value'.
    Proof.
      rewrite /quotientfilter_query_internal.
      case Hvalue: (value == value'); rewrite /quotientfilter_add_internal; first by move/eqP:Hvalue <-.
      case_eq (quotient_num value) => [quotient remainder] Heq.
      move=>Hneq.
      have Hsim x: quotientfilter_state ({| quotientfilter_state := x |}) = x; first by [].
      case_eq (quotient_num value') => [quotient' remainder'] Heq'.
      rewrite !Hsim; clear Hsim.
      case Hquot: (quotient == quotient').
      - {
          rewrite tnth_set_nth_eq; last  by[].
          move/eqP:Hquot => Hquot.
          move/Bool.negb_true_iff: Hneq .
          rewrite /fixlist_contains.
          rewrite fixlist_has_eq Hquot.
          move=>  ->; rewrite Bool.orb_false_l =>/andP[/eqP Hrem]/andP[_ _].
          apply quotient_num_inj.
          by rewrite Heq Heq' //= -Hquot Hrem.
        }
      - {
          rewrite tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hquot.
          by move/Bool.negb_true_iff: Hneq ->.
        }
    Qed.

    End Theorems.

End QuotientFilterDefinitions.




