From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg finset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Taken from https://github.com/erikmd/coq-bool-games/*)

(* Erik Martin-Dorel, 2016 *)

(** * Tactic for rewriting under bigops *)

(** ** When the bigop appears in the goal *)

(** [under_big] allows one to apply a given tactic under the bigop
    that correspond to the specified arguments. *)
Ltac under_big b i Hi tac :=
  let b' := eval hnf in b in
  match b' with
  | @BigOp.bigop ?R ?I ?idx ?r ?f =>
    match f with
    | fun x => @BigBody ?R ?I x ?op (@?P x) (@?F1 x) =>
      (* erewrite (@eq_bigr R idx op I r P F1 _); (*not robust enough*) *)
      pattern b;
      match goal with
      | [|- ?G b] =>
        refine (@eq_rect_r _ _ G _ b
          (@eq_bigr R idx op I r P F1 _ _ : _ = @BigOp.bigop _ _ _ _ (fun i => _)));
        [|move=> i Hi; tac;
          try reflexivity (* instead of "; first reflexivity" *) ];
        cbv beta
      end
    end
  end.

(** The following tactic can be used to add support for patterns to
tactic notation:
It will search for the first subterm of the goal matching [pat], and
then call [tac] with that subterm.

Inpired by Ralf Jung's post on 2016-02-25 to the ssreflect mailing list.
*)
Ltac find_pat pat tac :=
  match goal with |- context [?x] =>
                  unify pat x with typeclass_instances;
                  tryif tac x then idtac else fail
  end.

(** [under] allows one to apply a given tactic under some bigop:
    if [pat] is a local variable (let-in) that appears in the goal,
    only the occurrences of [pat] will be rewritten;
    otherwise the occurrences of the first bigop that matches [pat]
    will be rewritten. *)
Tactic Notation "under" open_constr(pat) simple_intropattern(i) simple_intropattern(Hi) tactic(tac) :=
  tryif match goal with [|- context [pat]] => is_var pat end
  then under_big pat i Hi tac
  else find_pat pat ltac:(fun b => under_big b i Hi tac).

(** A shortcut when we want to rewrite the first occurrence of [bigop _ _ _] *)
Notation big := (bigop _ _ _) (only parsing).

(** [swap under big ? _ tac] : shortcut for [(under big ? _ tac); last first] *)
Tactic Notation "swap" tactic(tac) :=
  tac; last first.

(** ** When the bigop appears in some hypothesis *)

(** [under_big_in] allows one to apply a given tactic under the bigop
    that correspond to the specified arguments, in some hypothesis *)
Ltac under_big_in H b i Hi tac :=
  let b' := eval hnf in b in
  match b' with
  | @BigOp.bigop ?R ?I ?idx ?r ?f =>
    match f with
    | fun x => @BigBody ?R ?I x ?op (@?P x) (@?F1 x) =>
      (* erewrite (@eq_bigr R idx op I r P F1 _); (*not robust enough*) *)
      pattern b in H;
      match type of H with
      | ?G b =>
        let e := fresh in
        let new := fresh in
        refine (let e := G _ in _);
        shelve_unifiable;
        suff new : e;
        [ try clear H ; try rename new into H
        | refine (@eq_rect _ _ G H _
            (@eq_bigr R idx op I r P F1 _ _ : _ = @BigOp.bigop _ _ _ _ (fun i => _)));
          move=> i Hi; tac;
          try reflexivity (* instead of "; first reflexivity" *)
        ]; try unfold e in * |- *; try clear e ; cbv beta
      end
    end
  end.

Ltac find_pat_in H pat tac :=
  match type of H with context [?x] =>
    unify pat x with typeclass_instances;
    tryif tac x then idtac else fail
  end.

(** [under...in] allows one to apply a given tactic under some bigop:
    if [pat] is a local variable (let-in) that appears in H,
    only the occurrences of [pat] will be rewritten;
    otherwise the occurrences of the first bigop that matches [pat]
    will be rewritten. *)
Tactic Notation "under" open_constr(pat) "in" hyp(H) simple_intropattern(i) simple_intropattern(Hi) tactic(tac) :=
  tryif match type of H with context [pat] => is_var pat end
  then under_big_in H pat i Hi tac
  else find_pat_in H pat ltac:(fun b => under_big_in H b i Hi tac).

(** * Similar material, for the bigop predicates *)

(** ** When the bigop appears in the goal *)

(** [underp_big] allows one to apply a given tactic for rewriting the
    predicate of the bigop corresponding to the specified arguments. *)
Ltac underp_big b i tac :=
  let b' := eval hnf in b in
  match b' with
  | @BigOp.bigop ?R ?I ?idx ?r ?f =>
    match f with
    | fun x => @BigBody ?R ?I x ?op (@?P1 x) (@?F x) =>
      pattern b;
      match goal with
      | [|- ?G b] =>
        refine (@eq_rect_r _ _ G _ b
          (@eq_bigl R idx op I r P1 _ F _ : _ = @BigOp.bigop _ _ _ _ (fun i => _)));
        [|move=> i; tac;
          try reflexivity (* instead of "; first reflexivity" *) ];
        cbv beta
      end
    end
  end.

(** [underp] allows one to apply a given tactic for rewriting
    some bigop predicate:
    if [pat] is a local variable (let-in) that appears in the goal,
    only the occurrences of [pat] will be rewritten;
    otherwise the occurrences of the first bigop that matches [pat]
    will be rewritten. *)
Tactic Notation "underp" open_constr(pat) simple_intropattern(i) tactic(tac) :=
  tryif match goal with [|- context [pat]] => is_var pat end
  then underp_big pat i tac
  else find_pat pat ltac:(fun b => underp_big b i tac).

(** ** When the bigop appears in some hypothesis *)

(** [underp_big_in] allows one to apply a given tactic for rewriting the
    predicate of the bigop corresponding to the specified arguments,
    in some hypothesis *)
Ltac underp_big_in H b i tac :=
  let b' := eval hnf in b in
  match b' with
  | @BigOp.bigop ?R ?I ?idx ?r ?f =>
    match f with
    | fun x => @BigBody ?R ?I x ?op (@?P1 x) (@?F x) =>
      pattern b in H;
      match type of H with
      | ?G b =>
        let e := fresh in
        let new := fresh in
        refine (let e := G _ in _);
        shelve_unifiable;
        suff new : e;
        [ try clear H ; try rename new into H
        | refine (@eq_rect _ _ G H _
            (@eq_bigl R idx op I r P1 _ F _ : _ = @BigOp.bigop _ _ _ _ (fun i => _)));
          move=> i; tac;
          try reflexivity (* instead of "; first reflexivity" *)
        ]; try unfold e in * |- *; try clear e ; cbv beta
      end
    end
  end.

(** [underp...in] allows one to apply a given tactic for rewriting
    some bigop predicate:
    if [pat] is a local variable (let-in) that appears in H,
    only the occurrences of [pat] will be rewritten;
    otherwise the occurrences of the first bigop that matches [pat]
    will be rewritten. *)
Tactic Notation "underp" open_constr(pat) "in" hyp(H) simple_intropattern(i) tactic(tac) :=
  tryif match type of H with context [pat] => is_var pat end
  then underp_big_in H pat i tac
  else find_pat_in H pat ltac:(fun b => underp_big_in H b i tac).


(*
(** * Tests and examples *)

Section Tests.

(* A test lemma covering several testcases. *)
Let test1 (n : nat) (R : ringType) (f1 f2 g : nat -> R) :
  (\big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) =
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) (f1 i * g i) + \big[+%R/0%R]_(i < n) (f2 i * g i))%R.
Proof.
set b1 := {2}(bigop _ _ _).
Fail under b1 x _ rewrite GRing.mulrDr.

under b1 x _ rewrite GRing.mulrDl. (* only b1 is rewritten *)

Undo 1. rewrite /b1.
under b1 x _ rewrite GRing.mulrDl. (* 3 occurrences are rewritten *)

rewrite big_split /=.
by rewrite GRing.addrA.
Qed.

(* A test with a side-condition. *)
Let test2 (n : nat) (R : fieldType) (f : nat -> R) :
  (forall k : 'I_n, f k != 0%R) ->
  (\big[+%R/0%R]_(k < n) (f k / f k) = n%:R)%R.
Proof.
move=> Hneq0.
swap under big ? _ rewrite GRing.divff. (* the bigop variable becomes "i" *)
done.

rewrite big_const cardT /= size_enum_ord /GRing.natmul.
case: {Hneq0} n =>// n.
by rewrite iteropS iterSr GRing.addr0.
Qed.

(* Another test lemma when the bigop appears in some hypothesis *)
Let test3 (n : nat) (R : fieldType) (f : nat -> R) :
  (forall k : 'I_n, f k != 0%R) ->
  (\big[+%R/0%R]_(k < n) (f k / f k) +
  \big[+%R/0%R]_(k < n) (f k / f k) = n%:R + n%:R)%R -> True.
Proof.
move=> Hneq0 H.
set b1 := {2}big in H.
under b1 in H ? _ rewrite GRing.divff. (* only b1 is rewritten *)
done.

Undo 2.
move: H.
under b1 ? _ rewrite GRing.divff.
done.

done.
Qed.

(* A test lemma for [underp] *)
Let testp1 (A : finType) (n : nat) (F : A -> nat) :
  \big[addn/O]_(0 <= k < n)
  \big[addn/O]_(J in {set A} | #|J :&: [set: A]| == k)
  \big[addn/O]_(j in J) F j >= 0.
Proof.
under big k _ underp big J rewrite setIT. (* the bigop variables are kept *)
done.
Qed.

(* A test lemma for [underp...in] *)
Let testp2 (A : finType) (n : nat) (F : A -> nat) :
  \big[addn/O]_(J in {set A} | #|J :&: [set: A]| == 1)
  \big[addn/O]_(j in J) F j = \big[addn/O]_(j in A) F j -> True.
Proof.
move=> H.
underp big in H J rewrite setIT. (* the bigop variable "J" is kept *)
done.
Qed.

End Tests.
 *)
