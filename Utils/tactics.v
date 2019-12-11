From mathcomp.ssreflect Require Import
     ssreflect ssrbool ssrnat eqtype fintype
     choice ssrfun seq path bigop finfun binomial.

From mathcomp.ssreflect Require Import tuple.

From mathcomp Require Import path.

From infotheo Require Import
     ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From ProbHash.Computation
     Require Import Comp Notationv1.

From ProbHash.Core
     Require Import Hash HashVec  FixedList  FixedMap.

From ProbHash.Utils
     Require Import InvMisc seq_ext seq_subset rsum_ext stirling.



Lemma eq_rmull (f g x: Rdefinitions.R) :
  f = g -> (f *R* x) = (g *R* x).
Proof. by move=>->. Qed.

Lemma eq_rmulr (f g x: Rdefinitions.R) :
  f = g -> (x *R* f) = (x *R* g).
Proof. by move=>->. Qed.
Lemma cons_tuple_base (A:Type) (a:A) : [tuple a] = cons_tuple a [tuple].
Proof. by rewrite cons_tuple_eq_tuple //=. Qed.


(*
Normalizes a probabilistic computation into a standard form where the steps
of the computation are multiplied together
P[ c1; c2; c3; ...] => \sum ... \sum P[ c1 = x1 ] * P[c2 = x2] ....
 *)
Ltac comp_normalize :=
  match goal with
  | [ |-  context [FDistBind.d _ _  ] ] => rewrite !FDistBind.dE //=; comp_normalize
  | [ |-  context [Uniform.d _  ] ] => rewrite !Uniform.dE //=; comp_normalize
  | [ |- context [FDist1.d _]] => rewrite !FDist1.dE //=; comp_normalize
  | [ |- context [(cons_tuple _ _ )]] => rewrite -cons_tuple_eq_tuple; comp_normalize
  | [ |- context [(_ *R* _)]] => rewrite !(rsum_Rmul_distr_l, rsum_Rmul_distr_r, mulR1, mulR0, mul1R, mul0R) //=; comp_normalize
  | [ |- context [(d[ _ ])] ] => rewrite //= !FDistBind.dE //=; comp_normalize
  | [ |- context [\sum_(_ in _) _]] =>
    rewrite ?( rsum_empty, rsum_split, rsum_Rmul_distr_l, rsum_Rmul_distr_r)
            //=; tryif under eq_bigr => ? ? do idtac then under eq_bigr => ? ? do comp_normalize else comp_normalize
  | [ |- context [(?X1 *R* ?X2)]] => progress (under eq_rmull do comp_normalize);
                                     progress (under eq_rmulr do comp_normalize); comp_normalize
  | [ |- _ ] => idtac
  end.

(* pulls the nth (0-indexed) summation to the outermost point *)
Ltac exchange_big_outwards n :=
  match n with
  |  ?n'.+1 => (under eq_bigr => ? ? do try exchange_big_outwards n'); rewrite exchange_big
  | 0 => idtac
  end.

(* moves the outermost summation to the innermost and then executes tactic f in that context
                                                    b,c
----------------------------------                ----------------------------------
\sum_{a) \sum_{b} \sum_{c} g(a,b,c)        =>      \sum_{a) g(a,b,c)                     => apply f.
 *)
Ltac exchange_big_inwards f :=
  match goal  with
  |  [ |- context [\sum_(_ in _) _ ] ] => rewrite exchange_big //=; under eq_bigr => ? ? do exchange_big_inwards f
  |  [ |- context [\sum_(_ in _) _ ] ] =>  f
  |  [ |- _ ] => fail
  end.

(* applies the provided tactic under all the summations *)
Ltac under_all x :=
  match goal  with
  |  [ |- context [\sum_(_ in _) _ ] ] =>  under eq_bigr => ? ? do (under_all x)
  | _ => x
  end.


(*
Given a summation index, rearranges the goal such that any equalities on the index are brought to the left.
Once in this form, -big_pred_demote can be applied to raise the equality into the summation index,
and big_pred1_eq can then be used to simplify the summation.
 *)
Ltac comp_simplify_eq x :=
  match goal with
  | [ |-  (Under_eq ((_ (x == _) %R) *R* _)) _ ] => idtac
  | [ |-  (((_ (x == _) %R) *R* _)) ] => idtac
  | [ |-  context [(_ (_ == x) %R)] ] => rewrite [_ == x]eq_sym; comp_simplify_eq x
  | [ |- context [(((_ (x == _) %R) *R* _) *R* _)] ] =>
    rewrite -[(((_ (x == _) %R) *R* _) *R* _)]mulRA;
    comp_simplify_eq x
  | [ |- context [(_ *R* ((_ (x == _) %R) *R* _))] ] =>
    rewrite
      [(_ *R* ((_ (x == _) %R) *R* _))]mulRA
      [(_ *R* (_ (x == _) %R))]mulRC
    -[(((_ (x == _) %R) *R* _) *R* _)]mulRA;  comp_simplify_eq x
  | [ |- context [(_ *R* (_ (x == _) %R))] ] =>
    rewrite [(_ *R* (_ (x == _) %R))]mulRC; comp_simplify_eq x
  | [ |- context [(x,_) == (_,_)]] =>
    rewrite [(x,_) == (_,_)]xpair_eqE
            [((x == _) && _  %R)]boolR_distr; comp_simplify_eq x
  | [ |- context [(_,x) == (_,_)]] =>
    rewrite [(_,x) == (_,_)]xpair_eqE
            [(_ && (x == _) %R)]boolR_distr; comp_simplify_eq x
  | [ |- context [(_,_) == (x,_)]] =>
    rewrite [(_,_) == (x,_)]xpair_eqE
            [((_ == x) && _ %R)]boolR_distr; comp_simplify_eq x
  | [ |- context [(_,_) == (_,x)]] =>
    rewrite [(_,_) == (x,_)]xpair_eqE
            [(_ && (_ == x) %R)]boolR_distr; comp_simplify_eq x
  | [ |- context [(cons_tuple _ _)]] =>
    rewrite !(xpair_eqE, xcons_eqE, cons_tuple_eq_tuple, cons_tuple_base, ntuple_cons_eq, ntuple_tailE);
    comp_simplify_eq x
  | [ |- _ ] => fail
  end.

(*
 Recursively attempts to perform probabilistic beta reduction with every summation index in context
 *)
Ltac comp_simplify_internal :=
  match goal with
  | [|- context [\sum_(i in _) _]] =>
    progress (exchange_big_inwards
                ltac:(
                (* once we've moved the summation to the inside *)
                (* move the equalities on the summation index to start of the summand  *)
                under eq_bigr => i _ do comp_simplify_eq i;
                                 (* promote equality on summation index to summation and simplify
                 i.e \sum(i in _) (i == 3 * f(i) ...) =>
                     \sum(i == 3 ) (f(i) ...) =>
                     f(3) ... *)
                                 ((
                                     rewrite -rsum_pred_demote big_pred1_eq //=

                                   ) ||
                                  (* if that failed, it could be because the summation already has some predicate:
                            \sum(i | P i) (i == 3 * f(i) ...)
                           if so, the demote the existing predicate, and retry
                            \sum(i) (P i * i == 3 * f(i) ...)
                                   *)
                                  (
                                    rewrite rsum_pred_demote;
                                    under eq_bigr => i Hi do  comp_simplify_eq i; rewrite -rsum_pred_demote big_pred1_eq //=))
             )) ||
             (
               under eq_bigr => ? ? do progress comp_simplify_internal)
  end.



(*
  Performs beta reduction until no further progress is made
 *)
Ltac comp_simplify :=
  do !(progress comp_simplify_internal).

(*
  Same as comp_simplify, but only runs a fixed number of times
  (sometimes comp_simplify_internal can exchange the order of summands without making progress)
 *)
Ltac comp_simplify_n n :=
  do n!(progress comp_simplify_internal).


(* dispatches 0 <= obligations that arise during proofs *)
Ltac dispatch_eq0_obligations :=
  intros;
  match goal with
  | [|- context [_ *R* _]] => apply RIneq.Rmult_le_pos
  | [|- context [\sum_(_ in _) _]] => apply rsumr_ge0
  | [|- context [#| _ |]] => rewrite card_ord
  | [|- context [_ -<=- _]] => apply fdist_ge0_le1 || apply leR0n || apply prob_invn
  | [|- context [Rdefinitions.Rinv (?x.+1 %R)]] => rewrite -add1n
  end.

