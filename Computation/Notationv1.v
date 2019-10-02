Set Implicit Arguments.

From mathcomp.ssreflect
Require Import ssreflect ssrnat seq ssrbool ssrfun fintype choice eqtype .

From ProbHash.Computation
Require Import Comp.

Lemma size_enum_equiv: forall n: nat, size(enum (ordinal n.+1)) = n.+1 -> #|ordinal_finType n.+1| = n.+1.

Proof.
    move=> n H.
    by rewrite unlock H.
Qed.

Definition random n := (@Rnd (ordinal_finType n.+1) n (size_enum_equiv (size_enum_ord n.+1))).

Notation "'ret' v" := (Ret _ v) (at level 75).
Notation "[0 ... n ]" := (random n).
Notation "{ 0 , 1 } ^ n" := (random (2^n))
    (right associativity, at level 77).
Notation "{ 0 , 1 }" := (random 1) 
    (right associativity, at level 75).
Notation "x <-$ c1 ; c2" := (@Bind _ _ c1 (fun x => c2))
    (right associativity, at level 81, c1 at next level).
Notation "x <- e1 ; e2" := ((fun x => e2) e1)
    (right associativity, at level 81, e1 at next level).
Notation "'P[' a '===' b ']'" := ((evalDist a) b).
Notation "'P[' a ']'" := ((evalDist a) true).
Notation "'E[' a ']'" := (expected_value a).
Notation " a '|>' b " := (w_a <-$ a; b w_a) (at level 50).
Notation " w '>>=' a '<&&>' b " := (fun w => ret (a  && b )) (at level 49).
Notation " w '>>=' a '<||>' b " := (fun w => ret (a || b )) (at level 49).

Definition example :=
    x <- 3;
    y <-$ [0 ... 3];
    ret y.
