(** *  Comp.v
-----------------
Defines an data type encoding of the syntax of a probabilistic computation,
and provides operations to evaluate such computations into the distribution
type defined by the infotheo library.
*)
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype bigop fintype choice.

Require Import Reals Fourier FunctionalExtensionality.

From infotheo
Require Import fdist proba pproba ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop .

Require Import Nsatz.
Require Import Bvector.


Set Implicit Arguments.

(** convenience wrapper around infotheo's finite distribution type   *)
Definition dist A := fdist A.

(** Probabilistic Computation Monad - based on FCF's Computation Monad *)
Section Comp.

    (** Data type encoding the syntax of a probabilistic computation  *)
    Inductive Comp : finType -> Type :=
        | Ret : forall (A : finType) (a : A), Comp A 
        | Bind : forall (A B : finType), Comp B -> (B -> Comp A) -> Comp A
        | Rnd : forall (A : finType) (n : nat) (n_valid : #|A| = n.+1), Comp A.

    (** Deprecated function to retrieve the support of a probabilistic computation.
       `enum (evalDist p)` should be used instead *)
    Fixpoint getSupport(A : finType) (c : Comp A) : list A :=
        match c with
            | Ret _ a => [:: a]
            | Bind _ _ c1 c2 => 
            (flatten 
                (map 
                    (fun b => (getSupport (c2 b)))
                    (getSupport c1)
                )
            )
            (* | Repeat _ c P => (filter P (getSupport c)) *)
            | Rnd A n _ => (flatten (map (fun x => match pickle_inv x with 
                                                        | Some value => [:: value]
                                                        | None => [::]
                                                        end) (index_iota 0 n.+1)))
        end.

    (** Evaluates a syntactical encoding of a probabilistic
    computation into Infotheo's probability monad *)
    Fixpoint evalDist(A : finType) (c : Comp A) : dist A :=
        match c with
            | Ret _ a => FDist1.d a  (* Dist1 is a distribution of 1 or 0 if eq a*)
            | Bind _ _ c f => FDistBind.d (evalDist c) (fun b => evalDist (f b))
            | Rnd _ n n_valid => Uniform.d n_valid
            end.

    (** Unused operations to determine the expected value of a
    probabilistic computation *)
    Section expected_value.
            Variable n : nat.
            Definition expected_value (c : Comp (ordinal_finType n)) : R:= (Ex (evalDist c) INR).
    End expected_value.

End Comp.
