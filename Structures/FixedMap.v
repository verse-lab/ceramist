From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From BloomFilter
Require Import FixedList.
Set Implicit Arguments.

From mathcomp.ssreflect
Require Import tuple.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.




Section fixmap.
    Variable K : eqType.
    Variable V : eqType.


    Definition fixmap n := fixlist [eqType of (K * V)] n.


    Definition fixmap_empty n : fixmap n := 
            (fixlist_empty _ n).


    Fixpoint fixmap_find  (k : K) (n : nat) (map : fixmap n) {struct n} : option V :=
      match n as n0 return (n = n0 -> fixmap n0 -> option V) with
        | 0 => fun (_ :n = 0) (map: fixmap 0) => None
        | n0.+1 => fun (H: n = n0.+1) (map: fixmap n0.+1) =>
                     match ntuple_head map with
                     | Some (k',v') => if k' == k
                                        then Some v'          
                                        else fixmap_find k (ntuple_tail map)
                     | None         => fixmap_find k (ntuple_tail map)
                     end
      end (erefl n) map.
      
        (* case n eqn: H. *)
        (*     exact None. *)
        (* case (ntuple_head map). *)
        (*     move=> [k' v']. *)
        (*     case (k' == k) eqn: H'. *)
        (*         exact (Some v'). *)
        (*         exact (fixmap_find k n0 (ntuple_tail map)). *)
        (*     exact (fixmap_find k n0  (ntuple_tail map)). *)


    Fixpoint fixmap_find_ind'  (acc: nat) (k : K) (n : nat) (map : fixmap n) : option nat.
        case n eqn: H.
            exact None.
        case (ntuple_head map).
            move=> [k' v'].
            case (k' == k) eqn: H'.
                exact (Some acc).
                exact (fixmap_find_ind' acc.+1 k n0 (ntuple_tail map)).
            exact (fixmap_find_ind' acc.+1 k n0  (ntuple_tail map)).
   Defined.

    Definition fixmap_find_ind (k : K) (n : nat) (map : fixmap n) : option nat :=
      fixmap_find_ind' 0 k map.





            

    Fixpoint fixmap_put (k : K) (v : V) (n : nat) (map : fixmap n) {struct n} : fixmap n :=
      match n as n0 return (n = n0 -> fixmap n0 -> fixmap n0) with
         | 0 => fun (_ : n = 0) (map : fixmap 0) => map
         | n0.+1 => fun (Hn: n = n0.+1) (map: fixmap n0.+1) =>
                      match ntuple_head map with
                      | Some (k',v') => if k' == k
                                           then ntuple_cons (Some (k,v)) (ntuple_tail map)
                                           else ntuple_cons (Some (k',v')) (fixmap_put k v (ntuple_tail map))
                      | None         =>  ntuple_cons (Some (k,v)) (ntuple_tail map)
                     end                                                                   
     end (erefl n) map.                

        (* match (fixmap_find_ind k map) with *)
        (*     | None =>  (fixlist_insert map (k,v))  *)
        (*     | Some ind => (fixlist_set_nth map (k,v) ind) *)
        (* end. *)


    Lemma fixmap_find_ind_pred n  (fm : fixmap n) k acc ind  : 
        acc > 0 ->
        fixmap_find_ind' acc k fm = Some ind ->
        fixmap_find_ind' acc.-1 k fm = Some ind.-1.
    Proof.
      move: fm acc ind => [].
      elim: n.
          by move=> [] //=.
      move=> n IHn [//=|x xs] //= Heqn acc ind .
      case: acc => //= acc Hacc.
      rewrite /ntuple_head//=/thead (tnth_nth x) //=.
      case: x => //=.
      move=> [k' v'] //=.
      move: (erefl _).
      case: (_ == _) => //= _.
        by move => [] <- //=.
      rewrite /ntuple_tail //=; move: (behead_tupleP _) => //= Hxseqn /IHn H.
      by apply H.
      rewrite /ntuple_tail //=; move: (behead_tupleP _) => //= Hxseqn /IHn H.
      by apply H.
    Qed.


    Lemma fixmap_find_ind_empty n (fm : fixmap n) k acc : 
              fixlist_is_empty fm ->
              fixmap_find_ind' acc k fm =  None.
    Proof.
      move: fm k acc => []; elim: n => //= n IHn [//=| x xs] //= Heqn k acc.
      case: x => //=.
      rewrite /fixlist_is_empty//= fixlist_coerce_none => Hempty.
      rewrite /ntuple_tail //=; move: (behead_tupleP _) => //= prf'.
      rewrite (proof_irrelevance _ prf' Heqn) => //=.
      by apply IHn => //=.
    Qed.   





End fixmap. 

Section fin_fixmap.
    Variable K : finType.
    Variable V : finType.
    Variable n : nat.

    Definition finmap := fixmap K V n.

    Canonical finmap_of_eqType := Eval hnf in [eqType of finmap].
    Canonical finmap_of_choiceType := Eval hnf in [choiceType of finmap].
    Canonical finmap_of_countType := Eval hnf in [countType of finmap].
    Canonical finmap_of_finType := Eval hnf in [finType of finmap].

End fin_fixmap.

