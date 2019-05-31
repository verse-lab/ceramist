From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun bigop seq path finfun tuple.




(* utility function for ranges of values form (inclusive) a to b (exclusive) *)
Definition itoj (m n : nat) : seq.seq nat :=
  iota m (n - m).

(* Couldn't find a remove_nth function in stdlib or ssreflect*)
Fixpoint rem_nth {A:Type} (n : nat) (ls : list A) : list A := 
    match n with
      | 0 => if ls is h::t then t else nil
      | S n' => if ls is h :: t 
            then h :: (rem_nth n' t)
            else ls
      end.

(*
Example rem_nth_test_1 : rem_nth 0 [:: 1; 2; 3] = [:: 2; 3].
Proof. by []. Qed.

Example rem_nth_test_2 : rem_nth 1 [:: 1; 2; 3] = [:: 1; 3].
Proof. by []. Qed.


Example rem_nth_test_3 : rem_nth 2 [:: 1; 2; 3] = [:: 1; 2].
Proof. by []. Qed.
*)

(* Also couldn't find any utilities for dealing with option types *)
Definition option_cons 
  {A : Type} 
  (self : option A) 
  (list : seq.seq A) : seq.seq A := match self with 
    | Some value => value :: list
    | None => list
  end.

(*Example option_cons_test_1 : option_cons (Some 1) [:: 2; 3] = [:: 1; 2; 3].
Proof. by []. Qed.


Example option_cons_test_2 : option_cons None [:: 2; 3] = [:: 2; 3].
Proof. by []. Qed.*)

Lemma options_cons_some_eq_cons : forall (A : Type) (x : A) (xs : seq.seq A), option_cons (Some x) xs = cons x xs.
Proof.
  by [].
Qed.

Lemma options_cons_none_ident : forall (A : Type) (xs : seq.seq A), option_cons None xs = xs.
Proof.
  by [].
Qed.

Print rem.

Fixpoint prefix {A : eqType} (xs : list A) (ys : list A) :=
  if length xs > length ys 
    then false
    else 
      match ys with
        | [::] => xs == [::]
        | y' :: ys' => if length ys == length xs
              then xs == ys
              else prefix  xs ys'
        end.
    
Example prefix_example_1 : prefix  [:: 1; 2; 3] [:: 4; 5; 1; 2; 3].
Proof. by []. Qed.

Example prefix_example_2 : @prefix _ [:: 1; 2; 3] [:: 1; 2; 3].
Proof. by []. Qed.

Fixpoint all_consecutive_sequences {A} (xs : list A) (l : nat) (p : list A -> bool) :=
  if (length xs) < l
    then true
  else 
    match xs with
      | [::] => true
      | x' :: xs' => p (take l xs) && all_consecutive_sequences xs' l p
      end.


Definition mod_incr (n : nat) (pf: n > 0) (m : 'I_n) : 'I_n. 
  case_eq (m < n)=> H.
  exact (Ordinal H).
  exact (Ordinal pf).
Qed.






Lemma negb_eqn b: b != true -> eq_op b false.
Proof.
  by case b.
Qed.


Lemma length_sizeP (T : Type) (ls : seq.seq T) : size ls = length ls.
Proof.
  by elim ls.
Qed.

Lemma has_countPn (T : Type) (a : pred T) (s : seq T) : ~~ has a s -> count a s = 0.
Proof.
  rewrite has_count.
  by rewrite -eqn0Ngt => /eqP .
Qed.

Lemma ltn_transPn n r : n < r -> r < n.+1 -> False.
Proof.
  elim: n => //= .
  by elim r => //=.
  move=> n IHn.
  move=> Hltn Hltr.
  apply IHn.
  rewrite leq_eqVlt in Hltn.
  move/orP: Hltn => [/eqP <- //=|].
  move/ltn_trans: Hltr => H /H.
  by rewrite ltnn.
  rewrite leq_eqVlt in Hltr.
  move/orP: Hltr => [/eqP [] Hwr|].
  move: Hltn.
  rewrite Hwr.
  by rewrite ltnn.
  rewrite -{1}(addn1 r).
  rewrite -{1}(addn1 n.+1).
  by rewrite ltn_add2r.
Qed.

Lemma subn_eqP n m : n <= m -> n - m = 0.
Proof.
  by rewrite -subn_eq0 => /eqP ->.
Qed.




Lemma ltn1 n : (n < 1)%nat = (n == 0%nat)%bool.
Proof.
  by elim n.
Qed.



Lemma ltnSn_eq a b : (a < b.+1)%nat -> (b < a.+1)%nat -> (a == b)%bool.
Proof.
  move: a.
  induction b => //= a.
  rewrite ltn1.
  by move=>  /eqP -> .
  have H (x y : nat) : (x > 0)%nat -> (x.-1 == y)%bool = (x == y.+1)%bool. by elim x  =>//=.
  case (0 < a)%nat eqn: Hva.
  rewrite -H //=.
  move=> Haltb Hblta.
  apply IHb.
  rewrite -ltnS.
  by rewrite prednK.
  by rewrite prednK.

  move/negP/negP: Hva.
  rewrite -leqNgt.
  rewrite leq_eqVlt.
  rewrite (ltnS b.+1).
  move=>/orP[/eqP ->|].
  by rewrite ltn0.
  by rewrite ltn0.
Qed.

Lemma addr_ltn a b c:
   (a + b < c)%nat -> (a < c)%nat.
Proof.
    by move=>/(ltn_addr b); rewrite ltn_add2r.
Qed.




Lemma ltn_leq_split a b c : (a + b - 1 < c.+1)%nat -> ~~ (b <= c)%nat -> ((b == c.+1)%bool  && (a == 0%nat)%bool).
Proof.
  rewrite -ltnNge.
  case (b) => [|b'].
  by rewrite ltn0.
  rewrite subn1 addnS.
  move=> Hab. move: (Hab).
  have Hltnadn x : (x > 0)%nat -> x.+1.-1 = x.-1.+1. by elim x => //=.
  move=> Habltn; move: Hab; rewrite prednK //=.
  move=> Hab; move: (Hab); rewrite addnC.
  move=> /addr_ltn Hbltc Hcltb.
  move: (ltnSn_eq _ _ Hbltc Hcltb) => /eqP Hbeq; move: Hab.
  rewrite Hbeq -(addn1 c) addnC ltn_add2l ltn1.
  move=>/eqP ->; apply/andP.
  by [].
Qed.


Lemma ltn_SnnP a b : (a.+1 < b.+1)%nat <-> (a < b)%nat.
Proof.
  split.
  by elim: a => //=.
  by elim: a => //=.
Qed.



Lemma subn_ltn_pr a b c : (a < c)%nat -> (a - b < c)%nat.
Proof.
  move: a b.
  elim: c => //= c .
  move=> IHn a b.
  case H: (a < c)%nat.
    move=> _.
    rewrite -(addn1 c).
    apply ltn_addr.
    by apply IHn.
  move/negP/negP: H .
  rewrite -leqNgt .
  rewrite -ltnS.
  move=> /ltnSn_eq H /(H) /eqP Heqa.
  induction a => //=.
  induction b => //=.
  by rewrite -Heqa subn0.
  rewrite subSS.
  rewrite -(addn1 c).
  apply ltn_addr.
  apply IHn.
  by rewrite Heqa.
Qed. 

Lemma ltn_subn_pr a b c : (a < b - c) -> (a < b).
Proof.
  move: a b.
  elim: c=>//= [ a b | c  IHc a b].
  by rewrite subn0.
  rewrite subnS -subn1 subnAC =>/IHc.
  rewrite ltn_subRL addnC addn1.
  case: b => //= b /ltn_SnnP /(ltn_addr 1).
  by rewrite addn1.
Qed.


Lemma leq_subn_pr a b c : (a <= b - c) -> (a <= b).
Proof.
  rewrite {1}leq_eqVlt => /orP [/eqP -> | ].
  by apply leq_subr.
  move=>/ltn_subn_pr Hlt.
  by apply/ltnW.
Qed.



Lemma ltnn_subS n : (n > 0) -> n.-1 < n.
Proof.
    by case n .
Qed.

Lemma ltn_weaken a b c : a + b < c -> a < c.
Proof.
  elim: c => //= c IHc.
  rewrite leq_eqVlt => /orP [/eqP [] <- |].
  rewrite -addnS.
  by elim a => //=.
  rewrite -(addn1 (a + b)).
  rewrite -(addn1 c).
  rewrite ltn_add2r.
  move=>/IHc Hlt.
  by apply ltn_addr.
Qed.


Lemma ltn_subl1 a b : a < b -> a.-1 < b.
Proof.
  move: b.
  elim:a => //= a IHa b.
  by rewrite -{1}(addn1 a) => /ltn_weaken.
Qed.

Lemma ltn_subl a b c : a < b -> a - c < b.
Proof.
  move: a b.
  elim: c => //= [a b | c IHc a b].
  by rewrite subn0.
  move=> /IHc Hlt.
  rewrite subnS.
  by apply ltn_subl1.
Qed.

Lemma ltn_subLR  m n p : ( p > 0) -> (n  < p + m) -> (n - m < p).
Proof.
  move: n p.
  elim: m => [//=|m IHn].
  move=>  n p.
  by rewrite addn0 subn0.
  move=> n p p_vld H.
  rewrite subnS.
  rewrite -subn1.
  rewrite subnAC.
  apply IHn =>//=.
  rewrite addnS  ltnS in H.
  rewrite leq_eqVlt in H.
  move/orP: H => [/eqP ->|].
  by rewrite addnC -addnBA; [rewrite ltn_add2l subn1; apply ltnn_subS|].
  move=> H.
  rewrite subn1.
  by apply ltn_subl1.
Qed.

(* TODO: Move this to somewhere more appropriate *)
Lemma leq_addr_weaken x y z : (x + y <= z)%nat -> (x <= z)%nat.
Proof.
  move: x y.
  elim: z => [ | z IHz x y] //=.
    by move=> [|] //=.
  rewrite {1}leq_eqVlt => /orP [ /eqP <- | ].
  by apply (leq_addr ).
  move=> /IHz Hltxz.
  rewrite -(addn1 z) -(addn0 x).
  by apply leq_add.
Qed.


Lemma subn_eqQ a b : a - b = a -> a = 0 \/ b = 0.
Proof.
  case: a => //= [ | a]. by move=> _; left.
  case Hltn: (b <= a).
  rewrite subSn //= => [] [].
  move=>/(f_equal (fun x => x + b)).
  rewrite addnC.
  rewrite subnKC //=.
  move=>/(f_equal (fun x => x - a)).
  rewrite subnn.
  rewrite addnC.
  by rewrite -addnBA //= subnn addn0 => Hbeqn0; right.
  move/negP/negP: Hltn.
  by rewrite -ltnNge -subn_eq0 => /eqP ->.
Qed.



Lemma addr2n r : (r - 2 < r)%nat \/ (r == (r - 2%nat)%nat)%bool /\ (r == 0%nat)%bool.
Proof.
  elim r=> //.
  by right; rewrite sub0n.
  move=> n [IHn|IHn].
  case (n > 1)%nat eqn: H.
  by left; rewrite subSn; [rewrite -(addn1 (n - 2%nat)) -(addn1 n) ltn_add2r| ].
  move/negP/negP: H.
  rewrite -leqNgt leq_eqVlt.
  by move=>/orP[/eqP -> | ]; [left; rewrite subnn | rewrite ltn1; move=>/eqP ->; left].
  by destruct IHn as [_ Heq0]; move/eqP:Heq0 -> ; left.
Qed.  



Lemma add_lt0 x y: (0 < x + y)%nat = ((0 <x)%nat && (0 <= y)%nat) || ((0 <=x)%nat && (0 < y)%nat).
Proof.
    by induction x => //=.
Qed.


Lemma addn_lt1 x y :  ((x + y)%nat <= 1)%nat -> (((x == 0)) || ((y == 0)))%nat.
Proof.
  by case: x => //= x; case: x => //=; case: y => //=.
Qed.


Lemma iota_predn r s : iota r s.+1 = iota r s ++ [:: r + s].
Proof.
  move: r.
  elim: s => [//=| s IHs   ] r.
  by rewrite addn0.
  rewrite -{1}(addn1 ).
  rewrite iota_add .
  have: (iota (r + s.+1) 1 = [:: r + s.+1]). by [].
  by move=> ->.
Qed.

 
Lemma size_iota_rcons (P : nat -> bool) r s : ~~ P (r + s.-1) -> size (filter P (iota r s)) = size (filter P (iota r s.-1)).
Proof.
  elim: s => [//=|] s' IHs Hs'.
  rewrite iota_predn.
  rewrite -pred_Sn.
  rewrite -pred_Sn in Hs'.
  rewrite filter_cat.
  have: ([seq x <- [:: r + s'] | P x] = [::]).
  move=> //=.
  by apply ifN.
  move=> ->.
  by rewrite cats0.
Qed.

Lemma subn_eq0_eq a b : (a - b == 0) -> (b - a == 0) -> a == b.
Proof.
  move: a; elim: b => //= [a| b IHn a].
  by rewrite subn0 sub0n => /eqP ->.
  rewrite !subn_eq0.
  rewrite leq_eqVlt => /orP [/eqP -> //=| ].
  elim: a => //= a Heqn.
  rewrite -{1}(addn1 a).
  move=> /ltn_weaken.
  by move=>/ltnSn_eq H /H /eqP ->.
Qed.



Lemma leq_exists  a b : a <= b -> exists c, a + c = b.
Proof.
  rewrite leq_eqVlt => /orP [/eqP -> | ]. by exists 0.
  move: a.
  elim: b => //= b IHb a.
  rewrite ltnS leq_eqVlt => /orP [/eqP -> | ]. by exists 1; rewrite addn1.
  by move=> /IHb [c' Heqn]; exists (c'.+1); rewrite addnS Heqn.
Qed.


Lemma addn_ltn_eqn' a b c : a > 0 -> a + c = b -> c < b.

Proof.
  move=> Hgt0a Heqn.
  rewrite -subn_eq0.
  rewrite -Heqn.
  rewrite subnDA.
  rewrite subnAC.
  rewrite subSn //= subnn.
  move: Hgt0a.
  by case a .
Qed.

Lemma ltn_exists a b : a > 0  -> a < b -> exists c, c < b /\ a + c = b.
Proof.
    move: a; elim: b => //= b IHb a Hltn0.
    rewrite leq_eqVlt => /orP [ /eqP [] Heq0 | ].
    by move: Hltn0; rewrite Heq0 => Hlnt0; exists 1; split => //=; rewrite addn1.
    rewrite -{1}(addn1 a) -{1}(addn1 b). rewrite ltn_add2r.
    move=> /IHb Hltn.
    move: (Hltn Hltn0) => [b' [Hb'ltb Hb'eqb]].
    exists (b'.+1); split.
    by rewrite -{1}(addn1 b) -{1}(addn1 b'); rewrite ltn_add2r.
    by rewrite addnS Hb'eqb.
Qed.

Lemma ltn_exists_multi a b : a > 0 -> a < b -> exists c d, c + d = b /\ c < a.
Proof.
  move: a; elim: b => //= b IHb'' a Ha0vld.
  move: (Ha0vld) => /IHb'' IHb' . clear IHb''.
  rewrite leq_eqVlt => /orP [ /eqP [] Haeqb | ].
  rewrite Haeqb.
  rewrite Haeqb in Ha0vld.
  exists b.-1.
  exists 2.
  split; last first.
  by apply ltnn_subS; move: Ha0vld.
  by rewrite addn2 -addn1 prednK //= addn1.
  rewrite -{1}(addn1 a).
  rewrite -{1}(addn1 b).
  rewrite ltn_add2r => /IHb' [c' [d' [Heqn Hlt]]].
  exists c'.
  exists d'.+1.
  by split; [rewrite addnS Heqn | ].
Qed.

Lemma leqn_eq0 a b : a > 0 -> (a <= a - b) -> b == 0 .
Proof.
  move: b.
  case: a => //= a b.
  case: b => //= b _ .
  rewrite subSS.
  move=> /ltn_subn_pr.
  by rewrite ltnn.
Qed.


Lemma nth_set_nth_ident
      (A : Type) (P : pred A) (ls : seq A) (a a' : A) (n : nat) :
  ~~ P a -> ~~ P (nth a ls n) -> ~~ P a' -> length (filter P (set_nth a ls n a'))
                                         = length (filter P ls).
Proof.
  elim: ls n => [n H0 H1 H2| a'' ls n n'] //=.
  rewrite /filter.

  case n => [//=|n0//=]; rewrite ifN.
    by [].
    by [].

  by induction n0 => //=; rewrite ifN.
    by [].

  induction n' => //= H0 H1 H2.
  by rewrite ifN; [rewrite ifN| by []] .
  case_eq (P a'') => H //=.
  by rewrite n.
  by rewrite n.
Qed.

Lemma nth_set_nth_ident_general (A : Type) (P : pred A) (ls : seq A) (a a' : A) (n : nat) :
    n < length ls ->
    P (nth a ls n) == P a' -> 
      length (filter P (set_nth a ls n a')) = length (filter P ls).
Proof.
 
  elim: ls n => [n H0 | a'' ls n n'] //=.

  move=> H0 /eqP H.
  case_eq (P a'') =>  //=.
  move: H H0.
  case_eq n' => //=.
  move=> n0 H H1 H2.
  rewrite ifT.
    by [].
    by rewrite -H H2.
    move=> n0 n0eq H H1 H2.
    rewrite ifT.
    rewrite -(n n0) => //=.
      by rewrite H.
      by [].
  move=> H1.
  move: H.
  case_eq n' => //=.
  move=> H2 H.
  rewrite ifF.
    by [].
    by rewrite -H.
  move=> n0 H2 H.
  rewrite ifN.
  rewrite n => //=.
  by rewrite H2 in H0.
  by rewrite H.
  by rewrite H1.
Qed.

Lemma nth_set_nth_incr (A : Type) (P : pred A) (ls : seq A) (a a' : A) (n : nat):
    n < length ls ->
    P a' ->
    ~~ P (nth a ls n)  -> 
      length (filter P (set_nth a ls n a')) = (length (filter P ls)).+1.
Proof.
  elim: ls n => [n H0 | a'' ls H n' ltnN Pa nPcons] //=.
  move: nPcons.
  case_eq n' => //= n0.
  move=> H1.
  rewrite ifT .
  by rewrite ifN. 
  by [].
  move=> n_eq.
  move=> H1.
  case_eq (P a'') => //= Pa''.
  rewrite H.
  by [].
  rewrite n_eq in ltnN.
  move: ltnN => //=.
  by [].
  by [].
  rewrite H.
  by [].
  rewrite n_eq in ltnN.
  move: ltnN => //=.
  by [].
  by [].
Qed.

   
 Lemma itoj_eq_0 s r : (s < r)%nat -> itoj r s = [::].
  Proof.
    rewrite /itoj; move=> Hsltr.
    have H: ((s - r)%nat = 0%nat). by apply /eqP; rewrite subn_eq0 leq_eqVlt; apply /orP; right.
    rewrite H => //=.
  Qed.




Lemma addn_eq0 a b : (eq_op (a + b)%nat a) -> (eq_op b 0%nat).
Proof.
  move: b.
  by elim: a => //=.
Qed.





(*

   Miscellaneous Real Lemmas

*)


Require Import Reals Fourier FunctionalExtensionality.

From infotheo
Require Import proba ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop .




Lemma Rleq_eqVlt : forall m n : R, (m <= n) <-> (m = n) \/ (m < n).
Proof.
  split.
  move=>/Rle_lt_or_eq_dec.
  by case=> H; [right|left].
  by case=> [/Req_le | /Rlt_le].
Qed.

(* Probably not the best way to do this *)
Lemma R_w_distr (A : finType) (f g : A -> R) :
  (forall w : A, (f w * g w) = 0) -> (forall w : A, (f w) = 0) \/ (exists w : A, (g w) = 0).
  move=> H.
  case ([forall w, f w == 0]) eqn: Hall0.
  by move/eqfunP: Hall0 => Hall; left.
  right.
  apply/exists_eqP.
  move/negP/negP: Hall0.
  rewrite negb_forall=>/existsP [w /eqP Hw].
  by move: (H w) => /Rmult_integral [Hf0 | Hg0]; [move: (Hw Hf0) => [] | apply /exists_eqP; exists w].
Qed.



(* Subtracts a value from an ordinal value returning another value in the ordinal range *)
Definition ordinal_sub {max : nat} (value : 'I_max) (suband : nat) : 'I_max :=
  ssr_have (value - suband < max)%nat
  match value as o return (o - suband < max)%nat with
  | @Ordinal _ m i =>
      (fun Hpft =>  
       (fun Hpf : (Ordinal (n:=max) (m:=m) i < max)%nat =>
          eq_ind_r [eta is_true] Hpft (subn_ltn_pr (Ordinal (n:=max) (m:=m) i) suband max Hpf)))
      is_true_true i
  end [eta Ordinal (n:=max) (m:=value - suband)] .



Lemma Rle_big_eqP (A : finType) (f g : A -> R) (P : pred A) :
   (forall i : A, P i -> f i <= g i) ->
   \rsum_(i | P i) g i = \rsum_(i | P i) f i <->
   (forall i : A, P i -> g i = f i).
Proof.
  move=> hf; split => [/Rle_big_eq H//=|].
    by  exact (H hf).
    move=> H.
      by  exact (@eq_bigr _ _ _ A _ P  g f H).
Qed.


Lemma addRA_rsum  (A : finType) f g : 
  \rsum_(i in A) (f i + g i)%R = (\rsum_(i in A) f i + \rsum_(i in A) g i)%R .
Proof.
  rewrite unlock.
  elim index_enum => //=.
  have H : R0 = 0. (* there's some issues with the types 0 doesn't want to auto-coerce  to R0 *)
    by [].
  move: (addR0   ).
  rewrite /right_id => H'.
  move: (H' R0).
  by rewrite H. 
  move=> x xs IHn.
  by rewrite IHn addRA (addRC (f x) (g x)) -(addRA (g x)) (addRC (g x)) -(addRA (f x + _)).
Qed.
 

Lemma gtRP (a b : R) : reflect (a > b) (a >b b).
Proof.
    by rewrite /gtRb /ltRb; apply: (iffP idP); [case Hrlta: (Rlt_dec b a) | case (Rlt_dec b a) ].
Qed.

Lemma foldl_rcons (T R : Type) (f : R -> T -> R) (b : R) (x : T) (xs : seq.seq T) : foldl f b (rcons xs x ) = f (foldl f b xs ) x. 
Proof.
  by rewrite -cats1 foldl_cat => //=.
Qed.


Lemma  Rmult_integralP   r1 r2 :  (r1 * r2)%R <> 0%R -> r1 <> 0%R /\ r2 <> 0%R .
Proof.
  case Hr1eq0: (eq_op r1 0).
    by move/eqP: Hr1eq0 => ->; rewrite (Rmult_0_l r2) .
  case Hr2eq0: (eq_op r2 0).
    by move/eqP: Hr2eq0 => ->; rewrite (Rmult_0_r r1) .
  by move/eqP: Hr1eq0 => Hr1neq; move/eqP: Hr2eq0 => Hr2neq.
Qed.

