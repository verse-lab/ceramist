From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path bigop finfun binomial.

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path .

From infotheo
     Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From BloomFilter
     Require Import Parameters Hash Comp Notationv1 BitVector BloomFilter InvMisc bigop_tactics.

(*
Proof idea
----------

1. if hashstate_find value hash_state is None, then the output of the hash function is uniformly distributed from 0..Hash_size.+1
2. folding on a list of values such that all the values are not-equal ensures that hashstate_find value is always None
3. after insert, probability of all hash functions not setting a bit is (1 - 1/(Hash_size.+1))^k.
4. after k inserts,  probability of all hash functions not setting a bit is (1 - 1/(Hash_size.+1))^kn.
5. after k inserts,  probability of all hash functions setting a bit is 1 - (1 - 1/(Hash_size.+1))^kn.



 *)






Ltac dispatch_Rgt :=  do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size).


Lemma ntuple_tail_consP n A (ls: n.-tuple A) val : (FixedList.ntuple_tail (FixedList.ntuple_cons val ls)) = ls.
Proof.
  rewrite /FixedList.ntuple_tail/FixedList.ntuple_cons//=.
  case: ls => [ls Hls]; move: (behead_tupleP _) =>//= Hls'.
  by rewrite (proof_irrelevance _ Hls Hls').
Qed.

Lemma   beheadE (E: eqType) (m: nat) (x: E) (xs: (m.-tuple E)):
  behead_tuple [tuple of x :: xs] = xs.
Proof.
  case: xs => xs Hxs; rewrite /behead_tuple; move: (behead_tupleP _) => //= Hxs'.
  by rewrite (proof_irrelevance _ Hxs Hxs').
Qed.  


Lemma ntuple_head_consP n A (ls: n.-tuple A) val : (thead (FixedList.ntuple_cons val ls)) = val.
Proof.
  rewrite /FixedList.ntuple_tail/FixedList.ntuple_cons//=.
  by case: ls => [ls Hls]; move: (eq_ind _ _ _ ) =>//= Hls'.
Qed.


Lemma fixmap_find_neq
          (K V : eqType) (n : nat) (map : FixedMap.fixmap K V n)
          (x y : K) (v: V):
      (x != y) ->
      (FixedMap.fixmap_find x map == None) ->
      (FixedMap.fixmap_find x (FixedMap.fixmap_put y v map) == None).
Proof.
  elim: n map x y v => [//=|n IHn] [[//=|m ms] Hmap] x y v Hneq /eqP Hz.
  apply/eqP; move: Hz; move=> //=.
  rewrite/FixedList.ntuple_head //=.
  have: thead (Tuple Hmap) = m. by []. move=>->.
  case: m Hmap => [[k' v']|] Hmap //=.
  case Hk': (k' == x) => //=.
  - case: (k' == y) => //=.
      - move/Bool.negb_true_iff: Hneq; rewrite (eq_sym y) => -> //=.
        move: Hmap (eq_ind _ _ _ _ _) => //= Hmap Hmap'.
        rewrite (proof_irrelevance _  Hmap' Hmap);   move=> <- //=.
        rewrite/FixedList.ntuple_tail; move: (behead_tupleP _) (behead_tupleP _) => //= H1 H2.
          by rewrite (proof_irrelevance _ H1 H2).
      -  by rewrite ntuple_head_consP Hk' ntuple_tail_consP => /eqP/(IHn _ _ _ _ Hneq)/eqP; apply.
   - rewrite eq_sym; move/Bool.negb_true_iff: (Hneq) ->.

     move: Hmap (eq_ind _ _ _ _ _) => //=Hmap Hmap'.
     rewrite (proof_irrelevance _ Hmap Hmap') /FixedList.ntuple_tail//=.
     move: (behead_tupleP _) (behead_tupleP _) => //= H H'.
     by rewrite (proof_irrelevance _ H H'). 
Qed.



Notation "a '/R/' b " := (Rdefinitions.Rdiv a b) (at level 70).
Notation "a '+R+' b " := (Rdefinitions.Rplus a b) (at level 70).
Notation "a '*R*' b " := (Rdefinitions.Rmult a b) (at level 70).
Notation "a '-R-' b " := (Rdefinitions.Rminus a b) (at level 70).
Notation "a '-<-' b " := (Rdefinitions.Rlt a b) (at level 70).
Notation "a '-<=-' b " := (Rdefinitions.Rle a b) (at level 70).
Notation "a '->-' b " := (Rdefinitions.Rgt a b) (at level 70).
Notation "a '->=-' b " := (Rdefinitions.Rge a b) (at level 70).
Reserved Notation "a '^R^' b"  (at level 70).
Notation "a '%R' " := (Raxioms.INR a) (at level 70).
Notation "d[ a ]" := (evalDist a) (at level 70).
Definition Reals := Rdefinitions.R.



(* We'll use the definition of rpower for natural numbers as
   coq's Rpower doesn't support raising 0 to a power  *)
Notation "a '^R^' b" := (Rpow_def.pow a b).

Coercion BinInt.Z.of_nat : nat >-> BinNums.Z.
Coercion Rdefinitions.IZR : BinNums.Z >-> Rdefinitions.R.



Definition stirling_no_2 (kn i: nat):=
  Rdefinitions.Rinv (Factorial.fact i) *R* (
    \rsum_(j in 'I_i) (((Rdefinitions.Ropp 1) ^R^ j) *R*
                       ('C (i, j) %R) *R*
                       ((j %R) ^R^ kn)
                      )
  ).


Axiom second_stirling_number_sum: forall l k m (f: nat -> Rdefinitions.R),
    \rsum_(inds in [finType of (l * k).-tuple 'I_m.+1])
     ((Rdefinitions.Rinv (m.+1 %R) ^R^ l * k) *R*
      (f (length (undup inds)))) =
    \rsum_(len in 'I_(l * k))
     (f(len) *R*
      ( ('C ((l * k), len) %R) *R*
        (Factorial.fact len %R) *R* (stirling_no_2 (l * k) len) *R*
        (Rdefinitions.Rinv (m.+1 %R) ^R^ (l * k))
     )).









Lemma distbind_dist (A B C: finType) (a : dist A) (c : A -> B) (g: B -> dist C)  :
      DistBind.d a (fun x => DistBind.d (@Dist1.d _ (c x)) g) = DistBind.d a (fun x =>  g (c x) ).
  Proof.
    rewrite (functional_extensionality (fun x : A => DistBind.d (Dist1.d (c x)) g) (fun x : A => g (c x))) => //= x.
    by rewrite DistBind1f.
Qed.



Lemma prsumr_eq1P :
forall (pr : dist [finType of bool]),
 pr true = (0 %R) <-> pr false = (1 %R).
Proof.
  rewrite !RIneq.INR_IZR_INZ //=.
  move=> [[f Hposf] Hdist].
  split => //=.
  move=> Htrue0.
  move: Hdist.
  rewrite unlock; rewrite /index_enum/[finType of bool]//=.
  by rewrite unlock //= Htrue0 Raxioms.Rplus_comm !RIneq.Rplus_0_r => /eqP.
  move=> Hfalse1.
  move: Hdist.

  rewrite unlock; rewrite /index_enum/[finType of bool]//=.
  rewrite unlock; rewrite /index_enum//=.
  rewrite Hfalse1 addR0.
  by move => /eqP/subR_eq0 //=; rewrite -subRBA subRR RIneq.Rminus_0_r.
Qed.



Lemma prsumr_neg1 (A:finType) (pr : Comp A) (f: A -> bool) :
  (1  -R- (d[ res <-$ pr; ret ~~ (f res) ]) true) =
  (d[ res <-$ pr; ret  (f res) ]) true.
Proof.
  rewrite //= -(epmf1 ((d[ pr]) ) ) !DistBind.dE.
  apply subR_eq;  rewrite -addRA_rsum; apply eq_bigr => a _.
  rewrite mulRC [((d[ pr]) a *R* _)]mulRC -RIneq.Rmult_plus_distr_r !Dist1.dE.
  rewrite -{1}(mulR1 (_ a)); apply Logic.eq_sym; rewrite mulRC; apply f_equal.
  by case: (f a) => //=; rewrite ?addR0 ?add0R.
Qed.


Lemma prsum_nge0p {A: finType}  f : 
  (forall a : A, 0 -<=- f a) -> (forall a : A, ~ (f a  ->- (0 %R))) -> (forall a, f a = (0 %R)).
Proof.
  move=> Hdist Hngt a; move/RIneq.Rnot_gt_le: (Hngt a) (Hdist a).
  by move=>/RIneq.Rle_antisym H /H.
Qed.

Lemma prsumr_ge0 (A : finType) (f: A -> Rdefinitions.R) : (forall a : A, (0 -<=- f a)) -> \rsum_(a in A) f a <> (0 %R) <-> (exists a,  f a ->- (0 %R)).
Proof.
  have HforalleqP : (forall x, f x = (0 %R)) -> (forall x, (fun _ => true) x -> f x = (0 %R)). by [].
  have HforallgtP : (forall x, 0 -<=- f x) -> (forall x, (fun _ => true) x -> 0 -<=- f x). by [].
  move=> Hgt0.
  split.
  - move=>/eqP/negP Rsumr0.
    case Heq0: (~~ [exists a, (gtRb (f a) (0 %R))]).
    move/negP/negP:Heq0 => Heq0.
    rewrite negb_exists in Heq0.
    have Hforalleq: (forall x, ~~ (geRb (f x)  (0 %R))) -> (forall x, ~ (geRb (f x) 0)).
      by move=> Hb x; move/negP: (Hb x) => Hbool //=.
      move/forallP: Heq0 => Heq0.
      have: (forall x:A, ~ (f x) ->- 0).
        by move=> x; apply/gtRP.
        move/(prsum_nge0p Hgt0) => H.

      have: False.  
         apply Rsumr0; apply/eqP.
         transitivity (\rsum_(a in A) (0 %R)).
           by apply eq_bigr=> a _; rewrite H.
         by rewrite (bigsum_card_constE A) mulR0.
      by [].
      by move/negP/negP/existsP: Heq0 => [x Hx]; split with x;  move/gtRP: Hx.
      move=>[a  Ha].
      move=>/prsumr_eq0P H.
      have: (forall a: A, a \in A -> 0 -<=- f a); first by move=> a' _; apply Hgt0.
      by move=>/H H'; move: Ha; rewrite H' //= => /RIneq.Rgt_irrefl.
Qed.



Lemma evalDistBinv (p: Comp [finType of bool]) :
  evalDist p true = (1 %R) <-> evalDist (x <-$ p; ret ~~ x) true = (0 %R).
Proof.
  split=>//=.
  case: (evalDist p).
  move=> pmf Hpmf //= HpmfT.
  rewrite /DistBind.d; unlock; rewrite/DistBind.f//= ffunE.
  apply prsumr_eq0P.
  move=> [] Hb.
  - rewrite HpmfT; move: (RIneq.Rmult_ne ((Dist1.d (~~ true)) true)) => [H ->] //=.
      by rewrite Dist1.dE//=; apply RIneq.pos_INR.
  - have: (pmf false = (0 %R)).
    move: Hpmf; rewrite unlock; rewrite/index_enum/[finType of bool]//=;
                                       rewrite unlock; rewrite /index_enum//= HpmfT addR0 addRC.
      by rewrite eq_sym; move=>/eqP; rewrite -subR_eq//= subRR => <- //=.
  - by move=> ->; rewrite RIneq.Rmult_0_l; apply RIneq.Rle_refl.

    move=> [] Hb //=.
  - rewrite HpmfT; move: (RIneq.Rmult_ne ((Dist1.d false) true)) => [_ ->] //=.
      by rewrite Dist1.dE//=.
  - have: (pmf false = (0 %R)).  
    move: Hpmf; rewrite unlock; rewrite/index_enum/[finType of bool]//=;
                                       rewrite unlock; rewrite /index_enum//= HpmfT addR0 addRC.
      by rewrite eq_sym; move=>/eqP; rewrite -subR_eq//= subRR => <- //=.
  - by move=> ->; rewrite RIneq.Rmult_0_l. 

    case: (evalDist p).
    move=> pmf  //=.
    rewrite /DistBind.d; unlock; rewrite/DistBind.f//= ffunE.

    rewrite unlock; rewrite /index_enum/[finType of bool]//=;
                            rewrite unlock; rewrite /index_enum//=.
    rewrite  !Dist1.dE !addR0 mulR0 add0R mulR1 //= => H1 H2.
      by move: H1; rewrite H2 addR0 =>/eqP ->.

Qed.

Lemma prsum_multeq0 (A B: finType) (pr1 :  A -> Rdefinitions.R) (pr2 : B -> Rdefinitions.R):
  (forall (a : A) (b: B), (pr1 a) *R* (pr2 b) = Rdefinitions.IZR 0) ->
  (\rsum_(a in A) (pr1 a) *R* \rsum_(b in B) (pr2 b)) = Rdefinitions.IZR 0.
  move=> H1.
  rewrite unlock; rewrite /index_enum/reducebig//=.
  elim: (Finite.enum _) => //=; first by rewrite mul0R.
  elim: (Finite.enum _) => [x xs Hxs |] //=; first by rewrite mulR0.
  move=> y ys Hxs x xs Hys.
  rewrite RIneq.Rmult_plus_distr_r Hys addR0 Raxioms.Rmult_plus_distr_l H1 add0R.
    by move: (Hxs x [::]) => //=; rewrite mul0R addR0 => ->.
Qed.

(* There must be some lemma I'm missing for the following: *)
Lemma rsum_Rmul_distr_l (A: finType) (pr: A -> Rdefinitions.R) x :
  x *R* \rsum_(a in A) (pr a) = \rsum_(a in A) (x *R* (pr a)).
Proof.
  rewrite unlock => //=; elim: (index_enum _) x => [x|] //=; first by rewrite mulR0.
  move=> y ys Hys x.
    by rewrite Raxioms.Rmult_plus_distr_l; apply f_equal; rewrite Hys. 
Qed.

Lemma rsum_Rmul_distr_r (A: finType) (pr: A -> Rdefinitions.R) x :
  \rsum_(a in A) (pr a) *R*  x  = \rsum_(a in A) (x *R* (pr a)).
Proof.
    by rewrite mulRC rsum_Rmul_distr_l.
Qed.

    
Lemma rsum_split (A B: finType) p :
  \rsum_(x in [finType of (A * B)]) (p x) = \rsum_(a in A) \rsum_(b in B) (let x := (a,b) in (p x)).
Proof.
  unfold all => //=.
  rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
  rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
  rewrite !enumT.
  elim: (Finite.enum A); elim: (Finite.enum B); try by rewrite unlock => //=.
  rewrite unlock => //=; move=> _ xs //=.
  have: (flatten [seq [::] | _ <- xs] = [::]).
    by move=> T; elim: xs => //=.
      by move=> -> //=; rewrite add0R.
      move=> x xs IHx x' xs' IHx'.
        by rewrite big_allpairs !big_cons.
Qed.

Lemma rsum_pred_demote (A : finType) (b : pred A) (f: A -> Rdefinitions.R):
  \rsum_(a in A | b a) (f a) = \rsum_(a in A) ((b a %R) *R* (f a)).
Proof.

     apply Logic.eq_sym; rewrite (bigID (fun a => b a)) //=.   

     have: (\rsum_(i | ~~ b i) ((b i %R) *R* f i)) = (Rdefinitions.IZR 0); last move=>->;rewrite ?addR0.
          have: (\rsum_(i | ~~ b i) (Rdefinitions.IZR 0)) = Rdefinitions.IZR 0; last move=><-.
                by rewrite bigsum_card_constE mulR0.
          by apply eq_bigr=> i /Bool.negb_true_iff ->; rewrite //= mul0R.
     by apply eq_bigr=> i ->; rewrite //= mul1R.
Qed.
     
Lemma prsumr_sans_one (A: finType) (f: A -> Rdefinitions.R) (a': A) c:
  f a' = c ->
  \rsum_(a in A) (f a) = (1 %R) ->
  \rsum_(a | a != a') (f a) = (1 -R- c).
Proof.
  have: ((Rdefinitions.IZR (BinNums.Zpos BinNums.xH)) == (1 %R)). by [].
  move=> /eqP -> <- //=  <-.
  rewrite [\rsum_(a in A) _](bigID (fun a => a == a')) => //=.
  rewrite big_pred1_eq.
    by rewrite addRC -subRBA subRR subR0.
Qed.

Lemma rsum_tuple_split (A: finType) m (f: (m.+1).-tuple A -> Rdefinitions.R) :
  \rsum_(a in [finType of (m.+1).-tuple A]) (f a) =
  \rsum_(aas in [finType of (A * m.-tuple A)]) (let: (x, xs) := aas in f (cons_tuple x xs)).
Proof.
  rewrite (reindex (fun (aas: (A * m.-tuple A)) => let: (x,xs) := aas in cons_tuple x xs)) => //=.
    by apply eq_bigr => [[x xs] _].
    split with (fun xs => (thead xs, tbehead xs)).
  - move=> [x xs] _ //=.
    rewrite theadE.
    apply f_equal.
    (* Now just to deal with the annoying dependant type errors *)
    rewrite /tbehead/cons_tuple //=.
    rewrite /[tuple of _] //=.
    move: (behead_tupleP _) => //=; move: xs => [xs Hxs] Hxs'.
      by rewrite (proof_irrelevance _ Hxs' Hxs).

  - move=> [[//=| x xs] Hxs] _ //=.
      by erewrite (tuple_eta) => //=.
Qed.


Lemma rsum_distbind_d0 (A B:finType) (d_a: dist A) (g: B -> Rdefinitions.R) (f: A -> dist B):
  \rsum_(b in B) ((DistBind.d d_a f) b  *R* (g) b ) = 
  \rsum_(b in B) \rsum_(a in A) (d_a a *R*  ((f a) b *R* (g) b) ).
Proof.
  apply eq_bigr=> b _; rewrite DistBind.dE.
  rewrite rsum_Rmul_distr_r; apply eq_bigr=> a _.
  by rewrite mulRC -mulRA.
Qed.

Lemma rsum_distbind_d1 (A B C:finType) (d_c: dist C)
      (g: A -> B -> Rdefinitions.R) (f: A -> Rdefinitions.R)
      (df: C -> dist A) :
  \rsum_(b in B) \rsum_(a in A) ((DistBind.d d_c df) a *R*  (g a b) ) = 
  \rsum_(b in B) \rsum_(a in A) \rsum_(c in C)
   ((d_c c) *R* (((df c) a) *R*  (g a b))).
Proof.
  apply eq_bigr=> b _;apply eq_bigr=> a _; rewrite DistBind.dE.
  rewrite rsum_Rmul_distr_r; apply eq_bigr=> c _.
  by rewrite mulRC -mulRA.
Qed.


Lemma rsum_dist1_d0 (A B:finType) (a : A) (g: B -> Rdefinitions.R) (f: B -> A):
  \rsum_(b in B) ((Dist1.d a) (f b) *R* (g) b ) = 
  \rsum_(b in B) ((f b == a %R) *R* (g) b ).  
Proof.
  by apply eq_bigr=> b _; rewrite Dist1.dE.
Qed.


Lemma rsum_exchange_big1 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R):
  \rsum_(a in A) \rsum_(b in B) \rsum_(c in C) (f a b c) = 
  \rsum_(c in C) \rsum_(b in B)  \rsum_(a in A) (f a b c).
Proof.
  rewrite exchange_big [\rsum_(c in C) _]exchange_big;apply eq_bigr=> b _.
  by rewrite exchange_big.
Qed.

Lemma rsum_exchange_big2 (A B C D: finType)
      (f: A -> B -> C -> D -> Rdefinitions.R):
  \rsum_(a in A) \rsum_(b in B) \rsum_(c in C) \rsum_(d in D) (f a b c d) = 
  \rsum_(d in D)  \rsum_(b in B)  \rsum_(c in C)  \rsum_(a in A) (f a b c d).
Proof.
  rewrite exchange_big [\rsum_(d in D) _]exchange_big;apply eq_bigr=> b _.
  rewrite exchange_big [\rsum_(i in D) _]exchange_big;apply eq_bigr=> c _.
  by rewrite exchange_big.
Qed.

Lemma rsum_exchange_big3 (A B C D E: finType)
      (f: A -> B -> C -> D -> E -> Rdefinitions.R):
  \rsum_(a in A) \rsum_(b in B) \rsum_(c in C) \rsum_(d in D) \rsum_(e in E) (f a b c d e) = 
  \rsum_(e in E)  \rsum_(b in B)  \rsum_(c in C) \rsum_(d in D)  \rsum_(a in A) (f a b c d e).
Proof.
  rewrite exchange_big [\rsum_(e in E) _]exchange_big;apply eq_bigr=> b _.
  rewrite exchange_big [\rsum_(i in E) _]exchange_big;apply eq_bigr=> c _.
  rewrite exchange_big [\rsum_(i in E) _]exchange_big;apply eq_bigr=> d _.
  by rewrite exchange_big.
Qed.

Lemma rsum_rmul_distr_l1 (A B: finType)
      (f: A -> B -> Rdefinitions.R) (g: A -> Rdefinitions.R):
  \rsum_(a in A) (g a *R* \rsum_(b in B) (f a b)) = 
    \rsum_(a in A) \rsum_(b in B) (g a *R* (f a b)).
Proof.
  apply eq_bigr=> a _; rewrite rsum_Rmul_distr_l.
  by apply eq_bigr=> c _.
Qed.

Lemma rsum_rmul_distr_r1 (A B: finType)
      (f: A -> B -> Rdefinitions.R) (g: A -> Rdefinitions.R):
  \rsum_(a in A) ( \rsum_(b in B) (f a b) *R* g a) = 
    \rsum_(a in A) \rsum_(b in B) (g a *R* (f a b)).
Proof.
  apply eq_bigr=> a _; rewrite rsum_Rmul_distr_r.
  by apply eq_bigr=> c _.
Qed.


Lemma rsum_rmul_distr_l2 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R) (g: A -> B -> Rdefinitions.R):
  \rsum_(a in A) \rsum_(b in B) ((g a b) *R* \rsum_(c in C) (f a b c)) = 
    \rsum_(a in A) \rsum_(b in B)   \rsum_(c in C) (g a b *R* (f a b c)).
Proof.
  apply eq_bigr=> a _; apply eq_bigr=> b _; rewrite rsum_Rmul_distr_l.
  by apply eq_bigr=> c _.
Qed.

Lemma rsum_rmul_distr_r2 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R) (g: A -> B -> Rdefinitions.R):
  \rsum_(a in A) \rsum_(b in B) (\rsum_(c in C) (f a b c) *R* (g a b)) = 
    \rsum_(a in A) \rsum_(b in B)   \rsum_(c in C) (g a b *R* (f a b c)).
Proof.
  apply eq_bigr=> a _; apply eq_bigr=> b _; rewrite rsum_Rmul_distr_r.
  by apply eq_bigr=> c _.
Qed.

Lemma rsum_empty (A : finType) (f: 0.-tuple A -> Rdefinitions.R) :
  \rsum_(a in [finType of 0.-tuple A]) (f a) = (f [tuple]).
Proof.
  rewrite unlock => //=.

  have: (index_enum [finType of 0.-tuple A]) = [:: [tuple]].
      rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
      rewrite -enumT //=; rewrite/(enum _)//=.
      rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
      move: (FinTuple.size_enum 0 A)=> //=; rewrite expn0.
      move: (FinTuple.enum _ _)=>[|[[|//=] Hz] []]//= _.
        by move: (@tuple0  A (Tuple Hz)) <- =>//=.
  by move=> -> //=; rewrite addR0.      
Qed.

Lemma rsum_sans_one_const (A: finType) (c: Rdefinitions.R) (x : A) :
   #|A| > 0 ->
     (\rsum_(a in A | a != x) c) = ((#|A| - 1 %R) *R* (c)).
Proof.
  move=> Hlen; move: (bigsum_card_constE A c).
  rewrite natRB //= -addR_opp RIneq.Rmult_plus_distr_r mulNR mul1R addR_opp.
  rewrite (bigID (fun i => i == x)) big_pred1_eq//= addRC => <-.
  by rewrite -subRBA subRR subR0.
Qed.


Lemma rsum_mem_pred (A: finType) k x : #|A| > 0 -> \rsum_(xs in [finType of k.-tuple A] | x \in xs) ((Rdefinitions.Rinv (#|A| %R) ^R^ k)) = (1 -R- ((1 -R- (Rdefinitions.Rinv (#|A| %R)))  ^R^ k)).
Proof.
  rewrite rsum_pred_demote => Hord; elim: k x => [//=|k IHk] x;
  first by rewrite rsum_empty //= mul0R subRR.

  rewrite rsum_tuple_split rsum_split //=.

  rewrite (bigID (fun a => a == x)) big_pred1_eq//=.

  have: (
\rsum_(b in [finType of k.-tuple A])
      (((x \in cons_tuple x b) %R) *R*
       (Rdefinitions.Rinv (#|A| %R) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ k)))) = (
Rdefinitions.Rinv (#|A| %R) *R*
\rsum_(b in [finType of k.-tuple A])
      (( (Rdefinitions.Rinv (#|A| %R) ^R^ k)))
        ); last move=>->.
        rewrite rsum_Rmul_distr_l; apply eq_bigr=> inds _ //=.
        by rewrite in_cons eq_refl Bool.orb_true_l //= mul1R.
  rewrite bigsum_card_constE.

  have: (((#|[finType of k.-tuple A]| %R) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ k))) = (1 %R); last move=>->.
  rewrite card_tuple; rewrite -Rfunctions.Rinv_pow.
  rewrite natRexp;  rewrite mulRC mulVR //=; rewrite -natRexp; apply expR_neq0.
  by apply/eqP; apply RIneq.not_0_INR; apply/eqP; apply lt0n_neq0.
    by apply RIneq.not_0_INR; apply/eqP; apply lt0n_neq0.
    rewrite mulR1.

    have: (
   \rsum_(i | i != x)
      \rsum_(b in [finType of k.-tuple A])
         (((x \in cons_tuple i b) %R) *R*
          (Rdefinitions.Rinv (#|A| %R) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ k)))) = (
   \rsum_(i | i != x)
      (Rdefinitions.Rinv (#|A| %R) *R* \rsum_(b in [finType of k.-tuple A])
         (((x \in b) %R) *R*
          ( (Rdefinitions.Rinv (#|A| %R) ^R^ k))) 
          )); last move=>->; first by
    apply eq_bigr=> ind /Bool.negb_true_iff Hneq;
    rewrite rsum_Rmul_distr_l; apply eq_bigr=> inds _; rewrite in_cons eq_sym Hneq;
    rewrite Bool.orb_false_l mulRA mulRC mulRA mulRC; apply f_equal; rewrite mulRC.

    rewrite rsum_sans_one_const //= IHk //=.
    rewrite natRB. rewrite -addR_opp RIneq.Rmult_plus_distr_r mulRA.
    rewrite mulRV //= ?mul1R.
    rewrite addRA addRC addRA addRC; apply Logic.eq_sym.

    have: ((1 -R- ((1 -R- Rdefinitions.Rinv (#|A| %R)) *R* ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k)))) =
          ((1 -R- ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k)) +R+  (Rdefinitions.Rinv (#|A| %R) *R* ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k) )); last move=>->; try apply f_equal.
    rewrite -[_ -R- (Rdefinitions.Rinv _)]addR_opp RIneq.Rmult_plus_distr_r mul1R.
    by rewrite mulNR !addR_opp subRB.
    rewrite addRC mulNR addR_opp mul1R.
    by rewrite RIneq.Rmult_minus_distr_l subRB mulR1 subRR add0R.
    by apply/eqP; apply RIneq.not_0_INR;apply/eqP; rewrite -lt0n.
    by [].
Qed.



Lemma prsumr_dep_ineq (A: finType) (f g : A -> Rdefinitions.R) :
  (forall a, 0 -<=- f a) ->  (forall a, 0 -<=- g a) ->  
    (\rsum_(a in A) ((f a) *R* (g a))) -<=- (\rsum_(a in A) (f a) *R* \rsum_(a in A) (g a)).
Proof.
  move=> H1 H2; rewrite big_distrlr //=; apply ler_rsum => a _ //=; rewrite -rsum_Rmul_distr_l.
  apply RIneq.Rmult_le_compat_l => //=; rewrite (bigID (fun a' => a' == a)) big_pred1_eq //=.
  by apply leR_addl =>//=; dispatch_Rgt.
Qed.


Lemma prsumr_implb_ineq (A: finType) (p q : pred A) (f: A -> Rdefinitions.R):
  (forall a, 0 -<=- f a) -> (forall a, p a ==> q a ) ->
  \rsum_(a  in A) ((p a %R) *R* (f a)) -<=-
   \rsum_(a  in A) ((q a %R) *R* (f a)).
Proof.
  move=> Hpr Himpl.
  apply ler_rsum => a H.
  apply RIneq.Rmult_le_compat_r; try by apply Hpr.
  move: (Himpl a); case: (p a) => //=; first by move=> -> //=; apply leRR.
  move=>_;case: (q a) => //=; by apply leRR.
Qed.


Lemma boolR_distr (a b : bool) : (a && b %R) = ((a %R) *R* (b %R)).
Proof.
  by case: a; case: b => //=; rewrite ?mulR1 ?mul1R ?mulR0 ?mul0R //=.
Qed.

(* unused last version for rcons inductions - however, rcons lacks an
 equivalent of tail*)
Definition tlast (n : nat) (T : Type) tuple :=
  (tnth (T:=T) tuple (Ordinal (ltnSn n))).




Lemma xcons_eqE {A: eqType} {l: nat} (h  h': A) (t t': l.-tuple A): ((cons_tuple h t) == (cons_tuple h' t')) = (h == h') && (t == t').
Proof.
    by rewrite /cons_tuple//=.
Qed.


Lemma ntuple_tailE A l (x:A) (xs: l.-tuple A): FixedList.ntuple_tail [tuple of x :: xs] = xs.
Proof.
  rewrite /FixedList.ntuple_tail/[tuple of _]//=.
  move: xs (behead_tupleP _) => [xs Hxs Hxs'].
    by rewrite (proof_irrelevance _ Hxs Hxs').
Qed.



Lemma rsum_indep (A : finType) (pr : dist A) (f g : pred A) :
 (inde_events pr (finset.SetDef.finset f) (finset.SetDef.finset g)) ->
  \rsum_(a in A) (pr a *R* (f a && g a %R)) =
  (\rsum_(a in A) (pr a *R* (f a %R)) *R* \rsum_(a in A) (pr a *R* (g a %R))).
Proof.
  rewrite /inde_events/Pr//=.
  rewrite [\rsum_(a in _ (_ f)) _ ](rsum_setT) [\rsum_(a in _ (_ g)) _ ](rsum_setT) //=.
  have: (\rsum_(a in finset.SetDef.pred_of_set
                       (finset.setI (finset.SetDef.finset f) (finset.SetDef.finset g))) 
          pr a = \rsum_(a | f a && g a) (pr a)).
      by apply eq_big => //=; move=> a //=; rewrite finset.in_setI !finset.in_set.
  move=>->.

  have: (\rsum_(i in finset.SetDef.pred_of_set (finset.setTfor (Phant A)) | finset.SetDef.pred_of_set
                                                                        (finset.SetDef.finset f) i) (pr i) = \rsum_(i | f i) (pr i)).
    by apply eq_big => //= a //=; rewrite !finset.in_set Bool.andb_true_l;
                    apply Logic.eq_sym;  rewrite -finset.in_set //=.
  move=>->.

  have: (\rsum_(j in finset.SetDef.pred_of_set (finset.setTfor (Phant A)) | finset.SetDef.pred_of_set
                                                                        (finset.SetDef.finset g) j) (pr j) = \rsum_(j | g j) (pr j)).
    by apply eq_big => //= a //=; rewrite !finset.in_set Bool.andb_true_l;
                    apply Logic.eq_sym;  rewrite -finset.in_set //=.
  move=>-> Heq.
  have H x y z: (y = (0%R)) -> x = z -> x +R+ y = z. by move => -> ->; rewrite addR0.
  transitivity (\rsum_(a | f a && g a) (pr a)).
       rewrite (bigID (fun a => f a && g a)) //=; apply H.
           - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
             by rewrite //=mulR0.
        by apply eq_bigr => a -> //=; rewrite mulR1.

  have: (\rsum_(a in A) (pr a *R* (f a %R)) = \rsum_(a | f a) (pr a)).      
       rewrite (bigID (fun a => f a)) //=; apply H.
           - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
             by rewrite //= mulR0.
       by apply eq_bigr => a -> //=; rewrite mulR1.
  move=> ->.

  have: (\rsum_(a in A) (pr a *R* (g a %R)) = \rsum_(a | g a) (pr a)).      
       rewrite (bigID (fun a => g a)) //=; apply H.
           - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
             by rewrite //= mulR0.
       by apply eq_bigr => a -> //=; rewrite mulR1.
  move=> ->.
  by [].
Qed.



  

  
Section Hash.

  Lemma hash_uni n (hash_state: HashState n) value (hash_value: 'I_Hash_size.+1) :
    (hashstate_find _ value hash_state == None) ->
    (
      P[ ((hash n value hash_state) |> (fun h => ret (snd h ))) === hash_value ] =
     ((1 %R) /R/ (#|ordinal Hash_size.+1| %R))
    ).
  Proof.
    move=>/eqP Hhsfindnone; rewrite /hash Hhsfindnone //= DistBindA //= DistBindp1.
    rewrite (functional_extensionality (fun x : 'I_Hash_size.+1 => DistBind.d (Dist1.d (hashstate_put n value x hash_state, x)) (fun b : HashState n * 'I_Hash_size.+1 => Dist1.d b.2)) (fun x : 'I_Hash_size.+1 => Dist1.d x)); first last.
      by move=> x; rewrite DistBind1f //=.
        by  rewrite DistBindp1 Uniform.dE div1R  //=.
  Qed.

End Hash.


Lemma hash_vec_insert_length n l (value: hash_keytype) (hashes: l.-tuple (HashState n)) (inds: l.-tuple 'I_Hash_size.+1):
  size (map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
               let (hash,ind) := pair in @hashstate_put _ value ind hash)
            (zip (tval hashes) (tval inds))) == l.
Proof.
    by rewrite size_map size_zip !size_tuple /minn ltnn //=.
Qed.


Lemma cons_sizeP T l (x : T) xs : (size (x :: xs) == l.+1) -> (size xs == l).
    by [].
Qed.



Lemma hash_vec_insert_length_consP n l (value: hash_keytype)
      (hashes: seq (HashState n)) (hash: HashState n) (Hhashes: size (hash :: hashes) == l.+1)
        (inds: seq 'I_Hash_size.+1) (ind: 'I_Hash_size.+1) (Hind: size (ind :: inds) == l.+1) :
    Tuple (hash_vec_insert_length value (Tuple Hhashes) (Tuple Hind)) =
    cons_tuple
      (@hashstate_put _ value ind hash) 
      (Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hhashes)) (Tuple (cons_sizeP Hind)))).
Proof.

  move: (cons_sizeP _ ) => //= Hhashes'.
  move: (cons_sizeP _ ) => //= Hinds'.
  move: (hash_vec_insert_length _ _ _) => Hinsert'.

  move: (Hinsert') => Hinsert; move: Hinsert'.
  have:    (map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                   let (hash,ind) := pair in @hashstate_put _ value ind hash)
                (zip (Tuple Hhashes) (Tuple Hind))) = 
           (hashstate_put n value ind hash) :: (map
                                                  (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                                                       let (hash,ind) := pair in @hashstate_put _ value ind hash)
                                                  (zip (Tuple Hhashes') (Tuple Hinds'))).
      by [].
  move=> ->; move: Hinsert =>  H1 H2.
  rewrite (proof_irrelevance _ H1 H2); clear H1.
  erewrite tuple_eta; case Heq: [tuple of _ :: _] => [[//=| x xs] Hxs].

  move: Heq.
  rewrite theadE.

  have: behead_tuple
                 (cons_tuple (hashstate_put n value ind hash)
                    (Tuple (hash_vec_insert_length value (Tuple Hhashes') (Tuple Hinds')))) = (Tuple (hash_vec_insert_length value (Tuple Hhashes') (Tuple Hinds'))).

      rewrite /behead_tuple //=; move:  (hash_vec_insert_length _ _ _) (behead_tupleP _ ) => //= H3 H4.
      by rewrite (proof_irrelevance _ H3 H4).

  move=>-> [Heqx Heqxs].

  move: Hxs H2; rewrite Heqx Heqxs => //= Ha Hb.
  by rewrite (proof_irrelevance _ Ha Hb).

Qed.

Lemma mem_zip (S T : eqType) (ss : seq S) (ts: seq T) (s: S) (t: T):
  ((s,t) \in (zip ss ts)) -> ((s \in ss) && (t \in ts)).
Proof.

  elim: ss ts => [|s' ss IHss] ts //=.
  - by case: ts =>//=.
  - case: ts => [//=|t' ts].
    move=>//=; rewrite !in_cons //= xpair_eqE =>/orP[/andP[ -> -> //=]| ].
    by move=>/IHss/andP[-> ->]; rewrite !Bool.orb_true_r.
Qed.

Lemma zip_empty_r (S T: eqType) (ts: seq T) : (@zip S _ [::] ts) = ([::]).
Proof.
  by case: ts.
Qed.


Definition hash_vec_contains_value n l (value: hash_keytype) (hashes: l.-tuple (HashState n)) (inds: l.-tuple 'I_Hash_size.+1) : bool :=
  all (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
               let (hash,ind) := pair in @hashstate_find _ value hash == Some ind)
            (zip (tval hashes) (tval inds)).

Lemma hash_vec_contains_value_preserve n l (value value': hash_keytype) (hashes: l.-tuple (HashState n)) (inds inds': l.-tuple 'I_Hash_size.+1) : value != value' ->
  hash_vec_contains_value value hashes inds ->
  hash_vec_contains_value value (Tuple (hash_vec_insert_length value' hashes inds')) inds.
Proof.

  move=> Hvalueq Hcontains; move: Hcontains inds'.
  elim: l  hashes inds => [|l IHl]  hashes inds Hcontains inds' //=.
    by rewrite !tuple0/hash_vec_contains_value //= !zip_empty_r //=.
  move: (IHl (behead_tuple hashes) (behead_tuple inds)) Hcontains.
  rewrite (tuple_eta inds) (tuple_eta hashes) (tuple_eta inds') //=.
  rewrite /hash_vec_contains_value //= => IHl' /andP [Hsh_eq /IHl' IH].
  apply/andP;split; last by apply IH => //=.
  clear IH IHl IHl'.

  move: Hsh_eq; rewrite /hashstate_find/hashstate_put //=.

  case: hashes => [[|hshs hshses] Hhshs] //=.
  case: inds' => [[|ind' inds'] Hinds'] //=.
  case: inds => [[|ind inds] Hinds] //=.
  have ->: (thead (Tuple Hhshs)) = hshs; first by [].
  have ->: (thead (Tuple Hinds')) = ind'; first by [].
  have ->: (thead (Tuple Hinds)) = ind; first by [].
  move: Hvalueq; clear.
  elim: n hshs => [//=|n IHn] hshs.
  move=>//=.

  rewrite  /FixedList.ntuple_head (tuple_eta hshs) !theadE !ntuple_tailE.

  case: hshs => [[| hsh hshs] Hhshs] //=.
  have ->:  thead (Tuple Hhshs) = hsh; first by [].

  case: hsh Hhshs => [[k v]|] Hshsh //=; last first.
  - {
      move=> Hneq; move: (Hneq); rewrite eq_sym =>/Bool.negb_true_iff -> //=.
      move: Hshsh (eq_ind _ _ _ _ _ )  => //= H1 H2.
      rewrite/ FixedList.ntuple_tail/behead_tuple (proof_irrelevance _ H1 H2) //=.
      move: (behead_tupleP _ ) (behead_tupleP _) => //= H3 H4.
      by rewrite (proof_irrelevance _ H3 H4) //=.
    }
  - {
      case Hkeq: (k == value).
      - {
          move/eqP: Hkeq => -> /Bool.negb_true_iff ->.
          by rewrite ntuple_head_consP eq_refl.
        }
      - {
          case Hkeq': (k == value').
          - {
              move: Hshsh (eq_ind _ _ _ _ _) =>//= H1 H2.
              rewrite /FixedList.ntuple_tail /behead_tuple.
              move: (behead_tupleP _) (behead_tupleP _) => //= H3 H4.
              by rewrite (proof_irrelevance _ H3 H4) eq_sym =>/Bool.negb_true_iff ->.
            }
          - {
              rewrite ntuple_head_consP Hkeq.
              rewrite ntuple_tail_consP.
              by move=> Hneq Hfind; apply IHn => //=.
            }
        }
    }
Qed.    


Lemma hash_vec_contains_value_base n l (value: hash_keytype) (hashes: l.-tuple (HashState n)) (inds
: l.-tuple 'I_Hash_size.+1) : 
  all (fun hsh => FixedList.fixlist_length hsh + 1 <= n) hashes ->
  hash_vec_contains_value value (Tuple (hash_vec_insert_length value hashes inds)) inds.
Proof.

  elim: l  hashes inds => [|l IHl]  hashes inds //=.
    by rewrite !tuple0/hash_vec_contains_value //= !zip_empty_r //=.

    move=> /allP Hhashes.
  have H1: all
     (fun hsh : FixedList.fixlist [eqType of hash_keytype * hash_valuetype] n =>
      FixedList.fixlist_length hsh + 1 <= n) (behead_tuple hashes).
  {
    apply/allP => ind Hind; apply Hhashes => //=.
      by move: Hind; rewrite (tuple_eta hashes) //= in_cons => ->; rewrite Bool.orb_true_r //=.    
  }

  move: (IHl (behead_tuple hashes) (behead_tuple inds) H1); clear IHl H1.
  rewrite (tuple_eta inds) (tuple_eta hashes) //=.
  rewrite /hash_vec_contains_value //= => H1; apply/andP; split=>//=; last first.
  clear H1.
  have: (thead hashes \in hashes); first by rewrite (tuple_eta hashes) in_cons theadE eq_refl//=.
  move=>/(Hhashes (thead hashes)); clear Hhashes.
  move: (thead hashes) (thead inds); clear hashes inds l.
  elim: n => [//= | n IHn].
  - {
      move=> hsh ind; rewrite addn1 //=.
    }

  - {

      move=> [[//=| hsh hshs] Hhshs] inds //=.
      have ->: FixedList.ntuple_head (Tuple Hhshs) = hsh; first by [].

      case: hsh Hhshs => //= [[k v]|] Hshsh.
      - {
          case Hkeq: (k == value) => //=.
          - by rewrite eq_refl.
          - {
              rewrite /FixedList.ntuple_head //= ntuple_head_consP Hkeq.
              rewrite ntuple_tail_consP => Hlen.
              by apply IHn => //=.
              }
        }

      - {
          by rewrite eq_refl.
        }
    }
Qed.

Lemma hash_vecP n l (value: hash_keytype) (hashes: l.-tuple (HashState n))
   (inds: l.-tuple 'I_Hash_size.+1) (Huns: all (fun hsh => FixedMap.fixmap_find value hsh == None) hashes) :
   d[ hash_vec_int value hashes ] (Tuple (hash_vec_insert_length value hashes inds), inds) =
     ((Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l).
 Proof.

   elim: l value hashes inds Huns => [//=| l IHl].
      - by move=> value [[|//=] Hlen] [[|//=] Hinds]; rewrite Dist1.dE //=.

      - move=> //= value [[//=| x xs] Hxs] [[//=| y ys] Hys] Huns; rewrite DistBind.dE.   
        erewrite <- (IHl value (FixedList.ntuple_tail (Tuple Hxs))).
        rewrite /FixedList.ntuple_tail; move: (behead_tupleP _) => //= Hlen.

        transitivity (
            \rsum_(hshs in [finType of l.-tuple (HashState n)])
             \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
             \rsum_(hsh in hashstate_of_finType n)
             \rsum_(ind in ordinal_finType Hash_size.+1)
             ((d[ hash_vec_int value (Tuple Hlen)]) (hshs, inds) *R*
              ((d[ hash n value (thead (Tuple Hxs))]) (hsh, ind) *R*
([&& (hsh == hashstate_put n value y x ) &&
       (hshs == Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs)) (Tuple (cons_sizeP Hys)))),
       ind == y
     & inds == Tuple (cons_sizeP Hys)] %R)
               ))
          ).
                rewrite rsum_split.
                apply eq_bigr => hshs _; apply eq_bigr => inds _ //=; rewrite DistBind.dE //=.
                rewrite mulRC rsum_Rmul_distr_r rsum_split.
                apply eq_bigr => hsh _; apply eq_bigr => ind _ //=.
                apply f_equal; apply f_equal => //=; rewrite Dist1.dE.
                rewrite xpair_eqE.
                rewrite hash_vec_insert_length_consP.
                rewrite !xcons_eqE.
                have: (Tuple Hys = cons_tuple y (Tuple (cons_sizeP Hys))).
                     rewrite (tuple_eta (cons_tuple _ _)) //= theadE; case Heq: [tuple of _] => [[//=| y' ys'] Hys'].
                     move: Heq => [Heqy' Heqys'].
                     move: Hys'; rewrite -Heqy' -Heqys'; move: Hys => H1 H2.
                     by rewrite (proof_irrelevance _ H1 H2).
                move=>->; rewrite xcons_eqE.

                rewrite eq_sym; apply f_equal; apply f_equal.

                case: (_ == _); rewrite ?Bool.andb_true_l ?Bool.andb_false_l//=.
                rewrite eq_sym.
                case: (_ == _); rewrite ?Bool.andb_true_l ?Bool.andb_false_l //=.
                rewrite eq_sym.
                by case: (_ == _); rewrite ?Bool.andb_true_l ?Bool.andb_false_l//=. 
        have H x1 y1 z1 : (y1 = (0 %R)) -> x1 = z1 -> x1 +R+ y1 = z1. by move=> -> ->; rewrite addR0.
        transitivity (
           \rsum_(hshs in [finType of l.-tuple (HashState n)])
            \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
              ((d[ hash_vec_int value (Tuple Hlen)]) (hshs, inds) *R*
               ((d[ hash n value (thead (Tuple Hxs))]) (hashstate_put n value y x, y) *R*
                ([&& (hshs == Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs))
                           (Tuple (cons_sizeP Hys))) ) & inds ==  Tuple (cons_sizeP Hys)] %R)))
          ).                
                - apply eq_bigr => hshs _; apply eq_bigr => inds _.
                  rewrite (bigID (fun hsh => hsh == hashstate_put n value y x)) big_pred1_eq eq_refl //=.

                  apply H.
                     - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
                       apply prsumr_eq0P => ind' Hind'; first by dispatch_Rgt.
                       by rewrite //= !mulR0.

                  rewrite (bigID (fun ind => ind == y)) big_pred1_eq eq_refl //=.

                  apply H.
                     - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
                       by rewrite !Bool.andb_false_l Bool.andb_false_r //= !mulR0.
                  by [].     

        transitivity (
            ((d[ hash_vec_int value (Tuple Hlen)]) (Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs)) (Tuple (cons_sizeP Hys))), Tuple (cons_sizeP Hys)) *R*
             ((d[ hash n value (thead (Tuple Hxs))]) (hashstate_put n value y x, y)))
         ).
                  rewrite (bigID (fun hshs => hshs == Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs)) (Tuple (cons_sizeP Hys))))) big_pred1_eq eq_refl //=.

                  apply H.
                     - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
                       apply prsumr_eq0P => ind' Hind'; first by dispatch_Rgt.
                       by rewrite //= !mulR0.

                  rewrite (bigID (fun inds => inds == Tuple (cons_sizeP Hys))) big_pred1_eq eq_refl //=.                  apply H.
                     - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
                       by rewrite //= !mulR0.
                  by rewrite mulR1.

        move: (cons_sizeP _) => Hlen'; rewrite (proof_irrelevance _ Hlen' Hlen); clear Hlen'.
        apply Logic.eq_sym; rewrite mulRC.
        apply f_equal.

        move: Huns => /allP Huns.

        have H1: (x \in Tuple Hxs). by rewrite in_cons eq_refl //=.
        move /eqP: (Huns x H1) => Hx.
        have: (thead (Tuple Hxs)) = x. by [].
        move=>->; rewrite /hash/hashstate_find Hx //= DistBind.dE.
        apply Logic.eq_sym.

        transitivity (
  \rsum_(a in [finType of 'I_Hash_size.+1])
      (\rsum_(a0 in ordinal_finType Hash_size.+1)
      ((Uniform.d (size_enum_equiv (size_enum_ord Hash_size.+1))) a0 *R* (Dist1.d a0) a) *R*
       ((hashstate_put n value y x == hashstate_put n value a x) && (a == y) %R))
          ).
           apply eq_bigr => a _.
           by rewrite DistBind.dE Dist1.dE xpair_eqE (eq_sym y).

        rewrite (bigID (fun a => a == y)) big_pred1_eq eq_refl //=.   
        apply H.

            - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first (dispatch_Rgt; move=>_; dispatch_Rgt).
              by rewrite Bool.andb_false_r //= mulR0.

       rewrite eq_refl //= mulR1. 

       transitivity (
           \rsum_(a0 in 'I_Hash_size.+1)
            ((Uniform.d (size_enum_equiv (size_enum_ord Hash_size.+1))) a0 *R* (a0 == y %R))
          ).
           by apply eq_bigr => a' _; rewrite Dist1.dE eq_sym.

      rewrite (bigID (fun a0 => a0 == y)) big_pred1_eq //= eq_refl mulR1 //=.
      apply H.

          - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by dispatch_Rgt.
            by rewrite mulR0.
     by rewrite Uniform.dE card_ord.

     rewrite /FixedList.ntuple_tail //=.
     by move: Huns => //= =>/andP [].
 Qed.

Lemma negb_consP (A: eqType) (x y: A) (xs ys: seq A) : x :: xs != y :: ys = ((x != y) || (xs != ys)). 
Proof.
  by rewrite eqseq_cons Bool.negb_andb.
Qed.

Lemma tuple_eq_inj (A: eqType) l (xs ys: seq A) (Hxs: size xs == l) (Hys: size ys == l) :
  (Tuple Hxs == Tuple Hys) = (xs == ys).
Proof.
  by move=> //=.
Qed.



Lemma neg_hash_vecP n l (value: hash_keytype) (hashes hashes': l.-tuple (HashState n))
      (inds: l.-tuple 'I_Hash_size.+1)
      (Huns: all (fun hsh => FixedMap.fixmap_find value hsh == None) hashes)
  : (tval hashes' != map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                            let (hash,ind) := pair in
                            @hashstate_put _ value ind hash) (zip (tval hashes) (tval inds))) ->
   d[ hash_vec_int value hashes ] (hashes', inds) =
     (0 %R).
 Proof.


   elim: l value hashes hashes' inds Huns => [//=| l IHl].
      - move=> value hashes hashes' inds.
        have: (hashes == [tuple]); last move=> /eqP ->; first by case: hashes => [[]] //=.
        have: (hashes' == [tuple]); last move=> /eqP ->; first by case: hashes' => [[]] //=.
        have: (inds == [tuple]); last move=> /eqP ->; first by case: inds => [[]] //=.
        by clear hashes hashes' inds => //=.

      - move=> //= value [[//=| x xs] Hxs] [[//=| y ys] Hys] [[//=| z zs] Hzs] /allP Huns; rewrite DistBind.dE //=.   

        rewrite negb_consP =>/orP [Hyneq | Hysneq].

        transitivity (  
            \rsum_(hshs' in tuple_finType l (hashstate_of_finType n))
             \rsum_(bf' in tuple_finType l (ordinal_finType Hash_size.+1))
                         (
(d[ hash_vec_int value (FixedList.ntuple_tail (Tuple Hxs))]) (hshs', bf') *R* 
(
  \rsum_(hshs'' in hashstate_of_finType n)
     \rsum_(ind' in ordinal_finType Hash_size.+1)
     \rsum_(ind'' in [finType of 'I_Hash_size.+1])
     (0%R)
)

                     )).
           - rewrite rsum_split; apply eq_bigr => hshs' _; apply eq_bigr => bf' _ //=.
             have: (thead (Tuple Hxs)) = x; last move=> ->; first by [].
             apply f_equal; rewrite DistBind.dE rsum_split.
             apply eq_bigr => hshs'' _; apply eq_bigr => ind' _ //=.
             rewrite /hash/hashstate_find Dist1.dE.
             case Hteq: ((_,_) == _); last by rewrite bigsum_card_constE //= !mulR0.
             move/eqP: Hteq => [<- _ <- _ ] //=; rewrite mulR1.
             have Hin: (x \in Tuple Hxs); first by rewrite (tuple_eta (Tuple Hxs)) //= in_cons; apply/orP;left. 
             move/eqP: (Huns x Hin) -> => //=; rewrite DistBind.dE.
             apply eq_bigr => ind'' _; rewrite Dist1.dE xpair_eqE.
             case Hz: (z == ind''); last by rewrite Bool.andb_false_r //= mulR0.
             by move/eqP: Hz <-; move/Bool.negb_true_iff: Hyneq -> => //=; rewrite mulR0.  
               by do ? [
                       (apply prsumr_eq0P; intros; first by dispatch_Rgt; intros; dispatch_Rgt)|
                       (apply RIneq.Rmult_eq_0_compat_l)
                     ].

             apply prsumr_eq0P => [[hshs' bf']|] ; first by dispatch_Rgt; case; intros; dispatch_Rgt.  
             move=> [hshs' bf'] _; case Heq: (tval hshs' == ys); last first.
                 - apply RIneq.Rmult_eq_0_compat_l => //=; rewrite DistBind.dE.
                   apply prsumr_eq0P => [[hshs'' ind']|[hshs'' ind']] _; first by dispatch_Rgt.
                   rewrite //= Dist1.dE xpair_eqE //=; apply RIneq.Rmult_eq_0_compat_l => //=.
                   suff: (Tuple Hys == [tuple of hshs'' :: hshs']) = false; first by move => -> //=.
                   rewrite (tuple_eta (Tuple Hys)).
                   have: (thead (Tuple Hys)) = y; last move=> -> //=; first by  [].
                   move: Heq; clear=> Heq.
                   rewrite !tupleE xcons_eqE //= /behead_tuple.
                   move: (behead_tupleP _) => //= Hys' //=.
                   move: hshs' Heq => [hshs' Hhshs'] //= Hneq.
                   suff: (Tuple Hys' == Tuple Hhshs') = false; first by move=>->; rewrite Bool.andb_false_r.
                   by rewrite tuple_eq_inj eq_sym Hneq.
             case Hbfeq: (tval bf' == zs); last first.      
                 - apply RIneq.Rmult_eq_0_compat_l => //=; rewrite DistBind.dE.
                   apply prsumr_eq0P => [[hshs'' ind']|[hshs'' ind']] _; first by dispatch_Rgt.
                   rewrite //= Dist1.dE xpair_eqE //=; apply RIneq.Rmult_eq_0_compat_l => //=.
                   suff: (Tuple Hzs == [tuple of ind' :: bf']) = false; first by move => ->; rewrite Bool.andb_false_r //=.
                   rewrite (tuple_eta (Tuple Hzs)).
                   have: (thead (Tuple Hzs)) = z; last move=> -> //=; first by  [].
                   by rewrite tuple_eq_inj eqseq_cons [zs == _]eq_sym Hbfeq Bool.andb_false_r.
             apply RIneq.Rmult_eq_0_compat_r; apply IHl;move/eqP:Heq=>Heq;move/eqP:Hbfeq=>Hbfeq; rewrite ?Heq ?Hbfeq //=.
                   clear IHl.
                   by apply/allP => x' Hx'; apply Huns=> //=; rewrite in_cons;apply/orP;right.

 Qed.
 

Lemma hash_vec_simpl (n' k': nat) (hashes: k'.-tuple (HashState n')) value inds f :
  all (fun hsh : FixedMap.fixmap hash_keytype hash_valuetype n' => FixedMap.fixmap_find value hsh == None) hashes ->
  (\rsum_(hshs' in [finType of k'.-tuple (HashState n')])
   ((d[ hash_vec_int value hashes]) (hshs', inds) *R* (f hshs'))) =
  ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k') *R* (f (Tuple (hash_vec_insert_length value hashes inds)))).
Proof.
  move=> Hall.
  rewrite (bigID (fun hshs' => hshs' == (Tuple (hash_vec_insert_length value hashes inds)))) big_pred1_eq//=.

  under big i Hneq rewrite neg_hash_vecP ?mul0R //=.
  rewrite bigsum_card_constE mulR0 addR0.
  rewrite hash_vecP //=.
Qed.


Lemma hash_vec_find_simpl n l (value: hash_keytype) (hashes hashes': l.-tuple (HashState n))
      (inds inds': l.-tuple 'I_Hash_size.+1):
  hash_vec_contains_value value hashes inds ->
   d[ hash_vec_int value hashes ] (hashes', inds') =
  ((hashes' == hashes) && (inds' == inds) %R).
Proof.
  elim: l hashes inds hashes'  inds' => [//=| l IHl].
  - by do ?(case; case => //=; intro); move=> _ //=; rewrite Dist1.dE xpair_eqE //= !tuple0 //=.
  - move=> [[//=| hash hashes] Hhashes] [[//=| ind inds] Hinds] [[//=| hash' hashes'] Hhashes']  [[//=|ind' inds'] Hinds'] //=.
    rewrite DistBind.dE rsum_split //=.
    have H1: (thead (Tuple Hhashes)) = hash; first by [].
    under big a _ under big b _ rewrite H1.
    move: (IHl (FixedList.ntuple_tail (Tuple Hhashes)) (FixedList.ntuple_tail (Tuple Hinds))) => IHl' /allP Hcontains.
    under big a H3 under big b H4 rewrite IHl' ?boolR_distr -?mulRA.
    {
      rewrite exchange_big; under big b _ rewrite -rsum_pred_demote big_pred1_eq.
      rewrite -rsum_pred_demote big_pred1_eq //=.
      rewrite DistBind.dE rsum_split //=.

      under big a _ under big b _ rewrite Dist1.dE xpair_eqE//=.

      have Heq (a: HashState n) (b: 'I_Hash_size.+1):
        (Tuple Hhashes' == [tuple of a :: (FixedList.ntuple_tail (Tuple Hhashes))])
          && (Tuple Hinds' == [tuple of b :: FixedList.ntuple_tail (Tuple Hinds)]) =
        ((a == hash') && (b == ind') &&
                      ((FixedList.ntuple_tail (Tuple Hhashes')) == (FixedList.ntuple_tail (Tuple Hhashes))) &&
                      ((FixedList.ntuple_tail (Tuple Hinds')) == (FixedList.ntuple_tail (Tuple Hinds)))
        ).
      {
        have ->: (Tuple Hhashes') = ([tuple of hash' :: (FixedList.ntuple_tail (Tuple Hhashes'))]).
        {
          rewrite (tuple_eta (Tuple Hhashes')) //=.
          rewrite!/[tuple of _] //=; move: (valP _) =>//= H8; move: (valP _ )=>//=H9.
            by rewrite (proof_irrelevance _ H8 H9).        
        }
        rewrite xcons_eqE eq_sym -andbA -andbA -andbA; apply f_equal.
        have ->: (Tuple Hinds') = ([tuple of ind' :: (FixedList.ntuple_tail (Tuple Hinds'))]).
        {
          rewrite (tuple_eta (Tuple Hinds')) //=.
          rewrite!/[tuple of _] //=; move: (valP _) =>//= H8; move: (valP _ )=>//=H9.
            by rewrite (proof_irrelevance _ H8 H9).        
        }
        rewrite xcons_eqE andbC eq_sym -andbA //=; apply f_equal.
          by rewrite !ntuple_tailE //= andbC //=.
      }

      under big a _ under big b _ rewrite Heq !boolR_distr mulRC -!mulRA.

      rewrite exchange_big; under big a _ rewrite -rsum_pred_demote big_pred1_eq.
      rewrite -rsum_pred_demote big_pred1_eq //=.
      rewrite/Hash.hash //=.

      have ->: (Tuple Hhashes' == Tuple Hhashes) && (Tuple Hinds' == Tuple Hinds) =
      (hash == hash') && (ind == ind') &&
                      (FixedList.ntuple_tail (Tuple Hhashes') == FixedList.ntuple_tail (Tuple Hhashes)) &&
                      (FixedList.ntuple_tail (Tuple Hinds') == FixedList.ntuple_tail (Tuple Hinds)).
      {
        rewrite (tuple_eta (Tuple Hhashes')) (tuple_eta (Tuple Hhashes)) (tuple_eta (Tuple Hinds)) (tuple_eta (Tuple Hinds'))  //=.
        rewrite !ntuple_tailE //=.
        have -> : (thead (Tuple Hhashes')) = hash'; first by [].
        have -> : (thead (Tuple Hhashes)) = hash; first by [].
        have -> : (thead (Tuple Hinds')) = ind'; first by [].
        have -> : (thead (Tuple Hinds)) = ind; first by [].
        apply Logic.eq_sym.

        transitivity (
            ((hash' == hash) && (behead_tuple (Tuple Hhashes') == behead_tuple (Tuple Hhashes))) &&
                                                                                                 ((ind' == ind) && (behead_tuple (Tuple Hinds') == behead_tuple (Tuple Hinds)))
          ).

        {
          rewrite -andbA -andbA -andbA eq_sym; apply f_equal.
          rewrite andbC -andbA; apply f_equal.
            by rewrite andbC eq_sym.
        }
          by rewrite -!xcons_eqE //=.
      }
      rewrite andbC andbA andbC !boolR_distr; do? apply f_equal.
      have Hin: ((hash, ind) \in zip (Tuple Hhashes) (Tuple Hinds)); first by rewrite //= in_cons eq_refl //=.
        by move: (Hcontains (hash,ind) Hin) =>/eqP -> //=; rewrite Dist1.dE eq_sym xpair_eqE boolR_distr //=.
        
    }
    {

      apply/allP => [[hsh_tail ind_tail]] //= Hin.

      have Hin': (hsh_tail, ind_tail) \in zip (Tuple Hhashes) (Tuple Hinds); first by rewrite//= in_cons Hin Bool.orb_true_r.
      by move: (Hcontains (hsh_tail, ind_tail) Hin').

    }
Qed.


  


Module uniform_vec.
Section definitions.
Variable n k : nat.

Definition pmf: pos_ffun [finType of k.-tuple 'I_n.+1].
split with (finfun (fun a => (Rdefinitions.Rinv (n.+1 %R)) ^R^ k)).
apply /forallP_leRP=> a //=.
by rewrite ffunE; apply expR_ge0; left; apply RIneq.Rinv_0_lt_compat; apply ltR0n.
Defined.

Lemma pmfE a : pmf a = ((Rdefinitions.Rinv (n.+1 %R)) ^R^ k).
Proof. by move=> //=;rewrite ffunE. Qed.


Definition dist: dist [finType of (k.-tuple 'I_n.+1)].
split with pmf.
apply/eqP=> //=.
under big a _ rewrite pmfE.
rewrite bigsum_card_constE card_tuple card_ord -natRexp.
rewrite -Rfunctions.Rinv_pow ?mulRV //=.
by apply expR_neq0; apply/eqP; apply RIneq.not_0_INR.
by apply RIneq.not_0_INR.
Defined.

Lemma dE  a : dist a = ((Rdefinitions.Rinv (n.+1 %R)) ^R^ k).
Proof. by move=> //=;rewrite ffunE. Qed.

End definitions.
End uniform_vec.

Section BloomFilter.

  (*
    k - number of hashes
   *)
  Variable k: nat.
  (*
    n - maximum number of hashes supported
   *)
  Variable n: nat.
  (* valid k *)
  Variable Hkgt0: k >0.

  (* the sequence of hash functions used to update the bloom filter *)
  Definition hash_vec := k.-tuple (HashState n).


  Definition hash_not_full (hsh: HashState n) : bool :=
    FixedList.fixlist_length hsh < n.

  Definition hash_unseen (b: B) (hsh: HashState n) : bool :=
    FixedMap.fixmap_find b hsh == None.

  Definition hash_has_free_spaces (s: nat) (hsh: HashState n) : bool :=
    FixedList.fixlist_length hsh + s <= n.

  Definition hashes_not_full (hashes: hash_vec) : bool :=
    (* provided the finite maps of all the hash function are not full*)
    all hash_not_full (tval hashes).

  Definition bloomfilter_value_unseen  (hashes: hash_vec)  (b: B) : bool :=
    (* provided the finite maps of all the hash function have not seen the value*)
    all (hash_unseen b) (tval hashes).

  Definition hashes_have_free_spaces  (hashes: hash_vec) (s: nat) : bool :=
    all (hash_has_free_spaces s) (tval hashes).
  
  Lemma evalDist1f (A B: finType) (p : A) :
      evalDist (ret p) = Dist1.d p.     
  Proof. by []. Qed.

  
  

  Lemma bloomfilter_set_get_eq hash_value bf :  bloomfilter_get_bit hash_value (bloomfilter_set_bit hash_value bf).
    Proof.
        by rewrite /bloomfilter_get_bit/bloomfilter_set_bit// /bloomfilter_state FixedList.tnth_set_nth_eq //=.
    Qed.


  
  
  Lemma behead_tupleE n' A p (ps: n'.-tuple A) : (Tuple (behead_tupleP [tuple of p :: ps]) = ps).
    by case: ps (behead_tupleP _ ) => //= xs H H'; rewrite (proof_irrelevance _ H H').
  Qed.
  

    
Lemma ntuple_cons_eq n' A v (vs: n'.-tuple A): FixedList.ntuple_cons v vs = [tuple of v :: vs].
Proof.    

  case: vs => vs Hvs.

  have Hvvs: size (v :: vs) == n'.+1; first by [].
  have Hthead: (thead (Tuple Hvvs)) = v; first by [].
  have: [tuple of v :: Tuple Hvs] = Tuple Hvvs.
  {
    move=>//=; rewrite (tuple_eta (Tuple Hvvs)) => //=; rewrite Hthead //=. 
    rewrite!/[tuple of _ :: _] //=; move: (valP _ ) (valP _) => //= H1 H2;
        rewrite (proof_irrelevance _ H1 H2) //=.
  }
  move=> ->; rewrite /FixedList.ntuple_cons //=; clear Hthead.
  by move: Hvvs (eq_ind _ _ _ _ _ ) =>//= H1 H2; rewrite (proof_irrelevance _ H1 H2).
Qed.

Lemma hash_find_insert_involutive n' value x y : 
FixedList.fixlist_length y + 1 <= n' ->
hashstate_find n' value (hashstate_put n' value x y) = Some x.
Proof.
  rewrite /hashstate_find/hashstate_put//=.
  rewrite addnS addn0.
  elim: n' value x  y => [//=|n' IHn'] value x y .
  rewrite (tuple_eta y) //=.
  rewrite/FixedList.ntuple_head/FixedList.ntuple_tail -/behead_tuple  !theadE ?beheadE ?behead_tupleE //=.

  case: (thead y) => [[k' v']|]//=; first case Hkeq: (k' == value) => //=; rewrite ?eq_refl//=.

  rewrite !ntuple_cons_eq //=.
  rewrite !behead_tupleE Hkeq //= => Hlen.
  apply IHn' => //=.
Qed.


Lemma hash_vec_int_id' (n' k': nat) (hashes: k'.-tuple (HashState n')) value inds ps :
 all (fun y => FixedList.fixlist_length y + 1 <= n') hashes ->
  (d[ hash_vec_int  value (Tuple (hash_vec_insert_length value hashes inds))])
    (ps, inds) = (ps == (Tuple (hash_vec_insert_length value hashes inds)) %R).
Proof.

  move: (hash_vec_insert_length _ _ _) => //=.
  elim: k' n'  inds hashes ps => [//=|k' IHk'] n' [[//=| x xs] Hxs] [[//=|y ys] Hys] ps Hprf Hprf'' //=.
  move: Hprf => //= H0; rewrite Dist1.dE xpair_eqE //=.
  apply Logic.eq_sym; case Heq: (_ == _) => //=.
  by move/eqP: Heq ->; case: ps => //= [//= []] //=; rewrite tuple0 //=.
  by case: ps Heq  => //= [//= []] //= Hprf.

  case: ps => //= [//=[]]; (try by []); move=>  p ps Hps.
  rewrite /FixedList.ntuple_tail.
  move: (behead_tupleP _ ) => //= Hprf'.
  rewrite DistBind.dE.
  rewrite rsum_split //=; under big a _ under big b _ rewrite DistBind.dE.

  under big a _ under big b _ rewrite rsum_split //=.
  under big a _ under big b _ under big c _ under big d _ rewrite Dist1.dE xpair_eqE //=.

  have Hsusp1 (c: HashState n') (a: k'.-tuple (HashState n')) : ( (Tuple Hps) ==  [tuple of c :: a]) = ((p == c) && (ps == a)).
  by rewrite/[tuple of _] //=.
  have Hsusp2 (d: 'I_Hash_size.+1) (b: k'.-tuple 'I_Hash_size.+1) : ( (Tuple Hxs) ==  [tuple of d :: b]) = ((x == d) && (xs == b)).
  by rewrite/[tuple of _] //=.
  under big a _ under big b _ under big c _ under big d _ rewrite Hsusp1 Hsusp2 !boolR_distr eq_sym mulRC -mulRA -mulRA -mulRA.
  under big a _ under big b _ rewrite exchange_big.
  under big a _ under big b _ under big c _ rewrite -rsum_pred_demote big_pred1_eq //=.

  under big b _ under big c _ under big d _ rewrite mulRC eq_sym -mulRA.
  under big b _ under big c _ rewrite -rsum_pred_demote big_pred1_eq.

  under big b _ under big c _ rewrite mulRC -mulRA -mulRA eq_sym.

  have H (c: k'.-tuple 'I_Hash_size.+1): (tval c == xs) = (c == (behead_tuple (Tuple Hxs))).
  by rewrite/behead_tuple //=.

  (under big b _ under big c _ rewrite H); clear H.
  under big b _ rewrite -rsum_pred_demote big_pred1_eq//=.
  have H (b: k'.-tuple (HashState n')): (tval b == ps) = (b == (behead_tuple (Tuple Hps))).
  by rewrite/behead_tuple //=.

  under big b _ rewrite mulRC -mulRA  eq_sym H.
  rewrite -rsum_pred_demote big_pred1_eq.

  move: (IHk' n' (behead_tuple (Tuple Hxs)) (behead_tuple (Tuple Hys)) (behead_tuple (Tuple Hps))) =>//=.
  move=> /(_ Hprf') -> //=; clear IHk'.
  rewrite /hash //=.

  have ->: ((thead (Tuple Hprf)) = (hashstate_put n' value x y)); first by move=>//=.
  rewrite hash_find_insert_involutive //= ?Dist1.dE ?xpair_eqE ?eq_refl //=.
  rewrite ?Bool.andb_true_r.

  have ->: ((Tuple Hps == Tuple Hprf) = ((thead (Tuple Hps)== thead (Tuple Hprf))
           && (behead_tuple (Tuple Hps) == (Tuple Hprf'))));
  move=>//=.
  by rewrite !boolR_distr;apply Logic.eq_sym; rewrite mulRC; apply f_equal => //=.
  by move: Hprf'' => //= /andP [] //=.
  by move: Hprf'' => //= /andP [] //=.
Qed.

Lemma cons_tuple_eq_tuple n' A c (a: n'.-tuple A): 
[tuple of c :: a] = cons_tuple c a.
Proof.
  rewrite/[tuple of _ :: _ ] //=.
Qed.

Lemma hash_vec_int_id (n' k': nat) (hashes: k'.-tuple (HashState n')) value inds ps qs :
 all (fun y => FixedList.fixlist_length y + 1 <= n') hashes ->
  (d[ hash_vec_int  value (Tuple (hash_vec_insert_length value hashes inds))])
    (ps, qs) = ((ps == (Tuple (hash_vec_insert_length value hashes inds))) && (qs == inds) %R).
Proof.

  move=> Hall.

  case Heq: (qs == inds).
  - {
      rewrite Bool.andb_true_r.
        by move/eqP:Heq ->; rewrite hash_vec_int_id'.      
    }

  - rewrite Bool.andb_false_r //=.
  move: (hash_vec_insert_length _ _ _) Heq Hall => //=.
  elim: k' n'  inds hashes ps qs => [//=|k' IHk'] n' [[//=| x xs] Hxs] [[//=|y ys] Hys] ps qs Hprf Hprf''' Hprf''  //=.
  move: Hprf => //= H0; rewrite Dist1.dE xpair_eqE //=.
  apply Logic.eq_sym; case Heq: (_ == _) => //=.

  by move: Hxs Hprf''' => //=; rewrite !tuple0 => Hxs //=.

  case: ps => //= [//=[]]; (try by []); move=>  p ps Hps.
  rewrite /FixedList.ntuple_tail.
  move: (behead_tupleP _ ) => //= Hprf'.
  rewrite DistBind.dE.
  rewrite rsum_split //=; under big a _ under big b _ rewrite DistBind.dE.

  under big a _ under big b _ rewrite rsum_split //=.
  under big a _ under big b _ under big c _ under big d _ rewrite Dist1.dE xpair_eqE //=.

  have Hsusp1 (c: HashState n') (a: k'.-tuple (HashState n')) : ( (Tuple Hps) ==  [tuple of c :: a]) = ((p == c) && (ps == a)).
  by rewrite/[tuple of _] //=.
  have Hsusp2 (d: 'I_Hash_size.+1) (b: k'.-tuple 'I_Hash_size.+1) : ( (Tuple Hxs) ==  [tuple of d :: b]) = ((x == d) && (xs == b)).
  by rewrite/[tuple of _] //=.

  under big a _ under big b _ under big c _ under big d _ rewrite Hsusp1 !boolR_distr eq_sym mulRC -mulRA -mulRA.
  under big a _ under big b _ rewrite exchange_big.
  under big a _ under big b _ under big c _ rewrite -rsum_pred_demote big_pred1_eq //=.

  rewrite exchange_big.
  under big a _ under big b _ rewrite !rsum_Rmul_distr_l ?rsum_Rmul_distr_r. 

  under big a _ rewrite exchange_big; under big c _ under big d _ rewrite mulRC eq_sym -mulRA.

  have Hd' (d: k'.-tuple (HashState n')): ((tval d == ps)) = (d == behead_tuple (Tuple Hps)).
  by rewrite /behead_tuple //=.

  have Hq' (c: 'I_Hash_size.+1) (a: k'.-tuple ('I_Hash_size.+1)):
    (qs == [tuple of c :: a]) = ((c == thead qs) && (a == behead_tuple qs)).
  {
    rewrite/cons_tuple; rewrite -xcons_eqE eq_sym //=; rewrite (tuple_eta qs).
    rewrite !theadE !beheadE//= ; case: qs Hprf''' => [[| q qs] Hqs] Hprf'''//=.
  }

  rewrite/[tuple of _ :: _] //=.
  
  move=>//=.
  under big a _ under big b _ under big c _ rewrite Hd'.
  under big a _ under big b _ rewrite -rsum_pred_demote  big_pred1_eq //=.

  under big a _ under big b _  rewrite Hq' boolR_distr -mulRA -mulRA.
  under big a _ rewrite -rsum_pred_demote big_pred1_eq.
  rewrite -rsum_pred_demote big_pred1_eq.

  clear Hq'.
  case: qs Hprf''' => [[//=|q qs] Hqs]//= Hprf'''.
  have: ((q :: qs) == (x :: xs)) = false; first by clear Hprf Hsusp2; move: Hqs Hxs Hprf''' => //=.

  move=>/Bool.negb_true_iff; rewrite negb_consP =>/orP [Hneq| Heqf]; last first.

  - {
      move: (IHk' n' (behead_tuple (Tuple Hxs)) (behead_tuple (Tuple Hys)) (behead_tuple (Tuple Hps)) (behead_tuple (Tuple Hqs))) =>//= -> //=; first by rewrite mulR0.
  clear Hprf Hsusp2 Hprf'''; move: Hqs Hxs Heqf =>//=.
  rewrite/behead_tuple//= => Hqs Hxs Hneq; move: (behead_tupleP _) (behead_tupleP _) =>//= H1 H2.
    by rewrite tuple_eq_inj //=; apply /Bool.negb_true_iff.
    by move: Hprf'' => //= /andP [].
  }
  - {
      rewrite mulR_eq0; left => //=; have ->: (thead (Tuple Hqs)) = q; first by [].
      have ->: (thead (Tuple Hprf)) = hashstate_put n' value x y; first by [].
      rewrite/hash.
      rewrite hash_find_insert_involutive //= ?Dist1.dE ?xpair_eqE ?eq_refl //=.
      by move/Bool.negb_true_iff: Hneq ->; rewrite Bool.andb_false_r //=.
        by move: Hprf'' => //= /andP [] //=.
    }

Qed.


     

Lemma hash_vec_simpl_inv' (n' k': nat) (hashes: k'.-tuple (HashState n')) value inds f :
  all
    (fun y : FixedList.fixlist [eqType of B * 'I_Hash_size.+1] n' =>
     FixedList.fixlist_length y + 1 <= n') hashes ->
  (\rsum_(hshs' in [finType of k'.-tuple (HashState n')])
   ((d[ hash_vec_int  value (Tuple (hash_vec_insert_length value hashes inds))]) (hshs', inds) *R* (f hshs'))) =
  ((f (Tuple (hash_vec_insert_length value hashes inds)))).
Proof.
  move=> H1.
  under big hshs' _ rewrite hash_vec_int_id' //=.
  by rewrite -rsum_pred_demote big_pred1_eq //=.
Qed.

      

Lemma bloomfilter_set_bitC bf ind ind':
  (bloomfilter_set_bit ind (bloomfilter_set_bit ind' bf)) =
  (bloomfilter_set_bit ind' (bloomfilter_set_bit ind bf)).
Proof.
  rewrite /bloomfilter_set_bit/bloomfilter_state//.
  apply f_equal => //.
  apply eq_from_tnth => pos.
  case Hpos: (pos == ind); case Hpos': (pos == ind').
  - by rewrite !FixedList.tnth_set_nth_eq.
  - rewrite FixedList.tnth_set_nth_eq; last by [].
    rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos' ->.
      by rewrite FixedList.tnth_set_nth_eq; last by [].
  - rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos ->.
    rewrite FixedList.tnth_set_nth_eq; last by [].
      by rewrite FixedList.tnth_set_nth_eq; last by [].

  - rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos ->.  
    rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos' ->.
    rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos' ->.  
      by rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos ->.
Qed.


Lemma bloomfilter_add_internal_hit bf (ind: 'I_Hash_size.+1) hshs :
  (ind \in hshs) ->
  (tnth (bloomfilter_state (bloomfilter_add_internal hshs bf)) ind).
Proof.
  elim: hshs bf  => //= hsh hshs IHs bf.

  rewrite in_cons => /orP [/eqP -> | H]; last by apply IHs.

  clear IHs ind Hkgt0.
  elim: hshs bf hsh => //.
  - rewrite /bloomfilter_add_internal/bloomfilter_set_bit/bloomfilter_state //.
      by move=> bf hsh; rewrite FixedList.tnth_set_nth_eq => //=.
  - move=> hsh hshs IHs bf hsh'.    
    move=> //=.
    rewrite bloomfilter_set_bitC .
      by apply IHs.
Qed.

Lemma bloomfilter_add_internal_preserve bf ind hshs:
  tnth (bloomfilter_state bf) ind ->
  tnth (bloomfilter_state (bloomfilter_add_internal hshs bf)) ind.
Proof.

  elim: hshs bf ind => //= hsh hshs IHs bf ind Htnth.
  apply IHs.
  rewrite /bloomfilter_set_bit/bloomfilter_state //.
  case Hhsh: (ind == hsh).
  - by rewrite FixedList.tnth_set_nth_eq //=.
  - rewrite FixedList.tnth_set_nth_neq; first by move: Htnth; rewrite/bloomfilter_state//=.
      by move/Bool.negb_true_iff: Hhsh.
Qed.


Lemma bloomfilter_add_internal_miss
      bf (ind: 'I_Hash_size.+1) hshs :
  ~~ tnth (bloomfilter_state bf) ind ->
  ~~ ( ind \in hshs) ->
  (~~ tnth (bloomfilter_state (bloomfilter_add_internal hshs bf)) ind).
Proof.

  move=> Htnth.
  elim: hshs bf Htnth => //= hsh hshs IHs bf Htnth.
  move=> H; move: (H).
  rewrite in_cons.
  rewrite negb_or => /andP [Hneq Hnotin].
  apply IHs.
  rewrite /bloomfilter_state/bloomfilter_set_bit.
  rewrite FixedList.tnth_set_nth_neq => //=.
  exact Hnotin.
Qed.


Lemma bloomfilter_add_internal_hit_infer bf (ind: 'I_Hash_size.+1) inds:
  ~~ bloomfilter_get_bit ind bf ->
  tnth (bloomfilter_state (bloomfilter_add_internal inds bf)) ind ->
  ind \in inds.
Proof.
  move=> Hbit Htnth.
  case Hind: (ind \in inds) =>//=; move/Bool.negb_true_iff: Hind => Hind.
    by move/Bool.negb_true_iff: (bloomfilter_add_internal_miss Hbit Hind) Htnth ->.
Qed.


Lemma bloomfilter_add_internal_prob bf x l:
  ~~ tnth (bloomfilter_state bf) x ->
     \rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
        ((tnth (bloomfilter_state (bloomfilter_add_internal b bf)) x %R) *R*
         ((Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l)) = 
     (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l)).
Proof.
  elim: l x bf=> [|l IHl] x bf Hnth //=.
  rewrite subRR.
  rewrite unlock.

  have: (index_enum [finType of 0.-tuple 'I_Hash_size.+1]) = [tuple]::[::]; last move=>->//=.     
       rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
       rewrite -enumT //=; rewrite/(enum _)//=.
       rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
       move: (FinTuple.size_enum 0 (ordinal_finType Hash_size.+1))=> //=; rewrite expn0.
       move: (FinTuple.enum _ _)=>[|[[|//=] Hz] []]//= _.
       by move: (@tuple0  'I_Hash_size.+1 (Tuple Hz)) <- =>//=.
  by move/Bool.negb_true_iff: Hnth ->; rewrite //= mul0R add0R.     

  rewrite rsum_tuple_split rsum_split//=.
  rewrite (bigID (fun a => a == x)) big_pred1_eq //=.

  have: (\rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
          ((tnth (bloomfilter_state (bloomfilter_add_internal b (bloomfilter_set_bit x bf))) x %R) *R*
           (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) =
         \rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
          ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l.+1)))).
         apply eq_bigr=> b _.
         rewrite bloomfilter_add_internal_preserve; first by rewrite mul1R//=.
         rewrite /bloomfilter_set_bit/bloomfilter_state.
         by rewrite FixedList.tnth_set_nth_eq.
  move=>->; rewrite bigsum_card_constE//=.

  have: (
          \rsum_(i < Hash_size.+1 | i != x) \rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
         ((tnth (bloomfilter_state (bloomfilter_add_internal b (bloomfilter_set_bit i bf))) x %R) *R*
          (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))
          = (\rsum_(i < Hash_size.+1 | i != x)
              (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ l))))); last move=>->.
            apply eq_bigr=> i Hneq.

            transitivity (
                Rdefinitions.Rinv (Hash_size.+1 %R) *R* 
                \rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
                 ((tnth
                     (bloomfilter_state
                        (bloomfilter_add_internal b (bloomfilter_set_bit i bf))) x %R) *R*
                  ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) 
               ).
                  rewrite rsum_Rmul_distr_l; apply eq_bigr=>b _.
                  by rewrite mulRA mulRC mulRA mulRC; apply f_equal; rewrite mulRC; apply f_equal.
            rewrite IHl; first by [].
            rewrite (FixedList.tnth_set_nth_neq) //=.
            by rewrite eq_sym.
   rewrite bigsum_card_constE//=.
   rewrite card_tuple.
   rewrite cardC1 card_ord //=.


   have: (((Hash_size.+1 ^ l %R) *R*
           (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) =
          Rdefinitions.Rinv (Hash_size.+1 %R)
         ); last move=>->.

            rewrite -{3}(mulR1 (Rdefinitions.Rinv _)) mulRA mulRC mulRA mulRC ; apply f_equal.
            rewrite -natRexp; clear; elim: l => [|l IHl] //=; rewrite ?mulR1//=.
            transitivity (
                (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Hash_size.+1 %R)) *R*
                (((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R* (((Hash_size.+1 %R) ^R^ l)))
              ).
            rewrite -mulRA -mulRA mulRC mulRA mulRC; apply f_equal.
            rewrite  mulRC mulRA mulRC; apply f_equal.
            by rewrite mulRC.
            rewrite !Raxioms.Rinv_l ?mul1R ?IHl //=.
            by apply RIneq.not_0_INR =>//=.

   rewrite !RIneq.Rmult_minus_distr_l.

   rewrite addRA //= mulR1.

   rewrite -{1}(mul1R (Rdefinitions.Rinv _)) -RIneq.Rmult_plus_distr_r.

   have: (Rdefinitions.IZR 1 = (1 %R)); last move=>->; first by [].
   rewrite -natRD add1n RIneq.Rinv_r //= .
   rewrite addR_opp mulRA.

   have: (((Hash_size %R) *R* Rdefinitions.Rinv (Hash_size.+1 %R))) = ((1 %R) -R- Rdefinitions.Rinv (Hash_size.+1 %R)); last move=>->.

           rewrite -{2}(mulR1 (Rdefinitions.Rinv _)) //=.

           have: (1 %R) = Rdefinitions.IZR 1; last move=>->; first by [].
           rewrite -{1}(RIneq.Rinv_r (Hash_size.+1 %R)).
           rewrite [(_.+1 %R) *R* Rdefinitions.Rinv _]mulRC.
           rewrite -(RIneq.Rmult_minus_distr_l).
           have: (Rdefinitions.IZR 1 = (1 %R)); last move=>->; first by [].
           by rewrite -natRB //= subn1 //= mulRC.
                 by apply RIneq.not_0_INR =>//=.

                 
   have: (1 %R) = Rdefinitions.IZR 1; last move=>->; first by [].
   by [].
   by apply RIneq.not_0_INR =>//=.
Qed.





  (* for a given index ind *)
  Lemma bloomfilter_addn hashes (ind: 'I_(Hash_size.+1)) (bf: BloomFilter) (value: B):
    (* provided the bloom filter is not full *)
    hashes_not_full hashes ->
    (* and that the bloom filter has not set the value *)
    bloomfilter_value_unseen hashes value ->
    (* the bit in question is not set  *)
    ~~ bloomfilter_get_bit ind bf ->
    P[
        (
          (* bf' is the result of inserting into bf *)
          res <-$ bloomfilter_add  value hashes bf;
          let: (new_hashes, bf') := res in
            (* the probability of the given bit being set is *)
            ret (~~ bloomfilter_get_bit ind bf')
        )
      ] = 
     ((1 -R- Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ k).
  Proof.
    rewrite /bloomfilter_add/hashes_not_full/bloomfilter_value_unseen/hash_unseen /hash_not_full /bloomfilter_get_bit  => /allP Hnfl /allP Husn Hunset //= .  
    rewrite !DistBind.dE //=.

    transitivity (
        \rsum_(exp_hashes in [finType of k.-tuple (HashState n)])
         \rsum_(exp_bf in [finType of BloomFilter])
         \rsum_(exp_hashes' in [finType of k.-tuple (HashState n)])
         \rsum_(exp_bf' in [finType of k.-tuple 'I_Hash_size.+1])
         (((true == ~~ tnth (bloomfilter_state exp_bf) ind) %R) *R*
          ((d[ hash_vec_int value hashes]) (exp_hashes', exp_bf') *R*
           ((exp_hashes == exp_hashes') && (exp_bf == bloomfilter_add_internal exp_bf' bf) %R)))).
         - rewrite rsum_split.
           apply eq_bigr => exp_hashes _.
           apply eq_bigr => exp_bf _.
           rewrite DistBind.dE//= Dist1.dE rsum_Rmul_distr_r.
           rewrite rsum_split => //=.
           apply eq_bigr => exp_hashes' _.
           apply eq_bigr => exp_bf' _.
             by rewrite Dist1.dE//= xpair_eqE.

    transitivity (
        \rsum_(exp_bf' in [finType of k.-tuple 'I_Hash_size.+1])
         \rsum_(exp_hashes in [finType of k.-tuple (HashState n)])
         \rsum_(exp_bf in [finType of BloomFilter])
              (((true == ~~ tnth (bloomfilter_state exp_bf) ind) %R) *R*
               ((d[ hash_vec_int value hashes]) (exp_hashes, exp_bf') *R*
                ((exp_bf == bloomfilter_add_internal exp_bf' bf) %R)))
    ).

         - apply Logic.eq_sym; rewrite exchange_big; apply eq_bigr => exp_hashes _ //=.
           rewrite exchange_big; apply eq_bigr => exp_bf _ //=.
           apply Logic.eq_sym; rewrite exchange_big; apply eq_bigr => exp_bf' _ //=.
           rewrite (bigID (fun exp_hashes' => exp_hashes' == exp_hashes)) //=.
           have H x y z : (y = (0 %R)) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
           apply H.
           apply prsumr_eq0P => exp_hashes' /Bool.negb_true_iff Heq; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
           by rewrite [exp_hashes == _]eq_sym Heq //= !mulR0.
           rewrite big_pred1_eq; do ?(apply f_equal).
           by rewrite eq_refl Bool.andb_true_l.
           

    transitivity (       
        \rsum_(exp_bf in [finType of k.-tuple 'I_Hash_size.+1])
         \rsum_(exp_hashes in [finType of k.-tuple (HashState n)])
           (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal exp_bf bf)) ind) %R) *R*
            ((d[ hash_vec_int value hashes]) (exp_hashes, exp_bf)))
      ).
         - apply eq_bigr => exp_bf _; apply eq_bigr => exp_hashes _.
           rewrite (bigID (fun exp_bf' => exp_bf' == (bloomfilter_add_internal exp_bf bf))).
           have H x y z : (y = (0 %R)) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
           apply H.
           apply prsumr_eq0P => exp_bf' /Bool.negb_true_iff -> //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
           by rewrite !mulR0.
           by rewrite big_pred1_eq eq_refl //= mulR1.
      (*
        Sum has now been simplified to simplest form:
         \rsum_(hs in k.-tuple (HashState n))
            \rsum_(hashs in k.-tuple 'I_Hash_size.+1)
               ((d[ hash_vec_int Hkgt0 value hashes (Hpredkvld Hkgt0)]) (hs, hashs) *R*
                (tnth (bloomfilter_state (bloomfilter_add_internal hashs bf)) ind %R)) =
         ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k %R))
       *)              
      (*
         It is also clear now why the probability is the the way it is - given that bit at ind is unset at the start,
         the probability it will be set after bloomfilter_add_internal is equal to the probability that all the k hashes
         produced by hash_vec_int are 0 (where each hash has a probability of 1 - 1/HashSize of not selecting ind
       *)

        move: (Hpredkvld Hkgt0).

        move:  Hkgt0 hashes Hnfl Husn; rewrite /hash_vec.
        elim: k   => //=.
        clear k Hkgt0.
        case=> [ _  |k IHk] Hkgt0 hashes Hnfl Husn.
                      - move=> _ //=.
                        rewrite mulR1.

                        transitivity (
                            \rsum_(exp_bf in [finType of 1.-tuple 'I_Hash_size.+1])
                             \rsum_(exp_hashes in [finType of 1.-tuple (HashState n)])
                             \rsum_(hashes' in [finType of 0.-tuple (HashState n)])
                             \rsum_(values' in [finType of 0.-tuple 'I_Hash_size.+1])
                             \rsum_(hashes'' in hashstate_of_finType n)
                             \rsum_(values'' in ordinal_finType Hash_size.+1)
  ((((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal exp_bf bf)) ind) %R) *R*
    ((hashes' == [tuple]) && (values' == [tuple]) %R)) *R*
   ((d[ hash n value (thead hashes)]) (hashes'', values'') *R*
    ((exp_hashes == [tuple of hashes'' :: hashes']) && (exp_bf == [tuple of values'' :: values']) %R)))
                          ).

                               - apply eq_bigr => exp_bf _.
                                 apply eq_bigr => exp_hashes _.
                                 rewrite mulRC DistBind.dE rsum_Rmul_distr_r //=.
                                 rewrite rsum_split.
                                 apply eq_bigr => hashes' _.
                                 apply eq_bigr => values' _.
                                 rewrite Dist1.dE xpair_eqE //=.
                                 rewrite mulRA mulRC DistBind.dE !rsum_Rmul_distr_r.
                                 rewrite rsum_split.
                                 apply eq_bigr => hashes'' _.
                                 apply eq_bigr => values'' _ //=.
                                 by rewrite Dist1.dE xpair_eqE//=.

                        transitivity (
                            \rsum_(exp_hashes in [finType of 1.-tuple (HashState n)])
                             \rsum_(hashes' in [finType of 0.-tuple (HashState n)])
                             \rsum_(values' in [finType of 0.-tuple 'I_Hash_size.+1])
                             \rsum_(hashes'' in hashstate_of_finType n)
                             \rsum_(values'' in ordinal_finType Hash_size.+1)
                             ((((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal [tuple of values'' :: values'] bf)) ind)
                       %R) *R* ((hashes' == [tuple]) && (values' == [tuple]) %R)) *R*
                              ((d[ hash n value (thead hashes)])
                        (hashes'', values'') *R*

                               ((exp_hashes == [tuple of hashes'' :: hashes']) %R)))
                          ).

                               - rewrite exchange_big; apply eq_bigr => exp_hashes _.
                                 rewrite exchange_big; apply eq_bigr => hashes' _.
                                 rewrite exchange_big; apply eq_bigr => values' _.
                                 rewrite exchange_big; apply eq_bigr => hashes'' _.
                                 rewrite exchange_big; apply eq_bigr => values'' _.
                                 rewrite (bigID (fun i => i == [tuple of values'' :: values'])).

                                 have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
                                 apply H.

                                 apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                 by rewrite //= Bool.andb_false_r !mulR0.
                                 by rewrite big_pred1_eq eq_refl //= !Bool.andb_true_r.

                        transitivity (
                             \rsum_(hashes'' in hashstate_of_finType n)
                             \rsum_(values'' in ordinal_finType Hash_size.+1)
                             ((((true == ~~ tnth (bloomfilter_state (
                                                      bloomfilter_add_internal [tuple of values'' :: [tuple]] bf)) ind) %R) *R*
                              ((d[ hash n value (thead hashes)])
                                 (hashes'', values''))))
                          ).                                 
                               - rewrite exchange_big.
                                 rewrite (bigID (fun i => i == [tuple])) big_pred1_eq.
                                 have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
                                 apply H.

                                      - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by  dispatch_Rgt.
                                        apply prsumr_eq0P => i' _ //=; first by dispatch_Rgt.
                                        apply prsumr_eq0P => values' _ //=; first by dispatch_Rgt.
                                        apply prsumr_eq0P => hashes''  _ //=; first by dispatch_Rgt.
                                        apply prsumr_eq0P => values''  _ //=; first by dispatch_Rgt.
                                          by rewrite !mulR0 mul0R.

                                 rewrite exchange_big //= (bigID (fun i => i == [tuple])) big_pred1_eq //=. 
                                 apply H.
                                       - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=;  first by dispatch_Rgt. 
                                         apply prsumr_eq0P => i' _ //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                         apply prsumr_eq0P => values' _ //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                         apply prsumr_eq0P => hashes''  _ //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                           by rewrite !mulR0 mul0R.
                                rewrite exchange_big; apply eq_bigr => hashes'' _.
                                rewrite exchange_big; apply eq_bigr => values'' _.
                                rewrite (bigID (fun i => i == [tuple hashes''])) big_pred1_eq //=.

                                apply H.
                                     - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                         by rewrite !mulR0.
                                rewrite mulR1; do ?(apply f_equal).
                                  by rewrite (eq_refl [tuple hashes'']) //= mulR1.

                                rewrite /hash/hashstate_find.
                                have Hthead: (thead hashes) \in hashes.
                                by clear; rewrite (tuple_eta hashes) theadE//=; apply mem_head.
                                move/eqP: (Husn (thead hashes) Hthead) ->.

                                rewrite exchange_big (bigID (fun values'' => values'' == ind)).

                                have H x y z: y = (0 %R) -> x = z -> y +R+ x = z.
                                by move=> -> ->; rewrite add0R.

                                apply H.
                                     - apply prsumr_eq0P => ind' /eqP ->; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                       rewrite bloomfilter_add_internal_hit //=.
                                       apply prsumr_eq0P => i' _; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                       by rewrite mul0R.
                                       by apply mem_head.

                        transitivity ( 
                            \rsum_(i in 'I_Hash_size.+1 | i != ind)
                             \rsum_(i0 in hashstate_of_finType n)
                             ((d[ rnd <-$ gen_random; ret (hashstate_put n value rnd (thead hashes), rnd)]) (i0, i))
                          ).

                                     - apply eq_bigr => ind' /andP [_ Hnind].
                                       apply eq_bigr => vl _.
                                       rewrite bloomfilter_add_internal_miss.
                                       by rewrite eq_refl //= mul1R.
                                       by [].
                                       by rewrite mem_seq1 eq_sym. 

                        move=> //=.               

                        transitivity (
                            \rsum_(i < Hash_size.+1 | i != ind)
                             \rsum_(hs in [finType of HashState n])
                             \rsum_(hs' in [finType of 'I_Hash_size.+1])
                             \rsum_(i' in ordinal_finType Hash_size.+1)
                             (((hs == hashstate_put n value hs' (thead hashes)) && (i == hs') %R) *R*
                              (Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R) *R* ((hs' == i') %R)))
                          ).
                              - apply eq_bigr => i Hneq.
                                apply eq_bigr => hs _.
                                rewrite DistBind.dE.
                                apply eq_bigr => hs' _.
                                rewrite DistBind.dE rsum_Rmul_distr_r.
                                apply eq_bigr => i' _.
                                by rewrite !Dist1.dE Uniform.dE xpair_eqE.

                        transitivity (        
                            \rsum_(i < Hash_size.+1 | i != ind)
                             \rsum_(hs in [finType of HashState n])
                             \rsum_(i' in ordinal_finType Hash_size.+1)
                             (((hs == hashstate_put n value i' (thead hashes)) && (i == i') %R) *R*
                              (Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R)))
                          ).

                              - apply eq_bigr => i Hneq.
                                apply eq_bigr => hs _.
                                rewrite exchange_big; apply eq_bigr=> i' _.
                                rewrite (bigID (fun i0 => i0 == i')) //= addRC.
                                apply H.
                                      - apply prsumr_eq0P => i0 /Bool.negb_true_iff ->; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
                                          by rewrite //= !mulR0.

                                by rewrite big_pred1_eq eq_refl //= mulR1; do ?(apply f_equal).
                        transitivity (
                            \rsum_(i < Hash_size.+1 | i != ind)
                             Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R)
                          ).

                                      - apply eq_bigr => i Hneq.
                                        rewrite exchange_big (bigID (fun i' => i' == i)) //= addRC.
                                        apply H.
                                             - apply prsumr_eq0P => i0 /Bool.negb_true_iff Heq; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
                                               apply prsumr_eq0P => i1 _; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
                                               by rewrite eq_sym in Heq; rewrite Heq //= Bool.andb_false_r //= mul0R.
                                        rewrite big_pred1_eq.       
                                        rewrite (bigID (fun i0 => i0 == hashstate_put n value i (thead hashes))) big_pred1_eq //= addRC.

                                        apply H.
                                             - apply prsumr_eq0P => i0 /Bool.negb_true_iff ->; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
                                               by rewrite //= mul0R.

                                        by rewrite !eq_refl Bool.andb_true_l //= mul1R.       
                        apply prsumr_sans_one => //=.
                        by rewrite card_ord.
                        rewrite bigsum_card_constE card_ord RIneq.Rinv_r //=.
                        by apply RIneq.not_0_INR => //=.
                        (* Base case completed *) 

                        move=> Hpredkvld .
                        rewrite -(IHk _ (FixedList.ntuple_tail hashes)); last first.
                             - by rewrite -pred_Sn.
                             - destruct hashes eqn: Hhashes => ls.
                               clear Hnfl; move: tval i Hhashes Husn => [//= | x [//=| y xs]] Hprf Heq Hnfl.
                               rewrite FixedList.ntuple_tail_coerce => Hin; apply Hnfl => //=.
                                 by move: Hin; rewrite [ls \in [:: x, y & xs]]in_cons /tval => ->; rewrite Bool.orb_true_r.

                             - destruct hashes eqn: Hhashes => ls.
                               clear Husn; move: tval i Hhashes Hnfl => [//= | x [//= | y xs]] Hprf Heq Husn.
                               rewrite FixedList.ntuple_tail_coerce => Hin; apply Husn => //=.
                                 by move: Hin; rewrite [ls \in [:: x, y & xs]]in_cons /tval => ->; rewrite Bool.orb_true_r.
                             - by apply ltn0Sn.
                             - rewrite mulRC !rsum_Rmul_distr_r.
                               transitivity (
                                   \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                    \rsum_(ind' in 'I_Hash_size.+1)
                                    \rsum_(h in hashstate_of_finType n)
                                    \rsum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
                                    \rsum_(exp_hashes in tuple_finType k.+1 (hashstate_of_finType n))
                                    \rsum_(result in tuple_finType k.+1 (ordinal_finType Hash_size.+1))
                                    (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
                                     ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
                                      (d[ hash_vl <-$ hash n value (thead hashes);
                                          (let (new_hsh_fun, result0) := hash_vl in
                                           ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                                        (cons_tuple h hs, cons_tuple ind' inds)))
                                 ).
                                  - rewrite rsum_tuple_split rsum_split exchange_big.
                                    apply eq_bigr => inds _.
                                    apply eq_bigr => ind' _.
                                    rewrite rsum_tuple_split rsum_split.
                                    apply eq_bigr => h _.
                                    apply eq_bigr => hs _.
                                    rewrite DistBind.dE mulRC rsum_Rmul_distr_r rsum_split.

                                    apply eq_bigr => exp_hashes _.
                                    by apply eq_bigr => result _.

                               transitivity (
                                  \rsum_(result in tuple_finType k.+1 (ordinal_finType Hash_size.+1))
                                   \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                    \rsum_(ind' in 'I_Hash_size.+1)
                                    \rsum_(h in hashstate_of_finType n)
                                    \rsum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
                                    \rsum_(exp_hashes in tuple_finType k.+1 (hashstate_of_finType n))
                                    (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
                                     ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
                                      (d[ hash_vl <-$ hash n value (thead hashes);
                                          (let (new_hsh_fun, result0) := hash_vl in
                                           ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                                        (cons_tuple h hs, cons_tuple ind' inds)))
                                 ).

                                  - apply Logic.eq_sym.
                                    rewrite exchange_big; apply eq_bigr => inds _.
                                    rewrite exchange_big; apply eq_bigr => ind' _.
                                    rewrite exchange_big; apply eq_bigr => h _.
                                    rewrite exchange_big; apply eq_bigr => hs _.
                                    by rewrite exchange_big; apply eq_bigr => exp_hashes _.


                               apply eq_bigr => result _.
                               rewrite mulRC rsum_Rmul_distr_r.

                               transitivity (
                                   \rsum_(exp_hashes in tuple_finType k.+1 (hashstate_of_finType n))
                                   \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                    \rsum_(ind' in 'I_Hash_size.+1)
                                    \rsum_(h in hashstate_of_finType n)
                                    \rsum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
                                    (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
                                     ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
                                      (d[ hash_vl <-$ hash n value (thead hashes);
                                          (let (new_hsh_fun, result0) := hash_vl in
                                           ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                                        (cons_tuple h hs, cons_tuple ind' inds)))
                                 ).
                                  - apply Logic.eq_sym.
                                    rewrite exchange_big; apply eq_bigr => inds _.
                                    rewrite exchange_big; apply eq_bigr => ind' _.
                                    rewrite exchange_big; apply eq_bigr => h _.
                                    by rewrite exchange_big; apply eq_bigr => hs _.


                               apply eq_bigr => exp_hashes _.


                               transitivity (
                                   \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                    \rsum_(ind' in 'I_Hash_size.+1)
                                    \rsum_(h in hashstate_of_finType n)
                                    \rsum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
                                    ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
                                     (((true ==
                                        ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
                                      (d[ hash_vl <-$ hash n value (thead hashes);
                                          (let (new_hsh_fun, result0) := hash_vl in
                                           ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                                        (cons_tuple h hs, cons_tuple ind' inds))
                                    )
                                 ).
                                  - apply eq_bigr => inds _.
                                    apply eq_bigr => ind' _.
                                    apply eq_bigr => h _.
                                    apply eq_bigr => hs _.
                                    rewrite mulRC -mulRA.
                                    apply f_equal.
                                    by rewrite mulRC.

                               transitivity (
                                   (d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
                                   \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                    \rsum_(ind' in 'I_Hash_size.+1)
                                    \rsum_(h in hashstate_of_finType n)
                                    \rsum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
                                    ((((true ==
                                        ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
                                      (d[ hash_vl <-$ hash n value (thead hashes);
                                          (let (new_hsh_fun, result0) := hash_vl in
                                           ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                                        (cons_tuple h hs, cons_tuple ind' inds))
                                    )
                                 ).

                                  - apply Logic.eq_sym.
                                    rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => inds _.
                                    rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => ind' _.
                                    rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => h _.
                                    by rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => hs _.

                                  apply Logic.eq_sym; rewrite mulRA mulRC; apply f_equal; apply Logic.eq_sym.


                              transitivity (
                                  \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                   \rsum_(ind' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in hashstate_of_finType n)
                                   \rsum_(result' in ordinal_finType Hash_size.+1)
                                   \rsum_(hshs in [finType of 'I_Hash_size.+1])
                                   \rsum_(hshs' in ordinal_finType Hash_size.+1)
  ((((true ==
      ~~ tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit ind' bf))) ind)
     %R) *R* ([&& (h == hs_fun') && (hs == exp_hashes), ind' == result' & inds == result] %R)) *R*
   ((((hs_fun', result') == (hashstate_put n value hshs (thead hashes), hshs)) %R) *R*
    (Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R) *R* ((hshs == hshs') %R))))

                              ).
                                  - apply eq_bigr => inds _.
                                    apply eq_bigr => ind' _.
                                    apply eq_bigr => h _.
                                    apply eq_bigr => hs _.
                                    rewrite //= DistBind.dE mulRC rsum_Rmul_distr_r //=.
                                    rewrite rsum_split.
                                    apply eq_bigr => hs_fun' _.
                                    apply eq_bigr => result' _.
                                    rewrite /hash/hashstate_find.
                                    have Hhead: (thead hashes \in hashes). by rewrite (tuple_eta hashes) //= theadE; apply mem_head.
                                    move /eqP: (Husn (thead hashes) Hhead) ->.
                                    rewrite mulRC //= DistBind.dE !rsum_Rmul_distr_r.
                                    apply eq_bigr => hshs _.
                                    rewrite !Dist1.dE !DistBind.dE xpair_eqE !xcons_eqE mulRA mulRC !rsum_Rmul_distr_r.
                                    apply eq_bigr => hshs' _.
                                    by rewrite Uniform.dE Dist1.dE.


                              rewrite (bigID (fun inds => inds == result)) //=.      

                              have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
                              apply H.

                                 - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => ind' _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => h _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => hs _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => result' _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => hshs _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => hshs' _//=; first by dispatch_Rgt; move => [] //=.
                                     by rewrite !Bool.andb_false_r //= mulR0 mul0R.

                              rewrite big_pred1_eq.        

                              transitivity (
                                  \rsum_(result' in 'I_Hash_size.+1)
                                   \rsum_(ind' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in [finType of HashState n])
                                   \rsum_(hshs in 'I_Hash_size.+1)
                                   \rsum_(hshs' in 'I_Hash_size.+1)
                                   ((((true == ~~ tnth
                                                  (bloomfilter_state
                                                     (bloomfilter_add_internal result (bloomfilter_set_bit ind' bf))) ind) %R) *R*
                                     ([&& (h == hs_fun') && (hs == exp_hashes), ind' == result'
                                                                                & result == result] %R)) *R*
                                    ((((hs_fun', result') == (hashstate_put n value hshs (thead hashes), hshs)) %R) *R*
                                     (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
                                  ).

                                 - apply Logic.eq_sym.
                                   rewrite exchange_big; apply eq_bigr => ind' _.
                                   rewrite exchange_big; apply eq_bigr => h _.
                                   rewrite exchange_big; apply eq_bigr => hs _.
                                   by rewrite exchange_big; apply eq_bigr => hs_fun' _.

                              transitivity (     
                                  \rsum_(result' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in [finType of HashState n])
                                   \rsum_(hshs in 'I_Hash_size.+1)
                                   \rsum_(hshs' in 'I_Hash_size.+1)
                                   ((((true == ~~ tnth
                                                  (bloomfilter_state
                                                     (bloomfilter_add_internal result (bloomfilter_set_bit result' bf))) ind) %R) *R*
                                     ([&& (h == hs_fun') & (hs == exp_hashes) ] %R)) *R*
                                    ((((hs_fun', result') == (hashstate_put n value hshs (thead hashes), hshs)) %R) *R*
                                     (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
                                   ).

                                  apply eq_bigr => result' _.

                                  rewrite (bigID (fun ind' => ind' == result')) big_pred1_eq.
                                  apply H.
                                      - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move => [] //=.
                                        apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
                                        apply prsumr_eq0P => hs _; first by dispatch_Rgt; move=> [] //=.
                                        apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.
                                        apply prsumr_eq0P => hshs _; first by dispatch_Rgt; move=> [] //=.
                                        apply prsumr_eq0P => hshs' _; first by dispatch_Rgt; move=> [] //=.

                                        by rewrite eq_refl Bool.andb_true_r Bool.andb_false_r //= mulR0 mul0R.

                                  apply eq_bigr => h _.
                                  apply eq_bigr => hs _.
                                  apply eq_bigr => hs_fun' _.
                                  apply eq_bigr => hshs' _.
                                  apply eq_bigr => hshs _.
                                    by rewrite !eq_refl !Bool.andb_true_r.

                              transitivity (   
                                 \rsum_(hshs' in 'I_Hash_size.+1)
                                  \rsum_(result' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in [finType of HashState n])
                                   \rsum_(hshs in 'I_Hash_size.+1)

                                   ((((true == ~~ tnth
                                         (bloomfilter_state
                                            (bloomfilter_add_internal result (bloomfilter_set_bit result' bf))) ind)
                                        %R) *R* ((h == hs_fun') && (hs == exp_hashes) %R)) *R*
                                    ((((hs_fun' == hashstate_put n value hshs (thead hashes)) && (result' == hshs)) %R) *R*
                                     (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
                                               ).
                                      - apply Logic.eq_sym.

                                        rewrite exchange_big; apply eq_bigr => result' _.
                                        rewrite exchange_big; apply eq_bigr => h _.
                                        rewrite exchange_big; apply eq_bigr => hs _.
                                        rewrite exchange_big; apply eq_bigr => hshs _.
                                        rewrite exchange_big; apply eq_bigr => hshs' _.
                                        apply eq_bigr => hshs'' _.
                                        by rewrite xpair_eqE.

                              transitivity (          
                                   \rsum_(hshs' in 'I_Hash_size.+1)
                                   \rsum_(hshs in 'I_Hash_size.+1)
                                   \rsum_(result' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in [finType of HashState n])
                                   ((((true ==
                                       ~~
                                         tnth
                                         (bloomfilter_state
                                            (bloomfilter_add_internal result (bloomfilter_set_bit result' bf))) ind)
                                        %R) *R* ((h == hs_fun') && (hs == exp_hashes) %R)) *R*
                                    (((hs_fun' == hashstate_put n value hshs (thead hashes)) && (result' == hshs) %R) *R*
                                     (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
 ).

                                      - apply eq_bigr => hshs' _; apply Logic.eq_sym.
                                        rewrite exchange_big; apply eq_bigr => result' _.
                                        rewrite exchange_big; apply eq_bigr => h _.
                                        rewrite exchange_big; apply eq_bigr => hs _.
                                        by rewrite exchange_big; apply eq_bigr => hs_fun' _.


                              transitivity (
                                  \rsum_(hshs' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in [finType of HashState n])
                                   ((((true ==
                                       ~~
                                         tnth
                                         (bloomfilter_state
                                            (bloomfilter_add_internal result (bloomfilter_set_bit hshs' bf))) ind)
                                        %R) *R* ((h == hs_fun') && (hs == exp_hashes) %R)) *R*
                                    (((hs_fun' == hashstate_put n value hshs' (thead hashes))  %R) *R*
                                     (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R))))
                                 ).
                                        apply eq_bigr => hshs' _.
                                        rewrite (bigID (fun hshs => hshs == hshs')) big_pred1_eq.
                                        apply H.

                                              - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => result' _; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => hs _; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.

                                                by rewrite //= !mulR0.

                                        rewrite (bigID (fun result' => result' == hshs')) big_pred1_eq.                                        apply H.
                                              - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => hs _; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.
                                                by rewrite !Bool.andb_false_r //= !mul0R mulR0.

                                        apply eq_bigr => h _.
                                        apply eq_bigr => hs _.
                                        apply eq_bigr => hs_fun' _.
                                        do ?(apply f_equal).
                                        by rewrite eq_refl //= Bool.andb_true_r mulR1.
                              transitivity (                                                  
                                  \rsum_(hshs' in 'I_Hash_size.+1)
                                   \rsum_(hs_fun' in [finType of HashState n])                                
                                   \rsum_(h in [finType of HashState n])
                                
                                   ((((true ==
                                       ~~
                                         tnth
                                         (bloomfilter_state
                                            (bloomfilter_add_internal result (bloomfilter_set_bit hshs' bf))) ind) %R) *R*
                                     ((h == hs_fun')%R)) *R*
                                    (((hs_fun' == hashstate_put n value hshs' (thead hashes)) %R) *R*
                                     Rdefinitions.Rinv (#|'I_Hash_size.+1| %R)))
                                ).

                                              - apply eq_bigr => hshs' _.
                                                apply Logic.eq_sym.
                                                rewrite exchange_big; apply eq_bigr => h _.
                                                apply Logic.eq_sym.
                                                rewrite (bigID (fun hs => hs == exp_hashes)) big_pred1_eq.
                                                apply H.
                                                    - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
                                                      apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.

                                                      by rewrite Bool.andb_false_r //= mulR0 mul0R.

                                                apply eq_bigr => hs_fun' _.      
                                                by rewrite eq_refl Bool.andb_true_r.

                              transitivity (
                                  \rsum_(hshs' in 'I_Hash_size.+1)
                                   ((((true ==
                                       ~~
                                         tnth
                                         (bloomfilter_state (bloomfilter_add_internal result (bloomfilter_set_bit hshs' bf)))
                                         ind) %R)) *R*
                                    (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R)))
                                ).

                                                    - apply eq_bigr => hshs' _.

                                                      rewrite  (bigID (fun hs_fun' => hs_fun' == hashstate_put n value hshs' (thead hashes))) big_pred1_eq.

                                                      apply H.
                                                         - move=>//=;apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
                                                           apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
                                                             by rewrite //= mul0R mulR0.
                                                      rewrite (bigID (fun h => h == hashstate_put n value hshs' (thead hashes))) big_pred1_eq.                                                      

                                                      apply H.
                                                         - move=>//=;apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
                                                             by rewrite //=  !mulR0 mul0R.

                                                      by rewrite !eq_refl //= mulR1 mul1R.       


                                        case Hind: (ind \in result).              
                                            - rewrite !bloomfilter_add_internal_hit //= mulR0.
                                              apply prsumr_eq0P => hshs' _; first by dispatch_Rgt; move=> [] //=.
                                              by rewrite bloomfilter_add_internal_hit //= mul0R.

                                            - move/Bool.negb_true_iff: Hind => Hind.
                                              rewrite bloomfilter_add_internal_miss //= mulR1. 

                                              rewrite (bigID (fun hshs' => hshs' == ind)) big_pred1_eq //= addRC.
                                              apply H.
                                              rewrite bloomfilter_add_internal_preserve; first by rewrite mul0R.

                                              rewrite /bloomfilter_state/bloomfilter_set_bit.
                                              by rewrite FixedList.tnth_set_nth_eq.

                                              transitivity (
                                                  \rsum_(i < Hash_size.+1 | i != ind)
                                                   (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R))
                                                ).
                                                   - apply eq_bigr => i Hneq.
                                                     rewrite bloomfilter_add_internal_miss; first by rewrite //= mul1R.

                                                     rewrite /bloomfilter_state/bloomfilter_set_bit.
                                                     rewrite FixedList.tnth_set_nth_neq //= 1?eq_sym //= 1?Hind.
                                                       by [].
                                                     apply prsumr_sans_one => //=.
                                                       by rewrite card_ord.
                                                       rewrite bigsum_card_constE card_ord RIneq.Rinv_r //=.
                                                         by apply RIneq.not_0_INR => //=.


  (* DONE!!!! *)                                                         
  Qed.



  Definition bloomfilter_add_multiple  hsh_0 bf_0 values :=
           @foldr B (Comp [finType of k.-tuple (HashState n) * BloomFilter])
                (fun val hsh_bf =>
                   res_1 <-$ hsh_bf;
                     let (hsh, bf) := res_1 in
                     bloomfilter_add val hsh bf) (ret (hsh_0, bf_0)) values.

  Lemma eval_dist_bind1 (A B: finType) (f: B -> Comp A) (x: B):
     d[ (x0 <-$ ret x; f x0)] =  d[ f x ].
    Proof.
      by move=> //=; rewrite DistBind1f.
    Qed.


  

  Lemma bloomfilter_add_multiple_unfold A hshs bf x xs (f: _ -> Comp A):
    d[ res <-$ bloomfilter_add_multiple hshs bf (x :: xs);
         f (res) ] =
    d[
        res1 <-$ bloomfilter_add_multiple hshs bf xs;
        let (hshs', bf') := res1 in  
        res2 <-$ bloomfilter_add x hshs' bf';
          f (res2)
     ].
  Proof.
    apply dist_ext => a //=.
    rewrite DistBindA //=.
    by rewrite !DistBind.dE; apply eq_bigr => [[hshs' bf']] _; apply f_equal => //=.
  Qed.
  

Lemma bloomfilter_add_multiple_find_preserve value  inds hashes hashes' bf bf' xs:
  hash_vec_contains_value value hashes inds ->
  ((d[ bloomfilter_add_multiple hashes bf xs]) (hashes', bf') != (0 %R)) ->
        hash_vec_contains_value value hashes' inds.
Proof.

  move=> Hcontains.
  elim: xs hashes inds  Hcontains hashes' bf' => [//=| x xs IHxs] hashes inds Hcontains hashes' bf'.

  - {
      rewrite Dist1.dE xpair_eqE.

      case Hhashes: ((hashes') == _) => /eqP //= /eqP.
      case Hbf: ((bf') == _) => /eqP //= /eqP _.
      by move/eqP: Hhashes -> .
    }
  - {
      rewrite //= DistBind.dE rsum_split //=.

      under big a _ under big b _ rewrite DistBind.dE rsum_Rmul_distr_l rsum_split //=.

      under big a _ under big b _ under big c _ under big d _ rewrite Dist1.dE mulRA mulRC eq_sym xpair_eqE boolR_distr -!mulRA.

      under big a _ under big b _ rewrite exchange_big; under big c _ rewrite -rsum_pred_demote big_pred1_eq.

      move: (IHxs);clear IHxs => IHxs.
      move=>/eqP /prsumr_ge0; case; first by (intros; dispatch_Rgt).
      move=> hashes_internal' /RIneq.Rgt_not_eq/prsumr_ge0; case; first by (intros;dispatch_Rgt).
      move=> bf_prev/RIneq.Rgt_not_eq/prsumr_ge0; case; first by (intros;dispatch_Rgt).
      move=> inds_prev.
      case Heq0: ((d[ bloomfilter_add_multiple hashes bf xs]) (hashes_internal', bf_prev) == (0%R)).
      - by move/eqP:Heq0 ->;rewrite !mul0R mulR0 //= RIneq.INR_IZR_INZ //==>/RIneq.Rgt_not_eq //=.
      - {

          move/Bool.negb_true_iff: Heq0 => //= /IHxs Heq0.          

          move: (Heq0 _ Hcontains); clear Heq0 => Hcontains_internal.

          move=>/RIneq.Rgt_not_eq; rewrite (RIneq.INR_IZR_INZ 0) //= =>/eqP.
          rewrite !mulR_neq0' =>/andP[Hadd /andP [Haddm Hint]].

          case Hneq: (value == x).

          - {
              move: Hcontains_internal Hint.
              move/eqP: Hneq <- =>Hcontains_internal.

              erewrite hash_vec_find_simpl =>//=; last by exact Hcontains_internal.

              move=>/eqP;rewrite RIneq.INR_IZR_INZ; case Hand: (_ && _) => //= _.
              move/andP: Hand => [/eqP ->] //=.
            }

          move/Bool.negb_true_iff: Hneq => Hneq.
          move: Hneq Hcontains_internal Hint; clear.
          move: k inds hashes' hashes_internal' inds_prev;clear k; elim => [|k IHk].

          - {
              do 5!intro; rewrite !tuple0 //= Dist1.dE xpair_eqE => H3.  
              case Htrue: (_ && _); try rewrite RIneq.INR_IZR_INZ => /eqP //= _.
                by move/andP: Htrue => [/eqP -> /eqP _].              
            }
          - {

              move=> [[//=| ind inds] Hinds] [[//=| hash hashes] Hhashes] [[//=| hash' hashes'] Hhashes'].
              move=> [[//=|ind' inds'] Hinds'] Hneq.

              rewrite(tuple_eta (Tuple Hhashes'))(tuple_eta (Tuple Hinds))(tuple_eta (Tuple Hhashes))(tuple_eta (Tuple Hinds')) //=.

              rewrite !ntuple_tailE theadE//=.
              have->: ( thead (Tuple Hhashes)) = hash; first by [].
              have->: ( thead (Tuple Hhashes')) = hash'; first by [].
              have->: ( thead (Tuple Hinds)) = ind; first by [].
              have->: ( thead (Tuple Hinds')) = ind'; first by [].

              rewrite/hash_vec_contains_value //= => /andP[Hfind Hcontains].

              rewrite DistBind.dE rsum_split //=.
              move=> /eqP/prsumr_ge0; case; last move=> b'; first by (intros; dispatch_Rgt).
              move=> /RIneq.Rgt_not_eq/prsumr_ge0; case; last move=> b; first by (intros; dispatch_Rgt).
              move=>/RIneq.Rgt_not_eq/eqP.
              rewrite !mulR_neq0'=>/andP[Hint]/eqP;rewrite DistBind.dE.
              move=>/prsumr_ge0; case; last move=> [] //=; first by (intros; dispatch_Rgt).

              move=> hsh_val ind_val; rewrite Dist1.dE xpair_eqE.

              move=>/RIneq.Rgt_not_eq/eqP; rewrite !mulR_neq0'=>/andP[Hhash].

              rewrite RIneq.INR_IZR_INZ; case Hand: (_ && _) => //=/eqP //= _.

              move:Hint.
              move/andP: Hand =>[/eqP [ H1 H2 ] /eqP [ H3 H4 ]] Hint.
              have Hcont': hash_vec_contains_value value (behead_tuple (Tuple Hhashes')) (FixedList.ntuple_tail (Tuple Hinds)); first by rewrite/hash_vec_contains_value //=.

              move: (IHk (FixedList.ntuple_tail (Tuple Hinds)) b' (behead_tuple (Tuple Hhashes')) b Hneq Hcont' Hint); clear IHk; rewrite/hash_vec_contains_value //= -H2 => ->; rewrite Bool.andb_true_r.

              move:  Hneq Hfind Hhash.
              rewrite H1 /Hash.hash; clear.
              case: (hashstate_find n x hash') => //=.
              - {
                  move=> ind_val' Hneq; rewrite Dist1.dE xpair_eqE=> Hfind'/eqP.
                  case Hand: (_ && _) => //= _.
                  by move/andP: Hand => [/eqP ->] //=.
                }
              - {
                  move=> Hneq Hfind //=; rewrite DistBind.dE=>/eqP.

                  under big a _ rewrite DistBind.dE Dist1.dE xpair_eqE rsum_Rmul_distr_r.

                  under big a _ under big a0 _ rewrite mulRC -mulRA mulRC -mulRA Dist1.dE eq_sym.

                  under big a _ rewrite -rsum_pred_demote big_pred1_eq andbC boolR_distr -!mulRA eq_sym.
                  rewrite -rsum_pred_demote big_pred1_eq //==>/eqP.

                  rewrite mulR_neq0' =>/andP[/eqP ]; case Heq: (_ == _) => //= _ _.
                  move/eqP: Heq ->; move: Hneq Hfind; clear.
                  move=> Hvalue.
                  move: n hash';clear n; elim => [//=|n IHn] [[//=| hash hashes] Hhashes].
                  rewrite (tuple_eta (Tuple Hhashes)) //=.

                  rewrite /FixedList.ntuple_head !theadE  !ntuple_tailE.

                  have->: (thead (Tuple Hhashes)) = hash; first by [].

                  case: hash Hhashes => [[k' v']|] Hhashes //=.

                  case Heq: (k' == value)=>//=.

                  - {
                      move/eqP: Heq ->.
                      move/Bool.negb_true_iff: Hvalue -> => //=.
                        by rewrite ntuple_head_consP eq_refl.                      
                    }

                  - {

                      move=> Hin; move: (Hin).
                      move=>/IHn Heq'.
                      case Hkeq: (k' == x) => //=.
                      - {
                          move/eqP:Hkeq <-; rewrite Heq //=; move: Hin.
                          rewrite/FixedList.ntuple_tail/behead_tuple.
                          move: (behead_tupleP _) => //= H1.
                          move: (behead_tupleP _) => //= H2.
                            by rewrite (proof_irrelevance _ H2 H1) //=.                          
                        }
                      - {
                          by rewrite ntuple_head_consP Heq ntuple_tail_consP.
                        }
                    }

                  - {

                      rewrite eq_sym in Hvalue; move/Bool.negb_true_iff: (Hvalue) -> => //=.
                      rewrite/FixedList.ntuple_tail/behead_tuple.
                      move: (behead_tupleP _) => //= H1.
                      move: (behead_tupleP _) => //= H2.
                      by rewrite (proof_irrelevance _ H2 H1) //=.                          
                    }
                }

            }
        }
    }
    
Qed.            


  



  Lemma bloomfilter_add_multiple_preserve x xs l m hshs hshs' bf bf'
        (Huniq: uniq (x :: xs))
        (Hlen: length xs == l) 
        (Hfree: hashes_have_free_spaces hshs  ((l+m).+1))
        (Huns:      all (bloomfilter_value_unseen hshs) (x :: xs)):
              ((d[ bloomfilter_add_multiple hshs bf xs]) (hshs', bf') != (0 %R)) ->
        (hashes_have_free_spaces hshs' (m.+1)) && (bloomfilter_value_unseen hshs' x).
  Proof.

    (* First clean up the proof *)
    move=> //=.
    rewrite -all_predI /predI //=.

    move: m hshs Hfree Huns bf bf' hshs'; rewrite/hash_vec.
    move/eqP: Hlen <-; clear l.
    have all_cons P y ys : all P (y :: ys) =  P y && all P ys. by [].
    move=> m hshs Hfree; rewrite all_cons => /andP []; move: x m hshs Huniq Hfree; clear all_cons.
    rewrite/hashes_have_free_spaces/hash_has_free_spaces/bloomfilter_value_unseen/hash_unseen.

    (* proof has been cleaned up *)

    elim: xs => [//= | y ys IHy] x m hshs Huniq /allP Hfree /allP Huns Hx  bf bf' hshs'.
        - rewrite Dist1.dE=>/eqP;case Heq: (_ == _)=>//=;move:Heq;rewrite xpair_eqE=>/andP[/eqP->_] _.
          apply /allP=> hsh Hin //=; apply/andP; split.
             by apply Hfree.
             by apply Huns.
        - move: Hx; have all_cons P z zs : all P (z :: zs) =  P z && all P zs. by [].
          rewrite all_cons => /andP [/allP Hfindy /allP Hfindys].

          have H1: uniq (x :: ys).
             by move: Huniq => //=/andP [Hcons /andP [_ ->]]; move: Hcons; rewrite !in_cons Bool.negb_orb=>/andP[_ ->].
          have H2: all (fun hsh : HashState n => FixedList.fixlist_length hsh + (length ys + m.+1).+1 <= n) hshs.
              by apply/allP => vec Hvec; move: (Hfree vec Hvec) => //=; rewrite addSn !addnS.
          have H3: all (fun hsh : HashState n => FixedMap.fixmap_find x hsh == None) hshs.
              by apply /allP.
          have H4: all (fun b : B => all (fun hsh : HashState n => FixedMap.fixmap_find b hsh == None) hshs) ys.    
              by apply/allP.
          move: (IHy x m.+1 hshs H1 H2 H3 H4); clear IHy H1 H2 H3 H4 => IHy.
          move=>/eqP//=; rewrite DistBind.dE prsumr_ge0 => [[[hs1 bf1]]|]; last by move=>a;dispatch_Rgt.
          move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[/eqP/(IHy bf bf1 hs1) ].
          clear IHy all_cons bf Hfree Huns Hkgt0 Hfindys .
          move=>H1 H2; move: H2 H1; rewrite //=DistBind.dE.
          rewrite prsumr_ge0 => [[[hs2 vec1]]|]; last by move=>a;dispatch_Rgt.
          move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ] //=; rewrite Dist1.dE.
          case Heq: (_ == _)=>//=; move: Heq;rewrite xpair_eqE=>/andP[/eqP -> _] Hint _.
          clear hshs'; elim: k hs1 hs2 vec1 Hint; clear hshs Hfindy k.
                 - by move=> hs1 hs2 vec1 //=; rewrite Dist1.dE;case Heq:(_==_)=>//=;move:Heq;rewrite xpair_eqE=>/andP[/eqP ->] //=.          
                 - move=> k IHk hs1 hs2 vec1 //=.  
                   rewrite DistBind.dE prsumr_ge0=>[[[hs3 vec2]]|]; last by move=>a; dispatch_Rgt.
                   move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ].
                   rewrite (tuple_eta hs1) ntuple_tailE //=.
                   move=>/ (IHk _ _ _); clear IHk => IHk.

                   rewrite DistBind.dE prsumr_ge0 => [[[state1 ind1]]|]; last by move=>a;dispatch_Rgt.
                   move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ]//=.
                   rewrite theadE Dist1.dE => Hhash;case Heq:(_==_)=>//=;move:Heq;rewrite xpair_eqE.
                   move=>/andP [/eqP -> /eqP _] _.
                   move=>/andP [/andP [Hlen Hfree]] =>/IHk //= ->; rewrite Bool.andb_true_r.
                   move: Hhash; rewrite/hash/hashstate_find.

                   case: (FixedMap.fixmap_find _ _) => [val //=|]. 

                      - rewrite Dist1.dE //=; case Heq:(_==_)=>//=;move:Heq;rewrite xpair_eqE.
                        move=>/andP [/eqP -> _] _; apply/andP; split => //=.
                           by move:Hlen; rewrite addnS =>/ltnW.
                      - move=> //=;rewrite DistBind.dE prsumr_ge0 => [[ind2]|];last by move=>a;dispatch_Rgt.
                        move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ]//=.
                        rewrite DistBind.dE prsumr_ge0 => [[ind3]|];last by move=>a;dispatch_Rgt.
                        move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ]//= _.
                        rewrite !Dist1.dE;case Heq:(_==_)=>//=;move/eqP:Heq => -> _; clear ind2.
                        case Heq: (_ == _)=>//=;move:Heq;rewrite xpair_eqE=>/andP[/eqP -> /eqP <-] _;clear ind3.
                        apply/andP;split;last first.
                           - rewrite /hashstate_put.
                             move: Huniq => //=/andP[];rewrite in_cons Bool.negb_orb=>/andP[Hneq _ _].
                             by rewrite fixmap_find_neq //=.
                           - move: Hlen.
                             clear.
                             rewrite !addnS -addSn addnC -ltn_subRL => Hlen.
                             rewrite addnC -ltn_subRL.
                             apply (@leq_ltn_trans  (FixedList.fixlist_length (thead hs1)).+1) => //=.
                             clear Hlen; move: (thead _) => [ls Hls]; clear hs1.
                             elim: n ls Hls => [//=|]; clear n => n IHn [//=|l ls] Hls //=.
                             have->: (FixedList.ntuple_head (Tuple Hls)) = l; first by [].
                             case: l Hls => [[k' v']|] Hls; last first; last case Heq: (_ == _).
                               - by move: Hls (eq_ind _ _ _ _ _) => //=.
                               - by move: Hls (eq_ind _ _ _ _ _) => //= Hls Hls'.
                               rewrite /FixedList.ntuple_tail; move: (behead_tupleP _) => //= Hls'.
                               move: (IHn ls Hls') => IHn'.
                               rewrite/FixedList.fixlist_length/FixedList.ntuple_cons.
                               by case Hput: (hashstate_put _) => [ms Hms] //=; move: IHn';rewrite Hput.
  Qed.
  

               



  Lemma bloomfilter_addn_Nuns  ind bf (hashes: hash_vec) x :
    bloomfilter_get_bit ind bf ->
              (d[ res <-$ bloomfilter_add x hashes bf;
                  (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true = (0 %R).
    Proof.

      move=> Htnth //=.

      rewrite DistBind.dE; apply prsumr_eq0P => a _ ; first by dispatch_Rgt.
      move: a => [hashes' bf'].
      rewrite DistBind.dE rsum_Rmul_distr_r; apply prsumr_eq0P => a _; first by dispatch_Rgt.
      move: a => [hashes'' hvec] //=.

      rewrite !Dist1.dE xpair_eqE.

      case Hgth: (_ == _) => //=; rewrite ?mul1R; last by rewrite !mul0R.
      case Hhashes: (_ == _) => //=; rewrite ?Bool.andb_true_l; last by rewrite !mulR0.
      case Hbf: (_ == _) => //=; rewrite ?mulR1; last by rewrite mulR0.

      move/eqP: Hgth.
      move/eqP: Hbf ->.
      rewrite/bloomfilter_get_bit.
      by rewrite bloomfilter_add_internal_preserve //=.

    Qed.
         

        
  Lemma bloomfilter_addn_insert_multiple hashes l (ind: 'I_Hash_size.+1) (bf: BloomFilter) (values: seq B):
       length values == l ->
       hashes_have_free_spaces hashes l ->
       all (bloomfilter_value_unseen hashes) values ->
       uniq values ->
       ~~ bloomfilter_get_bit ind bf ->
       (d[ res <-$ bloomfilter_add_multiple hashes bf values;
           (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true =
       ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k * l)).

    elim: l ind bf values hashes => [|l IHl] ind bf values hashes0 .
      - case: values => //= _ _ _ _ Htnth; rewrite muln0 //= DistBind.dE rsum_split //=.

        transitivity (
            \rsum_(a in [finType of k.-tuple (HashState n)])
             \rsum_(b in [finType of BloomFilter])
             (((a == hashes0) &&  (b == bf) %R) *R* (Dist1.d (~~ bloomfilter_get_bit ind b)) true)
          ).
          by apply eq_bigr => a _; apply eq_bigr => b _; rewrite !Dist1.dE //= xpair_eqE.

        transitivity ((true == (~~ bloomfilter_get_bit ind bf) %R)).   
          rewrite (bigID (fun a => a == hashes0)) //= big_pred1_eq.
          have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.

          apply H.
             - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by dispatch_Rgt.
               apply prsumr_eq0P => b _; first by dispatch_Rgt.
               by rewrite mul0R.

          rewrite (bigID (fun b => b == bf)) //= big_pred1_eq.

          apply H.
            - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by dispatch_Rgt.
              by rewrite Bool.andb_false_r //= mul0R.
          by rewrite !eq_refl //= mul1R Dist1.dE.
        by rewrite Htnth.
      - rewrite mulnS.

        case: values => [//= | x xs] Hlen Hfree Huns Huniq Hnb.
        rewrite bloomfilter_add_multiple_unfold.
        rewrite RealField.Rdef_pow_add.
        erewrite <- (IHl ind bf xs hashes0) => //=.
        rewrite mulRC //= !DistBind.dE rsum_Rmul_distr_r; apply eq_bigr => [[hshs' bf']] _.
        case Hnz: (d[ bloomfilter_add_multiple hashes0 bf xs ] (hshs', bf') == (0 %R));
          first by move/eqP: Hnz ->; rewrite !mul0R mulR0.
        move/Bool.negb_true_iff: Hnz => Hnz.

        move: Hfree; rewrite -(addn0 l) => Hfree.
        move: (bloomfilter_add_multiple_preserve Huniq Hlen Hfree Huns Hnz) => /andP [].
        rewrite /hashes_have_free_spaces/bloomfilter_value_unseen => Hfree' Huns'.
        apply Logic.eq_sym; rewrite mulRA mulRC mulRA mulRC; apply f_equal; apply Logic.eq_sym.
        case Htnth': (~~ bloomfilter_get_bit ind bf').
          - have <-: (Rdefinitions.IZR 1) = (BinNums.Zpos BinNums.xH); first by [].
            erewrite <-  (@bloomfilter_addn hshs' ind bf' x) => //=.
                - by rewrite Dist1.dE //= mul1R !DistBind.dE //=; apply eq_bigr => [[hshs'' bf'']] _.


                - move: Hfree'; rewrite /hashes_not_full/hash_has_free_spaces => /allP Hlt; apply/allP => cell Hcell; rewrite /hash_not_full.
                    by move: (Hlt cell Hcell); rewrite addn1 //=.
          - move /Bool.negb_false_iff: Htnth' => Htnth'; rewrite Dist1.dE // mul0R.
              by rewrite bloomfilter_addn_Nuns //=.


      move/allP: Hfree => Hfree; apply/allP => cell Hcell.        
      move: (Hfree cell Hcell); rewrite /hash_has_free_spaces.
      by rewrite addnS => /ltnW.

      move /allP: Huns => Huns; apply/allP => x' Hx'.
      apply Huns => //=.
      by rewrite in_cons Hx' Bool.orb_true_r.
      by move: Huniq => //= /andP [].
   Qed.
      
  (* TODO: No False Negatives *)

  Lemma bloomfilter_add_internal_indep l bf' x xs :
    tnth (bloomfilter_state bf') x ->
    uniq (x :: xs) ->
    length (x::xs) < Hash_size.+1 ->

    \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
     (((tnth (bloomfilter_state (bloomfilter_add_internal inds bf')) x &&
        all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs) %R) *R*
      (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) =
    ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
     (((tnth (bloomfilter_state (bloomfilter_add_internal inds bf')) x) %R) *R*
      (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) *R*
    (\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
      ((( all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs) %R) *R*
      (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))).
    Proof.
      have H x1 y1 z1: y1 = (0 %R) -> x1 = z1 -> x1 +R+ y1 = z1. by move=> -> ->; rewrite addR0.
      elim: l bf' x xs=> [//=|l IHl] bf' x xs.
           -  move=> Htnth /andP[Hnin Huniq] Hlen; rewrite unlock=>//=.
              have: (index_enum [finType of 0.-tuple 'I_Hash_size.+1]) = [tuple]::[::].
                     rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
                     rewrite -enumT //=; rewrite/(enum _)//=.
                     rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
                     move: (FinTuple.size_enum 0 (ordinal_finType Hash_size.+1))=> //=; rewrite expn0.
                     move: (FinTuple.enum _ _)=>[|[[|//=] Hz] []]//= _.
                     by move: (@tuple0  'I_Hash_size.+1 (Tuple Hz)) <- =>//=.
              move=> -> //=.
              rewrite !addR0.
              by case: (tnth _ _) => //=;rewrite?mul1R?mul0R//=;case: (all _ _)=>//=;rewrite?mul1R.

           - move=> Htnth Huniq Hlength.
             rewrite rsum_tuple_split rsum_split=>//=.

             transitivity (
                 \rsum_(a in 'I_Hash_size.+1)
                  (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                   \rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
                    ((tnth (bloomfilter_state
                              (bloomfilter_add_internal b (bloomfilter_set_bit a bf'))) x &&
                           all [eta tnth (bloomfilter_state
                                            (bloomfilter_add_internal b (bloomfilter_set_bit a bf')))]
                           xs %R) *R*
                     ( (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
               ).
                   apply eq_bigr => a _; rewrite rsum_Rmul_distr_l; apply eq_bigr => b _.
                   rewrite mulRA mulRC mulRA mulRC; apply f_equal.
                     by rewrite mulRC; apply f_equal.

             transitivity (
                 \rsum_(a in 'I_Hash_size.+1)
                  (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
(\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
      ((tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf'))) x %R) *R*
       (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
   \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
      ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
          xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))
                  )
               ).
                  apply eq_bigr=> a _; apply f_equal.
                  rewrite IHl; last first; try by [].


                  case Haeq: (x == a); first by
                      rewrite /bloomfilter_set_bit/bloomfilter_state FixedList.tnth_set_nth_eq //=.
                  by rewrite FixedList.tnth_set_nth_neq //=;  move/Bool.negb_true_iff: Haeq.

              have: (\rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                            ((tnth (bloomfilter_state
                                      (bloomfilter_add_internal inds bf')) x %R) *R*
                             (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                              (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) =
                           \rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                            (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                              (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))
                          ).
                             apply eq_bigr=> inds _.
                             rewrite -{2}(mulR1 (Rdefinitions.Rinv _ *R* _)).
                             rewrite mulRC; apply f_equal.
                             by rewrite bloomfilter_add_internal_preserve //=.
                    move=> ->; rewrite bigsum_card_constE.
                    
                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf'))) x %R) *R*
                             (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
                           \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
                      ).
                    rewrite rsum_Rmul_distr_l.
                    by apply eq_bigr=> a _.

                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                           ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))   *R*
                           \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
                      ).
                           apply f_equal; apply eq_bigr=> a _.
                           rewrite mulRC; apply Logic.eq_sym; rewrite mulRC; apply f_equal; apply Logic.eq_sym.
                           apply eq_bigr=> inds _.
                           rewrite bloomfilter_add_internal_preserve.
                           by rewrite mul1R.

                           rewrite/bloomfilter_state/bloomfilter_set_bit.
                           case Haeq:(x == a); first by rewrite FixedList.tnth_set_nth_eq //=.
                           by move/Bool.negb_true_iff: Haeq=>Haeq; rewrite FixedList.tnth_set_nth_neq//=.


                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                           ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))   *R*
                           \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
                      ).
                           apply f_equal; apply eq_bigr => a _.
                           by rewrite bigsum_card_constE //=.
                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        ((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                           ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))   *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
                      ).
                            rewrite !rsum_Rmul_distr_l; apply eq_bigr=> a _.
                            by rewrite mulRA; apply f_equal.

                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        (((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                           ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))   *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))) 
                      )).
                      by rewrite -mulRA.
                    apply Logic.eq_sym.  

                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        (((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R) *R*
                          (
                           (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) *R*
                         \rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                          ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs %R) *R*
                           (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                            (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
                      ).
                        rewrite -mulRA mulRC -mulRA -mulRA; apply f_equal. 
                        rewrite !rsum_Rmul_distr_l !rsum_Rmul_distr_r mulRC !rsum_Rmul_distr_r.
                        apply eq_bigr=> a _.
                        rewrite mulRC -mulRA -mulRA -mulRA -mulRA; apply f_equal.
                        rewrite mulRC -mulRA mulRC -mulRA  -mulRA; apply f_equal.
                        by rewrite mulRC -mulRA; apply f_equal.
                    apply f_equal.                 
                    transitivity (
                        ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
                        (((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R)) *R*
                         \rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                          ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs %R) *R*
                           (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                            (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
                      ).
                        by rewrite -mulRA mulRC -mulRA; apply f_equal; rewrite mulRC.
                    apply Logic.eq_sym.    

                    transitivity (
                        ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
                        (((#|[finType of l.-tuple 'I_Hash_size.+1]| %R)) *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))) 
                      )).
                        by rewrite -mulRA mulRC -mulRA; apply f_equal; rewrite mulRC.
                    apply f_equal; apply Logic.eq_sym.    
                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        (((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R)) *R*
                         \rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                          ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs %R) *R*
                           ( (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
                      ).
                        apply Logic.eq_sym; rewrite mulRA mulRC mulRA mulRC; apply f_equal.
                        rewrite rsum_Rmul_distr_r; apply eq_bigr=> inds _.
                        by rewrite mulRC -mulRA; apply f_equal; rewrite mulRC.
                    rewrite rsum_tuple_split rsum_split !rsum_Rmul_distr_l; apply eq_bigr=> a _.
                    rewrite !rsum_Rmul_distr_l; apply eq_bigr=> inds _ //=.
                    transitivity ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))] xs %R) *R*
                        (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                                  ((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R) *R*
                                   ( (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))).
                        rewrite mulRC -mulRA mulRC -mulRA -mulRA; apply f_equal.
                        by rewrite mulRC -mulRA; apply f_equal; rewrite mulRC.
                    apply Logic.eq_sym.    

                    transitivity (
                        (all [eta tnth (bloomfilter_state
                                          (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))] xs
                               %R) *R* 
                        ((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                         ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))                 
                      ).
                       by rewrite mulRC -mulRA; apply f_equal; rewrite mulRC //=.
                    apply f_equal.
                    rewrite !card_tuple //=.
                    rewrite expnSr card_ord natRM; apply Logic.eq_sym.

                    transitivity (
                        ((Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Hash_size.+1 %R)) *R*
                         (((Hash_size.+1 ^ l %R)) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))                           ).
                          by rewrite -mulRA -mulRA; apply f_equal; rewrite mulRC -mulRA;
                             apply f_equal; rewrite mulRC.
                          rewrite Raxioms.Rinv_l; first by rewrite mul1R.
                            by apply RIneq.not_0_INR =>//=.
    Qed.
    
Lemma bloomfilter_add_insert_contains l (bf: BloomFilter) (inds: l.-tuple 'I_Hash_size.+1 ) (ps: seq 'I_Hash_size.+1) : all (fun p => p \in inds) ps -> all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf)) ps.
Proof.                  
  move=>/allP HinP; apply/allP => [p Hp].
  by rewrite /bloomfilter_get_bit/bloomfilter_state bloomfilter_add_internal_hit //=; move: (HinP p Hp).
Qed.

Lemma pr_in_vec (A : finType) (ps : seq A) :
   #|A| > 0 ->
       uniq ps ->
       \rsum_(ind in A) (Rdefinitions.Rinv (#|A| %R) *R* ((ind \notin ps) %R))
       = (1 -R- (Rdefinitions.Rinv (#|A| %R) *R* (length ps %R))).
  have: (\rsum_(ind in A) (Rdefinitions.Rinv (#|A| %R) *R* ((ind \notin ps) %R))) = ( \rsum_(ind in A) (((ind \notin ps) %R)  *R* Rdefinitions.Rinv (#|A| %R) )
                                                                                    ); last move=> ->; first by apply eq_bigr=> ind _; rewrite mulRC.
  rewrite -rsum_pred_demote.
  rewrite bigsum_card_constE.

  move=> HA; rewrite -(mulVR (#|A| %R)); last by apply /eqP; apply RIneq.not_0_INR =>//=; apply/eqP; apply/lt0n_neq0.
  rewrite -RIneq.Rmult_minus_distr_l mulRC=>Huniq;apply f_equal.

  rewrite -(cardC (fun i => i \in ps)) //=.
  rewrite/predC //=.


  have: (@card A
               (@mem (Finite.sort A) (predPredType (Finite.sort A))
                     (fun i : Finite.sort A =>
                        @in_mem (Finite.sort A) i (@mem (Finite.sort A) (seq_predType (Finite.eqType A)) ps)))) = (#|{: seq_sub ps}|); last move=> ->; first by rewrite card_seq_sub //=; apply /card_uniqP.
  rewrite card_seq_sub //= length_sizeP.
  rewrite natRD.
    by rewrite addRC -subRBA subRR subR0.

Qed.


Lemma rsum_bijective_eqC {A: finType} (c: Rdefinitions.R) (P Q : pred A) (p:  A -> A) :
   bijective p ->
  (forall a, P (p a) = Q a) ->
  \rsum_(a in A | P a) c = \rsum_(a in A | Q a) c.
Proof.
  move=> Hbij Himpl.
  rewrite (@reindex _ _ _ _ _ p) //=.
  by transitivity ( \rsum_(j | Q j) c); first by apply eq_bigl => a'; rewrite Himpl.
  by apply onW_bij.
Qed.

(* Swaps all elements of a given vector by all elements of another*)

Fixpoint swap_vec {A: finType} (m:nat) (ps qs: seq A) (list: m.-tuple A) : m.-tuple A :=
  match m as m' return (m = m' -> m'.-tuple A -> m'.-tuple A) with
      | 0 => (fun (Hm: m = 0) (list: 0.-tuple A) => list)
      | m'.+1 => (fun (Hm: m = m'.+1) (list: (m'.+1).-tuple A) =>
                    let head := thead list in
                    let tail := behead_tuple list in
                    let new_head := (if (head \in ps) && (head \in qs) then
                                       head
                                     else if (head \in ps) then
                                            nth
                                              head
                                              (filter (fun p => p \notin qs) ps)
                                              (index head (filter (fun q => q \notin ps) qs))  
                                     else if (head \in qs) then
                                            nth
                                              head
                                              (filter (fun q => q \notin ps) qs)
                                              (index head (filter (fun p => p \notin qs) ps))
                                     else head) in
                    [tuple of new_head :: (swap_vec  ps qs tail)] )
    end (erefl m) list.


Lemma nth_filter (B: eqType) (f:B) (fs ys: seq B) ind: ind < length (filter (fun f => f \notin ys) fs) -> nth f (filter (fun f => f \notin ys) fs) ind \in ys = false.
Proof.  {
    elim: fs ind => [//=| r rs IHrs //=] ind.
    case Hinr: (r \in ys) => //=; first  by move=> /IHrs.
    case: ind => [|ind] /ltn_SnnP Hlen; first by [].
      by move=>//=; apply IHrs.
  }
Qed.
Lemma nth_mem_filter (B: eqType) (f:B) (fs: seq B) P ind: ind < length (filter P fs) -> nth f (filter P fs) ind \in fs. 
Proof.  {
        elim: fs ind => [//= | r rs IHrs] ind //=; case: (P r) => //=.
        case: ind => [//= _ | ind ]; rewrite ?in_cons ?eq_refl ?Bool.orb_true_l  //=.
        by move=>/ltn_SnnP/IHrs ->; rewrite Bool.orb_true_r.
        by rewrite in_cons =>/IHrs ->; rewrite Bool.orb_true_r.
  }
Qed.

Lemma mem_len (B: eqType) (f:B) (fs: seq B): f \notin fs -> index f fs = length fs. 
Proof.  {

    elim: fs f => [//=| r rs IHrs] f.
    rewrite in_cons Bool.negb_orb =>/andP [Hfnr /IHrs Hind]//=.
    by rewrite eq_sym; move/Bool.negb_true_iff: Hfnr ->; rewrite Hind.
  }
Qed.

Lemma filter_leq_size (B: eqType) (fs: seq B) P: length (filter P fs) <= length fs. 
Proof.  {
    elim: fs => [//=| f fs IHf] //=.
    case: (P f) => //=; by apply ltnW.
  }
Qed.

Lemma filter_size (B: eqType) (fs: seq B) P: length (filter P fs) = length fs - (length (filter (fun f => ~~ P f) fs)). 
Proof.  {

    elim: fs P => [//=| f  fs IHf] P //=.
    case: (P f) => //=.
    rewrite subSn; first rewrite IHf //=; last by apply filter_leq_size.
    by rewrite subSS IHf.
                                                                                                                     }
Qed.

Lemma uniq_filter (B: eqType) (fs: seq B) P: uniq  fs -> uniq (filter P fs). 
Proof.  {
    elim: fs => [//= | f fs IHf] //= /andP [ Hnin Huniq].
    case Hpf: (P f) => //=; last by apply IHf.
    rewrite IHf //= Bool.andb_true_r.
    by rewrite mem_filter Bool.negb_andb; apply/orP; right.
  }
Qed.

Lemma len_eq (B: eqType) (fs gs: seq B): uniq fs -> uniq gs -> length fs = length gs -> length (filter (fun f =>  f \notin gs) fs) = length (filter (fun g => g \notin fs) gs).
Proof.  {

    move=>Huniqfs Huniqgs Heqsize.
    rewrite filter_size [length (filter _ gs)]filter_size Heqsize; apply f_equal.
    transitivity  (length (filter (fun f => f \in gs) fs)).
      by do ?apply f_equal; apply eq_in_filter => fs' Hin //=; rewrite Bool.negb_involutive.
    apply Logic.eq_sym; transitivity (length (filter (fun g => g \in fs) gs)).
      by do ?apply f_equal; apply eq_in_filter => fs' Hin //=; rewrite Bool.negb_involutive.       
    rewrite -!length_sizeP.
    apply perm_eq_size; rewrite/perm_eq.
    apply uniq_perm_eq; try by apply uniq_filter.
    by move=> g; rewrite !mem_filter andbC //=.
 }
Qed.



  

Lemma substitute_vec_inv (A: finType) (m: nat) (ps qs: seq A) :
  uniq ps -> uniq qs -> length ps = length qs -> 
  forall x : m.-tuple A, 
    swap_vec  qs ps (swap_vec ps qs x) = x.
Proof.
  move=> Hinjp  Hinjq. rewrite -!length_sizeP=> Hlength.

  elim: m => [//= | m IHm x] .
  rewrite (tuple_eta x) //=.
  rewrite !theadE !beheadE !IHm.



  case Hinp: (thead x \in ps); case Hinq: (thead x \in qs) => //=.
     - by rewrite Hinp Hinq //=.
     - rewrite mem_len.
       rewrite nth_default.
       rewrite Hinq //= Hinp mem_len.
       rewrite nth_default //=.
       by rewrite length_sizeP len_eq.
       by rewrite mem_filter Bool.negb_andb Hinp //=.
       by rewrite length_sizeP len_eq.
       by rewrite mem_filter Bool.negb_andb Hinp //=.

     - rewrite mem_len.
       rewrite nth_default.
       rewrite Hinp Hinq //=.
       rewrite mem_len.
       rewrite nth_default //=.
       by rewrite length_sizeP len_eq.
       by rewrite mem_filter Bool.negb_andb Hinp Bool.orb_true_r //=.
       by rewrite length_sizeP len_eq.       
       by rewrite mem_filter Bool.negb_andb Hinp Bool.orb_true_r //=.

     - rewrite Hinp Hinq //=.
Qed.

Lemma swap_vec_bij (A: finType) (m: nat) (ps qs: seq A) :
  uniq ps -> uniq qs -> length ps = length qs -> 
  bijective (@swap_vec _ m ps qs).
Proof.
  move=> Huniqps Huniqqs Hleneq.
  split with (swap_vec qs ps); move=>x; by rewrite substitute_vec_inv.
Qed.  


  Lemma bloomfilter_addn_insert_multiple_inv hashes l (ind: 'I_Hash_size.+1) (bf: BloomFilter) (values: seq B):
       length values == l ->
       hashes_have_free_spaces hashes l ->
       all (bloomfilter_value_unseen hashes) values ->
       uniq values ->
       ~~ bloomfilter_get_bit ind bf ->
       (d[ res <-$ bloomfilter_add_multiple hashes bf values;
           (let '(_, bf') := res in ret bloomfilter_get_bit ind bf')]) true =
       (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k * l))).
    Proof.

      move=> Hlen Hhashes Huns Huniq Hnth.

      transitivity (
          (d[ res <-$ bloomfilter_add_multiple hashes bf values;
              ret (fun res' => (let '(_, bf') := res' in bloomfilter_get_bit ind bf')) res]) true
        ).
           - by rewrite //= !DistBind.dE; apply/eq_bigr=>[[hs' bf']] _ //=.
      rewrite -(prsumr_neg1 ).

      transitivity (
          (1 -R- (d[ res <-$ bloomfilter_add_multiple hashes bf values;
                     (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true)
        ).
          - by rewrite //= !DistBind.dE; apply f_equal; apply/eq_bigr=>[[hs' bf']] _ //=.
      by rewrite (@bloomfilter_addn_insert_multiple _ l).       
    Qed.





Notation "a \subseteq b" := (all (fun a' => a' \in b) a) (at level 70).



Lemma rem_in_neq (A: eqType) (q p: A) (inds: seq A) (Hneq:   q != p):

  (q \in rem p inds) = (q \in inds).
Proof.
  elim: inds => //= ind inds IHind.
  move: Hneq.
  case Heqind: (ind == p).
  - by move/eqP: Heqind ->;   rewrite in_cons eq_sym =>/Bool.negb_true_iff -> //=.
  - by rewrite !in_cons IHind.
Qed.

Lemma subseteq_in_rem (A: eqType) (p : A) (ps: seq A) inds:
  p \notin ps ->
  (p \in inds) ->
  (ps \subseteq (rem p inds)) = (ps \subseteq inds).
Proof.
  move=> Hnin IHind.
  elim: ps Hnin  => //= q qs IHps.
  rewrite //= in_cons Bool.negb_orb =>/andP[Hneq Hnin].
  move: (IHps Hnin) => ->.
  rewrite andbC [(q \in inds) && _]andbC; apply f_equal.
  clear IHps Hnin qs IHind.
  by apply rem_in_neq; rewrite eq_sym.
Qed.



    
  Theorem bloomfilter_addn_bits
       hashes b (inds: seq 'I_Hash_size.+1) (bf: BloomFilter) (value: B):
       b < k ->
       length inds == b ->
       hashes_have_free_spaces hashes 1 ->
       (bloomfilter_value_unseen hashes value)  ->
       uniq inds ->
       all (fun ind => ~~ bloomfilter_get_bit ind bf) inds ->
       (d[ res <-$ bloomfilter_add value hashes bf;
             (let '(_, bf') := res in ret (all (bloomfilter_get_bit^~ bf') inds))]) true = 
\rsum_(i in tuple_finType k (ordinal_finType Hash_size.+1))
     ((((inds \subseteq i) == true) %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k)).    Proof.
      have H x1 y1 z1: y1 = (0 %R) -> x1 = z1 -> x1 +R+ y1 = z1; first by move=> -> ->; rewrite addR0.
      rewrite //= DistBind.dE => Hb Hlen Hfree Huns Huniq Hall.
      under big a _ rewrite DistBind.dE //= !rsum_Rmul_distr_r //=.
      under big a _ rewrite  !rsum_Rmul_distr_r //=.
      rewrite rsum_split //=.
      under big a _ under big b0 _  rewrite Dist1.dE eq_sym.
      under big a _  rewrite exchange_big.
      rewrite exchange_big rsum_split//=.
      under big a _ under big b0 _ under big i _ under big i0 _ rewrite Dist1.dE xpair_eqE.
      under big a _ under big b0 _ rewrite (bigID (fun i => i == a)) big_pred1_eq //=.
      under big a _ rewrite addRA_rsum.
      rewrite addRA_rsum.
      erewrite H; last by []; last first.
      {
        do 2!(apply prsumr_eq0P; intros; first by intros; dispatch_Rgt).
        apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by intros; dispatch_Rgt.
        apply prsumr_eq0P; intros; first by intros; dispatch_Rgt.
        by rewrite //= !mulR0.
      }

      under big i _ under big i0 _ rewrite (bigID (fun j => j == (bloomfilter_add_internal i0 bf))) big_pred1_eq //=.
      under big i _ rewrite addRA_rsum //=.
      rewrite addRA_rsum.
      erewrite H; last by []; last first.
      {
        do 2!(apply prsumr_eq0P; intros; first by intros; dispatch_Rgt).
        apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by intros; dispatch_Rgt.
        by rewrite Bool.andb_false_r //= !mulR0.
      }
      under big i _ under big i0 _ rewrite !eq_refl //= mulR1.
      under big i _ under big i0 _ rewrite mulR1.
      rewrite exchange_big //=.

      under big i0 _ rewrite (bigID (fun i => i == Tuple (hash_vec_insert_length value hashes i0))) big_pred1_eq //=.
      rewrite addRA_rsum.
      erewrite H; last by []; last first.
      {
        do 1!(apply prsumr_eq0P; intros; first by intros; dispatch_Rgt).
        apply prsumr_eq0P => i Hneq; first by intros; dispatch_Rgt.
        by rewrite neg_hash_vecP //=; first rewrite !mulR0.
      }
      under big i _ rewrite hash_vecP //=.

      have Hpred_eq i: (all (bloomfilter_get_bit^~ (bloomfilter_add_internal i bf)) inds = all (fun ind => ind \in i) inds).
      {
        apply eq_in_all => ind Hinds.
        case HinI: (ind \in i); first by rewrite /bloomfilter_get_bit bloomfilter_add_internal_hit //=.

        apply/Bool.negb_true_iff; rewrite /bloomfilter_get_bit bloomfilter_add_internal_miss //=;
                                          first by move/allP: Hall => /(_ ind Hinds) .
          by rewrite HinI.
      }


      under big i _ rewrite Hpred_eq //=.

      by [].
Qed.

Lemma all_in_negP (A: eqType) (I J : seq A) :
    all (fun j => j \notin I) J = all (fun i => i \notin J) I.
Proof.
  apply/allP.

  case Hall: all;
  first by move/allP: Hall => Hnin;  move=> j Hj; apply/memPn => i Hi;
  move: (Hnin i Hi) =>/memPn/(_ j Hj); rewrite eq_sym.

  by move/Bool.negb_true_iff: Hall => /allPn [i Hi];
  rewrite Bool.negb_involutive => Hiinj;
   apply/allP;apply/allPn; exists i => //=; rewrite Bool.negb_involutive.
Qed.

Lemma rsum_subseq_internal (m : nat) (I J: seq 'I_m) : m > 0 ->
  uniq I -> 
  all (fun j => j \notin I) J ->
  \rsum_(i in 'I_m | i \notin J) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R)) =
 (((length I %R) *R* Rdefinitions.Rinv (m %R))).
Proof.
  move=> Hm; elim: I J => [|i I IHI] J Huniq Hall; first
  by rewrite //= ?mul0R bigsum_card_constE ?mulR0.
  under big i0 _ rewrite in_cons.
  rewrite rsum_pred_demote (bigID (fun i0 => i0 == i)) big_pred1_eq //= eq_refl //= mul1R.
  move: (Hall); rewrite all_in_negP => //=/andP[-> Hall'] //=; rewrite mul1R.
  rewrite -addn1 natRD RIneq.Rmult_plus_distr_r mul1R [(_ *R* _) +R+ _]addRC; apply f_equal.

  transitivity (\rsum_(i0 < m | i0 \notin (i :: J)) ((((i0 \in I) %R) *R* Rdefinitions.Rinv (m %R)))).
  - {
      rewrite rsum_pred_demote [ \rsum_(i0 < _ | _) _]rsum_pred_demote; apply eq_bigr => i0 _ //=.
        by rewrite in_cons Bool.negb_orb; case: (_ == _); case: (_ \in _) => //=;
                                                                              rewrite ?mulR0 ?mul0R ?mul1R ?mulR1//=.      
    }
    apply IHI => //=.
    - by move: Huniq => //=/andP[].
    - apply/andP; split.
    - by move: Huniq => //=/andP [].  

    - move/allP: Hall => Hall; apply/allP => j Hj.   
      by move: (Hall j Hj); rewrite in_cons Bool.negb_orb =>/andP[].
Qed.


Lemma rsum_subseq (m : nat) (I : seq 'I_m) : m > 0 ->
  uniq I -> 
  \rsum_(i in 'I_m) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R)) =
 (((length I %R) *R* Rdefinitions.Rinv (m %R))).
Proof.
  move=> Hm Huniq.
  transitivity ( \rsum_(i in 'I_m | i \notin [::]) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R))); first
  by apply eq_bigl => i //=.
  by apply rsum_subseq_internal => //=.
Qed.


  
Lemma rsum_subseq_mult (m b: nat) (I: seq 'I_m):
  0 < m ->
    uniq I ->
    \rsum_(ps in [finType of b.-tuple 'I_m] | ps \subseteq I)
     ((Rdefinitions.Rinv (m %R)) ^R^ b) = (((length I %R) *R* Rdefinitions.Rinv (m %R)) ^R^ b).
Proof.           
  elim: b I => [//=| b IHb I] Hm Huniq.
  - by rewrite rsum_pred_demote rsum_empty //= mul1R.
  - {

      rewrite rsum_pred_demote rsum_tuple_split rsum_split //=.
      have Hbool A B: (A && B %R) = ((A %R) *R* (B %R));
        first by case: A; case: B; rewrite ?mulR0 ?mul0R ?mulR1 ?mul1R.

      have Hsusp a b0: (((a \in I) && (b0 \subseteq I) %R) *R*
                        ((Rdefinitions.Rinv (m %R) *R*
                          (Rdefinitions.Rinv (m %R) ^R^ b)))) =
                       (((a \in I %R) *R*  Rdefinitions.Rinv (m %R)) *R*
                         (((b0 \subseteq I) %R) *R*
                        (((Rdefinitions.Rinv (m %R) ^R^ b)))));
      first by rewrite -mulRA Hbool -mulRA;apply f_equal;
        rewrite mulRC -mulRA; apply f_equal;
          rewrite mulRC; apply f_equal.
      under big a _ under big b0 _  rewrite Hsusp.
      by rewrite -big_distrlr //= -!rsum_pred_demote IHb 1?rsum_pred_demote 1?rsum_subseq //=.

      }
Qed.

Lemma rsum_subseq_undup_eq (m : nat) (I : seq 'I_m) : 
  \rsum_(i in 'I_m) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R)) =
 \rsum_(i in 'I_m) (((i \in undup I) %R) *R* Rdefinitions.Rinv (m %R)).
Proof.
  by under big i _ rewrite mem_undup.
Qed.

Lemma rsum_subseq_mult_undup_eq (m b: nat) (I: seq 'I_m):
    \rsum_(ps in [finType of b.-tuple 'I_m] | ps \subseteq I)
     ((Rdefinitions.Rinv (m %R)) ^R^ b) = 
    \rsum_(ps in [finType of b.-tuple 'I_m] | ps \subseteq undup I)
     ((Rdefinitions.Rinv (m %R)) ^R^ b).
Proof.

  elim: b => [//=| b IHb ]; first by rewrite rsum_pred_demote rsum_empty rsum_pred_demote rsum_empty //= mul1R.

  rewrite rsum_pred_demote rsum_tuple_split rsum_split //=.
  
  have Hbool A B: (A && B %R) = ((A %R) *R* (B %R));
        first by case: A; case: B; rewrite ?mulR0 ?mul0R ?mulR1 ?mul1R.

  have Hsusp a b0 :
    (((a \in I) && (b0 \subseteq I) %R) *R* (Rdefinitions.Rinv (m %R) *R* (Rdefinitions.Rinv (m %R) ^R^ b))) =
    ((((a \in I) %R) *R* Rdefinitions.Rinv (m %R)) *R* ((b0 \subseteq I %R) *R* (Rdefinitions.Rinv (m %R) ^R^ b)));
  first by rewrite Hbool -mulRA -mulRA; apply f_equal;  rewrite mulRC -mulRA; apply f_equal; rewrite mulRC.

  under big a _ under big b0 _ rewrite Hsusp.

  rewrite -big_distrlr //= -!rsum_pred_demote IHb 2!rsum_pred_demote big_distrl.
  apply Logic.eq_sym; rewrite rsum_pred_demote rsum_tuple_split rsum_split //=.
  apply eq_bigr=> a _;  rewrite rsum_Rmul_distr_l; apply eq_bigr=> b0 _.
  by rewrite mem_undup Hbool -mulRA -mulRA; apply f_equal;
  rewrite mulRC -mulRA; apply f_equal; rewrite mulRC.
Qed.

Definition bloomfilter_new : BloomFilter.
  apply mkBloomFilter.
  apply Tuple with (nseq Hash_size.+1 false).
  by rewrite size_nseq.
Defined.

Lemma bloomfilter_new_empty_bits b : ~~ bloomfilter_get_bit b bloomfilter_new .
Proof.
clear k n Hkgt0.
rewrite/bloomfilter_get_bit/bloomfilter_new //=.
elim: Hash_size b => [[[|//=] Hm]|//= n IHn] //=.
move=> [[| b] Hb]; rewrite /tnth //=.
move: (Hb); move/ltn_SnnP: Hb => Hb' Hb;move: (IHn (Ordinal Hb'));rewrite /tnth //=.
clear.

move: (size_nseq n.+1 _)  => Hprf.
move:(tnth_default _ _) (tnth_default _ _); clear Hb => b1 b2.

have ->: (false :: nseq n false) = (nseq n.+1 false); first by [].
move: Hb'; rewrite -Hprf; clear Hprf.
move: (n.+1); clear n; elim: b => [//= n'|]; first by case: (nseq n' _).
move=>  b IHb.
case => [//=| n].
by move=>//=/ltn_SnnP/(IHb n) IHb' H; apply IHb'.
Qed.

Lemma bloomfilter_new_empty bs : length bs > 0 -> ~~ bloomfilter_query_internal bs bloomfilter_new .
Proof.
clear k n Hkgt0.
case: bs => [//=| b1 [//=| b2 bs]] Hlen; first by rewrite Bool.andb_true_r; apply bloomfilter_new_empty_bits.
rewrite Bool.negb_andb; apply/orP; left; apply bloomfilter_new_empty_bits.
Qed.

Lemma minn_mult m l: (minn m (l * m + m) = m). Proof. by rewrite minnE //= addnC subnDA subnn subn0. Qed.
Lemma mult_subn m l: ((m * l) + l - l) = (m * l). Proof. by rewrite -addnBA //= subnn addn0. Qed.

Definition tuple_split (A:finType) (m l: nat) (xs: (m * l + l).-tuple A) : (l.-tuple A * (m * l).-tuple A).
  split.
  move: (take_tuple l xs); rewrite minn_mult=>V; exact V. 
  move: (drop_tuple l xs); rewrite mult_subn=>V; exact V.
Defined.

Definition tuple_split_mult (A:finType) (m l: nat) (xs: (m.+1 * l).-tuple A) : (l.-tuple A * (m * l).-tuple A).
  have H: (m.+1 * l = m * l + l); first by rewrite mulSnr.
  rewrite H in xs.
  exact (tuple_split xs).
Defined.

Lemma tcast_tval_eq (A: finType) (n' m : nat) (Hm: m = n') (v: m.-tuple A) (w: seq A) :
  w = tval v ->
  tval (tcast Hm v) = w.
Proof.
  move=> -> //=.
  rewrite <-Hm.
  by rewrite tcast_id.
Qed.

Lemma tuple_split_valid (A: finType) (m l:nat) :  bijective (fun (x: [finType of (m.-tuple A * (l * m).-tuple A)]) => let (b,a) := x in cat_tuple b a).

  split with (fun (xs : (m + l * m).-tuple A) =>  @tuple_split A l m (tcast (addnC m (l * m)) xs)) => [[p ps]| x].
  apply/eqP; rewrite xpair_eqE; apply/andP; split=>//=; apply/eqP.

  - {
      rewrite/take_tuple; move: (take_tupleP  _ _); rewrite/cat_tuple.
      erewrite (@tcast_tval_eq A (l * m + m) (m + l * m) (addnC m (muln l m))
                               (Tuple (cat_tupleP p ps)) (cat p ps)).
      rewrite take_cat //= size_tuple ltnn subnn take0 cats0 //=.
      move: (minn_mult _ _) => //=; rewrite minn_mult /eq_rect_r //= => Hm'.
      move: Hm' (Logic.eq_sym _ ) => _ H1.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat m (fun y :nat => y.-tuple A -> m.-tuple A) id H1) //=.
      case: p => //= p' H4 H5; rewrite (proof_irrelevance _ H4 H5) //=.
        by move=>//=.      
    }
  - {

      rewrite /drop_tuple; move: (drop_tupleP _ _); rewrite/cat_tuple.
      erewrite (@tcast_tval_eq A (l * m + m) (m + l * m) (addnC m (muln l m))
                               (Tuple (cat_tupleP p ps)) (cat p ps)).

      rewrite drop_cat //= size_tuple ltnn subnn drop0 //=.
      move: (mult_subn _ _) => //=; rewrite mult_subn /eq_rect_r //= => Hm'.
      move: Hm' (Logic.eq_sym _ ) => _ H1.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat (l * m) (fun y :nat => y.-tuple A -> (l*m).-tuple A) id H1) //=.
      case: ps => //= p' H4 H5; rewrite (proof_irrelevance _ H4 H5) //=.
        by move=>//=.      
    }
  - {
      move=> //=; rewrite /take_tuple/drop_tuple //=.
      rewrite/cat_tuple //=;      move: (cat_tupleP _ _).
      move: (take_tupleP _ _) (drop_tupleP _ _) => //=.
      move: (minn_mult _ _) (mult_subn _ _) => //=.
      rewrite minn_mult mult_subn //= => H1 H2.
      rewrite /eq_rect_r.

      move: (Logic.eq_sym H1) => //=;clear H1=> H1.
      move: (Logic.eq_sym H2) => //=;clear H2=> H2.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat m (fun y :nat => y.-tuple A -> m.-tuple A) id H1) //=.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat (l * m) (fun y :nat => y.-tuple A -> (l * m).-tuple A) id H2) //=.
      rewrite cat_take_drop.

      move=> _ _; move: x  (addnC _ _) . 
      rewrite addnC => x Heq; rewrite tcast_id; case: x => //= x H3 H4 .
      by rewrite (proof_irrelevance _ H3 H4).
    }
Qed.





Lemma subseq_imd (A: finType) (m l: nat) (f: (m.+1 * l).-tuple A -> Rdefinitions.R):
      \rsum_(bs in [finType of (m.+1 * l).-tuple A]) (f bs *R* (Rdefinitions.Rinv (#|A| %R) ^R^ (m.+1 * l))) = 
      \rsum_(b in [finType of l.-tuple A])
       ( (Rdefinitions.Rinv (#|A| %R) ^R^ l)      *R*
      \rsum_(bs in [finType of (m * l).-tuple A]) (f (cat_tuple b bs) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ (m * l)))
      ).
Proof.
under big b _ rewrite rsum_Rmul_distr_l.
  apply Logic.eq_sym.
  have Hoqv Q p q (vec : seq Q): (size vec == p.+1 * q) = (size vec == q + p * q); first by rewrite mulSnr addnC.

  have H: (m * l + l) = (m.+1 * l); first by rewrite mulSnr.
  transitivity (\rsum_(x in [finType of (l.-tuple A * (m * l).-tuple A)%type])
        (let (b,a) := x in ((Rdefinitions.Rinv (#|A| %R) ^R^ l) *R*
                            (f ((cat_tuple b a)) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ m * l)))) ).
  by rewrite rsum_split //=; do ? (apply eq_bigr; intros); do ?apply f_equal => //=.

  rewrite (@reindex Rdefinitions.R Rdefinitions.R0 _ ([finType of (l.-tuple A * (m * l).-tuple A)]) _ (@tuple_split A m l)) => //=.
  rewrite rsum_pred_demote //=; under big a _ rewrite mul1R.


  rewrite (big_tcast H) => //=; apply eq_bigr=> a Ha.


  rewrite  mulRA mulRC mulRA.

  have ->: (((Rdefinitions.Rinv (#|A| %R) ^R^ m * l) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ l))) =
        ((Rdefinitions.Rinv (#|A| %R) ^R^ m.+1 * l)); first by rewrite -H Rfunctions.pow_add.
  rewrite [f a *R* _]mulRC; apply f_equal.

      move=> //=; rewrite /take_tuple/drop_tuple //=.
      rewrite/cat_tuple //=;      move: (cat_tupleP _ _).
      move: (take_tupleP _ _) (drop_tupleP _ _) => //=.
      move: (esym H); clear H => H.
      clear Ha; case: a => a Ha.
      erewrite (@tcast_tval_eq A _ _ _ _ a).
      move: (minn_mult _ _) (mult_subn _ _) Ha => //=.
      rewrite minn_mult mult_subn //= => H1 H2; rewrite /eq_rect_r.
      move: (Logic.eq_sym H1) => //=;clear H1=> H1.
      move: (Logic.eq_sym H2) => //=;clear H2=> H2.
      move: (esym H); clear H => H.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat l (fun y :nat => y.-tuple A -> l.-tuple A) id H1) //=.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat (m * l) (fun y :nat => y.-tuple A -> (m * l).-tuple A) id H2) //=.

      move=> Hprf.
      rewrite cat_take_drop => _ _.
      rewrite addnC in H.
      clear -Hoqv; move: a Hprf.
      have: (l + m * l) = (m.+1 * l); first by rewrite mulSnr addnC.
      move=> H //=; move: f => //= f a H1 H2; apply f_equal; apply f_equal; move: H1 H2. 
      rewrite -(Hoqv A m l a) => H1 H2.
      by rewrite (proof_irrelevance _ H1 H2).
      by move=>//=.



      exists ((fun x : [finType of l.-tuple A * (m * l).-tuple A] => let (b, a) := x in tcast (addnC l (m*l)) (cat_tuple b a))).


      - {
          move=> vec _ //=.
          apply Logic.eq_sym.
          eapply eq_tcast.
          move=> //=; rewrite /take_tuple/drop_tuple //=.
          move: (take_tupleP _ _) (drop_tupleP _ _) => //=.
          move: (minn_mult _ _) (mult_subn _ _) => //=.
          rewrite minn_mult mult_subn //= => H1 H2.
          rewrite /eq_rect_r.

          move: (Logic.eq_sym H1) => //=;clear H1=> H1.
          move: (Logic.eq_sym H2) => //=;clear H2=> H2.
          rewrite -(@Eq_rect_eq.eq_rect_eq nat l (fun y :nat => y.-tuple A -> l.-tuple A) id H1) //=.
          rewrite -(@Eq_rect_eq.eq_rect_eq nat (m * l) (fun y :nat => y.-tuple A -> (m * l).-tuple A) id H2) //=.
          by rewrite cat_take_drop.
        }


      - {


          move => [p ps] _.
          apply/eqP; rewrite xpair_eqE; apply/andP; split=>//=; apply/eqP.

          - {
              rewrite/take_tuple; move: (take_tupleP  _ _); rewrite/cat_tuple.

              erewrite (@tcast_tval_eq A (m * l + l) (l + m * l) (addnC l (m * l)) (Tuple (cat_tupleP p ps)) (cat p ps)) => //=.
              rewrite take_cat //= size_tuple ltnn subnn take0 cats0 //=.
              move: (minn_mult _ _) => //=; rewrite minn_mult /eq_rect_r //= => Hm'.
              move: Hm' (Logic.eq_sym _ ) => _ H1.
              rewrite -(@Eq_rect_eq.eq_rect_eq nat l (fun y :nat => y.-tuple A -> l.-tuple A) id H1) //=.
              case: p => //= p' H4 H5; rewrite (proof_irrelevance _ H4 H5) //=.
            }
          - {

              rewrite /drop_tuple; move: (drop_tupleP _ _); rewrite/cat_tuple.
              erewrite (@tcast_tval_eq A (m * l + l) (l + m * l) (addnC l (m * l)) (Tuple (cat_tupleP p ps)) (cat p ps)) => //=.
              rewrite drop_cat //= size_tuple ltnn subnn drop0 //=.
              move: (mult_subn _ _) => //=; rewrite mult_subn /eq_rect_r //= => Hm'.
              move: Hm' (Logic.eq_sym _ ) => _ H1.
              rewrite -(@Eq_rect_eq.eq_rect_eq nat (m * l) (fun y :nat => y.-tuple A -> (m*l).-tuple A) id H1) //=.
              case: ps => //= p' H4 H5; rewrite (proof_irrelevance _ H4 H5) //=.
            }

        }
Qed.


  
Lemma subseq_cons_cat (A: eqType) (ps qs: seq A) (q: A): (ps \subseteq (q::qs)) = (ps \subseteq qs ++ [:: q]).
Proof.
  elim: ps qs q => [|p ps IHps] qs q//=.
  by rewrite mem_cat mem_seq1 in_cons IHps orbC.
Qed.
  
Lemma subseq_consC (A: eqType) (ps qs rs: seq A) : (ps \subseteq (qs ++ rs)) = (ps \subseteq rs ++ qs).
Proof.
  elim: ps qs rs  => [|p ps IHps] qs rs//=.
  by rewrite !mem_cat IHps orbC.
Qed.

Lemma subseq_consA (A: eqType) (ps qs rs ts: seq A) : (ps \subseteq ((qs ++ rs) ++ ts)) = (ps \subseteq qs ++ (rs ++ ts)).
Proof.
  elim: ps qs rs ts  => [|p ps IHps] qs rs ts//=.
  by rewrite !mem_cat IHps orbA.
Qed.


Lemma bloomfilter_add_multiple_unwrap_internal bf
      hashes l value (values: seq B) inds:
       length values == l ->
       hashes_have_free_spaces hashes (l.+1) ->
       all (bloomfilter_value_unseen hashes) (value::values) ->
  \rsum_(a in [finType of k.-tuple (HashState n) * BloomFilter])
     ((d[ bloomfilter_add_multiple (Tuple (hash_vec_insert_length value hashes inds)) bf
            values]) a *R*
      (d[ let (hashes2, bf) := a in res' <-$ bloomfilter_query value hashes2 bf; ret res'.2]) true) =
  \rsum_(a in [finType of k.-tuple (HashState n) * BloomFilter])
     ((d[ bloomfilter_add_multiple (Tuple (hash_vec_insert_length value hashes inds)) bf
            values]) a *R*
      (bloomfilter_query_internal inds a.2 == true %R)).
Proof.
  move: hashes; rewrite/hash_vec => hashes.
  move=>  Hlen Hfree Hall; apply eq_bigr => [[hshs' bf']] _.
  case Hzro: ((d[ bloomfilter_add_multiple (Tuple (hash_vec_insert_length value hashes inds)) bf values])
     (hshs', bf') == 0); first by move/eqP:Hzro -> ; rewrite !mul0R.
  move/Bool.negb_true_iff: Hzro => Hzro.
  apply f_equal.
  rewrite //= /bloomfilter_query_internal //=.
  rewrite DistBind.dE rsum_split //=.
  under big a _ under big b _ rewrite mulRC Dist1.dE eq_sym.
  under big a _ rewrite -rsum_pred_demote big_pred1_eq DistBind.dE rsum_split //=.
  under big a _ under big a0 _ under big b _ rewrite mulRC Dist1.dE xpair_eqE boolR_distr -mulRA.
  rewrite exchange_big //=; under big a0 _ rewrite exchange_big; under big b _ rewrite -rsum_pred_demote big_pred1_eq //=.
  move=>//=.
  rewrite eqb_id; under big a0 _ under big b _ rewrite eq_sym !eqb_id.
  have Hallleq: all
     (fun hsh : FixedList.fixlist [eqType of hash_keytype * hash_valuetype] n =>
      FixedList.fixlist_length hsh + 1 <= n) hashes.
  {
    move: Hfree;rewrite/hashes_have_free_spaces/hash_has_free_spaces=>/allP Hfree;apply/allP=>ind Hind.
      by move: (Hfree ind Hind); rewrite addn1 addnS =>/ltn_weaken.    
  }

  move: (@hash_vec_contains_value_base _ _ value hashes inds Hallleq) => Hcontains'.
  move: (@bloomfilter_add_multiple_find_preserve value inds (Tuple (hash_vec_insert_length value hashes inds)) hshs' bf bf' values Hcontains' Hzro) => Hcontains''.
  under big a0 _ under big b _ rewrite (@hash_vec_find_simpl n k value hshs' _ inds _ Hcontains'') //=.

  under big a0 _ under big b _ rewrite mulRC andbC boolR_distr -!mulRA.
  under big a0 _ rewrite -rsum_pred_demote big_pred1_eq.
  by rewrite -rsum_pred_demote big_pred1_eq.
Qed.


Lemma fixedlist_set_nthC (A:eqType) l (vec: l.-tuple A) (ind: 'I_l) (ind': 'I_l) (a : A):
   FixedList.set_tnth (FixedList.set_tnth vec a ind) a  ind' =
  FixedList.set_tnth (FixedList.set_tnth vec a ind') a ind.
Proof.
  elim: l ind ind' vec => [|l IHl] [ind Hind] [ind' Hind'] vec;
  first by rewrite !tuple0 //=.

  - {

      case: ind' Hind' => [|ind'] Hind'; case: ind Hind => [|ind] Hind //=; case: vec => [[| v vs] Hvs];
      rewrite ?ntuple_tailE /FixedList.ntuple_head ?theadE //=.

      - {
          have ->: (thead (Tuple Hvs)) = v; first by [].

          rewrite/FixedList.ntuple_tail//=.

          move: (behead_tupleP _ ) => //= H1; move: (behead_tupleP _) => //= H2; move: (behead_tupleP _ ) => //= H3.
          move: H2; rewrite (proof_irrelevance _ H1 H3) => H2; clear H1.

          rewrite!/[tuple of _ ] //=; move: (valP _) => //= H4; move: (valP _) => //= H5.
          by rewrite (proof_irrelevance _ H4 H5).
        }
      - {
          rewrite!/[tuple of _ ] //=; move: (valP _) => //= H4; move: (valP _) => //= H5.
          by rewrite (proof_irrelevance _ H4 H5).
        }
      - {

          have H1: (ind < l); first by move: Hind => /ltn_SnnP.
          have H2: (ind' < l); first by move: Hind' => /ltn_SnnP.
          by move: (@IHl (Ordinal H1)  (Ordinal H2) (FixedList.ntuple_tail (Tuple Hvs))) => //= -> //=.
        }  
    }
Qed.

Lemma bloomfilter_set_bit_conv bf b b':
  (bloomfilter_set_bit b (bloomfilter_set_bit b' bf)) =
  (bloomfilter_set_bit b' (bloomfilter_set_bit b bf)).
Proof.

  rewrite/bloomfilter_set_bit/bloomfilter_state; apply f_equal.
  case: bf; rewrite/BitVector=>bf .
  by rewrite  fixedlist_set_nthC.
Qed.

Lemma bloomfilter_add_multiple_cat bf b others:
  (bloomfilter_add_internal others (bloomfilter_add_internal b bf)) =
    (bloomfilter_add_internal (others ++ b) bf).
Proof.

  elim: others bf => [//=|other others Hothers] bf //= .
  rewrite -Hothers; apply f_equal; clear Hothers others.
  elim: b bf => [//=| b bs Hbs] bf //=.
  rewrite  bloomfilter_set_bit_conv.
  by rewrite Hbs.
Qed.

  

Lemma bloomfilter_add_multiple_unwrap_base 
        hashes l (values: seq B) others inds:
  uniq values ->
       length values == l ->
       hashes_have_free_spaces (hashes: k.-tuple (HashState n)) (l) ->
       all (bloomfilter_value_unseen hashes) (values) ->
  \rsum_(a in [finType of (k.-tuple (HashState n) * BloomFilter)]%type)
   ((d[ bloomfilter_add_multiple hashes bloomfilter_new values]) a *R*
    ((all (bloomfilter_get_bit^~ (bloomfilter_add_internal others a.2)) inds == true) %R)) =
  \rsum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
     ((inds \subseteq hits ++ others) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l * k)).
Proof.

  elim: l others values inds => [//=| l IHl] others [//=|//= value values] inds Huniq Hlen Hfree Hunseen.

  - {
      under big a _ rewrite Dist1.dE.
      rewrite -rsum_pred_demote big_pred1_eq //=.
      rewrite mul0n rsum_empty //= mulR1.

      rewrite eqb_id RIneq.INR_IZR_INZ; do?apply f_equal.
      apply eq_in_all => ind _; clear.


      case Hin: (ind \in others) => //=.
        by apply bloomfilter_add_internal_hit => //=.

        apply/Bool.negb_true_iff.
        apply bloomfilter_add_internal_miss => //=.
          by apply bloomfilter_new_empty_bits.
            by move/Bool.negb_true_iff: Hin.
    }
  - {

      move=>//=.

      move: (@subseq_imd ([finType of 'I_Hash_size.+1]) l k (fun hits => inds \subseteq hits ++ others)) => //=.
      rewrite card_ord => ->.

      have Hsusp b bs:  (inds \subseteq (b ++ bs) ++ others) = (inds \subseteq bs ++ (others ++ b)); first
        by rewrite -subseq_consA subseq_consC -subseq_consA.

      under big b _ under big bs _ rewrite Hsusp.
      under big b _ rewrite -(IHl (others ++ b) values inds) //=.
      under big a _ rewrite DistBind.dE rsum_Rmul_distr_r rsum_split //=.

      under big a _ under big a0 _ under big b _ rewrite DistBind.dE !rsum_Rmul_distr_l rsum_split //=.
      under big a _ under big a0 _ under big b _ under big a1 _ under big b0 _ rewrite Dist1.dE.

      rewrite exchange_big; under big a0 _ rewrite exchange_big; under big b _ rewrite exchange_big; under big a1 _ rewrite exchange_big;  (under big a _ under big c _  rewrite mulRA mulRC mulRA mulRC mulRA mulRC mulRA mulRA mulRC -mulRA); under big b0 _ rewrite -rsum_pred_demote big_pred1_eq.

      (under big a0 _ (under big b _ rewrite exchange_big); rewrite exchange_big); rewrite exchange_big.

      apply eq_bigr => b _ .

      rewrite rsum_Rmul_distr_l rsum_split //= [\rsum_(a in _) (\rsum_(b in _) (_ *R* _))]exchange_big.
      rewrite [\rsum_(i in [finType of k.-tuple (HashState n)]) (\rsum_(i0 in [finType of BloomFilter]) _)]exchange_big ; apply eq_bigr => bf' _.
      apply eq_bigr => hshs' _.


      rewrite -!rsum_Rmul_distr_l.

      rewrite mulRC -mulRA  mulRC -mulRA mulRC.
      apply Logic.eq_sym => //=.

      rewrite  -mulRA  mulRC -mulRA mulRC -mulRA.

      rewrite  bloomfilter_add_multiple_cat; apply f_equal.

      case Hzr0: ((d[ bloomfilter_add_multiple hashes bloomfilter_new values]) (hshs', bf') == 0);
        first by move/eqP: Hzr0 ->;rewrite mulR0 mul0R //=.
      move/Bool.negb_true_iff: Hzr0 => Hzr0.
      rewrite mulRC; apply f_equal; apply Logic.eq_sym.

      clear IHl.

      have H1:   (uniq (value :: values)); first by [].
      have H2: length values == l; first by move: Hlen =>/eqP [->].
      have H3: hashes_have_free_spaces hashes (l + 0).+1; first by rewrite addn0.
      have H4: all (bloomfilter_value_unseen hashes) (value :: values); first by [].
      move: (@bloomfilter_add_multiple_preserve
               value
               values l 0 hashes hshs' bloomfilter_new bf'
               H1 H2 H3 H4 Hzr0
            ) => /andP [Hfree' Huns'].

      move: (@hash_vec_simpl n k hshs' value b (fun _ => 1) Huns')=> //=.
      (under big a _ rewrite mulR1); by move=>->; rewrite mulR1 //=.

        by move/andP: Huniq => [].

        move/allP: Hfree => Hfree; apply/allP => ind Hind; move: (Hfree ind Hind).
          by rewrite/hash_has_free_spaces; rewrite addnS =>/ltnW.
            by move/andP: Hunseen => [].
    }
Qed.

Lemma fixedlist_add_incr (A B: eqType) (l m n': nat) (hsh: l.-tuple (option [eqType of (B * A)])) (ind: A) (value: B):
    length (FixedList.fixlist_unwrap hsh) + m < n' ->
  length (FixedList.fixlist_unwrap (FixedMap.fixmap_put value ind hsh)) + m <= n'.
Proof.

  move=> H.
  move:(ltn_SnnP (length (FixedList.fixlist_unwrap hsh) + m) n') => [_ ] H'.
  move: (H' H); clear H' H.
  rewrite -addSn addnC -ltn_subRL => Hlen.
  rewrite -ltnS addnC -ltn_subRL.
  eapply leq_ltn_trans; last by exact Hlen.
  clear Hlen.
  move: hsh => [ls Hls].
  elim: l ls Hls => [//=| l IHl]  [//=| x xs] Hxs //=.
  have->: (FixedList.ntuple_head (Tuple Hxs)) = x; first by [].
  case: x xs Hxs => [[k' v']|] xs Hxs; last first; last case Heq: (_ == _).
   - by apply (@leq_ltn_trans  (FixedList.fixlist_length (Tuple Hxs))) => //=.

   - by rewrite ltnS leq_eqVlt ltnS; apply/orP; right; rewrite leq_eqVlt; apply/orP; left=>//=.
   - 
     rewrite /FixedList.ntuple_tail; move: (behead_tupleP _) => //= Hls'.
     move: (IHl xs Hls') => IHl'.
     rewrite/FixedList.fixlist_length/FixedList.ntuple_cons.
       by case Hput: (FixedMap.fixmap_put _) => [ms Hms] //=; move: IHl';rewrite Hput.
Qed.

Lemma bloomfilter_add_multiple_unwrap 
        hashes l value (values: seq B) inds:
  uniq (value::values) ->
       length values == l ->
       hashes_have_free_spaces (hashes: k.-tuple (HashState n)) (l.+1) ->
       all (bloomfilter_value_unseen hashes) (value::values) ->
  \rsum_(a in [finType of k.-tuple (HashState n) * BloomFilter])
     ((d[ bloomfilter_add_multiple (Tuple (hash_vec_insert_length value hashes inds)) bloomfilter_new
            values]) a *R*
      (d[ let (hashes2, bf) := a in res' <-$ bloomfilter_query value hashes2 bf; ret res'.2]) true) =
  \rsum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
     ((inds \subseteq hits) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l * k)).
Proof.      


  rewrite/bloomfilter_query //= => Huniq Hlen Hfree Hunseen.
  rewrite (@bloomfilter_add_multiple_unwrap_internal _ _ l) => //=.
  rewrite //= /bloomfilter_query_internal.

  move: Huniq => //=/andP[Hnin Huniq].
  move: (@bloomfilter_add_multiple_unwrap_base
           (Tuple (hash_vec_insert_length value hashes inds)) l values [::] inds Huniq Hlen
        ) => //=.
  under big a _ rewrite cats0.
  move=>-> //=.

  - {
      move: Hfree; rewrite/hashes_have_free_spaces/hash_has_free_spaces//=; clear.
      move=>/allP Hfree; apply/allP => [ //= hsh' /mapP [[hsh ind] /mem_zip/andP [Hhsh Hind] ->]].
      rewrite/hashstate_put //=.
      move: (Hfree hsh Hhsh); clear.      
      rewrite/FixedList.fixlist_length => //=.
      move=> H; apply/ fixedlist_add_incr;move: H.
      by rewrite addnS.
    }
  - {
      move/andP: Hunseen Hnin => [Huns ]; clear.
      rewrite/bloomfilter_value_unseen //=; move=>/allP Hfree Hnin.
      apply/allP => [//= value' Hvalue]; move: (Hfree value' Hvalue)=>/allP  Hfree'.
      apply/allP => //= [ hsh' /mapP [[hsh ind] /mem_zip/andP [Hhsh Hind] ->]].
      move: (Hfree' hsh Hhsh ).
      move/memPn: Hnin => /(_ value' Hvalue); clear; rewrite /hash_unseen/hashstate_put.
      by move=> Hnew Hfind; apply fixmap_find_neq => //=.
    }
Qed.    
  

  
  

  

  



Theorem bloomfilter_collission_rsum
        hashes l value (values: seq B):
       length values == l ->
       hashes_have_free_spaces hashes (l.+1) ->
       all (bloomfilter_value_unseen hashes) (value::values) ->
       uniq (value::values) ->
        d[ 
            res1 <-$ bloomfilter_query value hashes (bloomfilter_new);
            let (hashes1, init_query_res) := res1 in
            res2 <-$ bloomfilter_add_multiple hashes1 (bloomfilter_new) values;
            let (hashes2, bf) := res2 in
            res' <-$ bloomfilter_query value hashes2 bf;
            ret (res'.2)
          ] true =
        \rsum_(inds in [finType of k.-tuple ('I_Hash_size.+1)])
         ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
          (\rsum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
            ((( inds \subseteq hits) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l * k)))))).
Proof.
  have H x y z: (y = (0%R)) -> x = z -> x +R+ y = z. by move => -> ->; rewrite addR0.

  move=>//= Hlen Hfree /andP[Huns Halluns]/andP[Hnin Huniq].

  rewrite DistBind.dE.

  (under big a _ rewrite DistBind.dE  rsum_Rmul_distr_r rsum_split exchange_big //=).


  rewrite exchange_big //=.
  (under big j _ rewrite exchange_big//=).

  under big j _ rewrite (bigID (fun i => i == Tuple (hash_vec_insert_length value hashes j))) big_pred1_eq hash_vecP //=.

  have Hfail j: 
\rsum_(i | i != Tuple (hash_vec_insert_length value hashes j))
         \rsum_(i0 in ([finType of k.-tuple (HashState n) * bool]))
            ((d[ let (hashes1, _) := i0 in
                 res2 <-$ bloomfilter_add_multiple hashes1 bloomfilter_new values;
                 (let (hashes2, bf) := res2 in res' <-$ bloomfilter_query value hashes2 bf; ret res'.2)])
               true *R*
             ((d[ hash_vec_int value hashes]) (i, j) *R*
              (Dist1.d (i, bloomfilter_query_internal j bloomfilter_new)) i0)) = (0%R).
  {
    apply prsumr_eq0P => i Hni; first by dispatch_Rgt.
    apply prsumr_eq0P => i0 _; first by dispatch_Rgt.
    rewrite neg_hash_vecP //=  mul0R ?mulR0 //=.
  }



  under big j _ rewrite Hfail addR0 //=.
  apply eq_bigr => inds _.
  under big i _ rewrite Dist1.dE //=.
  rewrite rsum_split //=.

  under big a _ under big b _ rewrite xpair_eqE.
  move: (size_tuple inds) Hkgt0 => {1}<- Hiff.
  move/Bool.negb_true_iff: (bloomfilter_new_empty Hiff) => Hfalse.
  under big a _ under big b _ rewrite Hfalse //=.

  rewrite (bigID (fun a => a == Tuple (hash_vec_insert_length value hashes inds))) big_pred1_eq//=.
  apply H; first by apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; rewrite !mulR0 bigsum_card_constE mulR0; try ( right).


  under big b _ rewrite eq_refl //=.

  rewrite (bigID (fun b => b == false)) big_pred1_eq //=.

  apply H; first by rewrite (eq_bigl (fun i => i == true)); first rewrite big_pred1_eq //= !mulR0; last by case.
  rewrite mulR1 mulRC; apply f_equal.

  rewrite DistBind.dE.

  erewrite  bloomfilter_add_multiple_unwrap => //=.
  by apply/andP; split=>//=.
  by apply/andP; split=>//=.
Qed.


Lemma subseq_conv l:
          \rsum_(inds in [finType of k.-tuple ('I_Hash_size.+1)])
         ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
          (\rsum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
            ((( inds \subseteq hits) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l * k)))))) =
((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l.+1 * k) *R*
   \rsum_(a in ordinal_finType (l * k))
      (((((a %R) ^R^ k) *R* (Factorial.fact a %R)) *R* ('C(l * k, a) %R)) *R* stirling_no_2 (l * k) a)).
Proof.

  under big inds _ rewrite rsum_Rmul_distr_l.
  rewrite exchange_big.

  under big inds _ under big inds' _ rewrite mulRA mulRC.

  under big inds _ rewrite -rsum_Rmul_distr_l; under big inds' _ rewrite mulRC.

  have Hbool inds' inds: (inds' \subseteq inds %R) = (inds' \subseteq inds); first by rewrite RIneq.INR_IZR_INZ.

  under big inds _ under big ps _ rewrite -Hbool.
  under big inds _ rewrite -rsum_pred_demote.
  (under big inds _ rewrite rsum_subseq_mult_undup_eq rsum_subseq_mult //=); last first.
  by apply undup_uniq.
  move=>//=.

  

  move:  (second_stirling_number_sum l k Hash_size
(fun len => (((len %R) *R* Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k))
         ) => //= ->.

  have H len: ((((len %R) *R* Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k) *R*
      (((('C(l * k, len) %R) *R* (Factorial.fact len %R)) *R* stirling_no_2 (l * k) len) *R*
       (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l * k))) = (
        (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l.+1 * k)) *R* (
        ((len %R) ^R^ k) *R*
        (Factorial.fact len %R) *R*
        ('C (l * k, len) %R) *R*
        (stirling_no_2 (l * k) len)
        )).

  {
    rewrite expRM -mulRA.
    apply Logic.eq_sym.
    rewrite mulRC -!mulRA; apply f_equal.
    rewrite mulRC; apply Logic.eq_sym; rewrite mulRC -!mulRA; apply f_equal.
    rewrite mulRC mulRA mulRA mulRC mulRA mulRC.
    rewrite mulRC mulRA; apply Logic.eq_sym.
    rewrite mulRA mulRA mulRC -!mulRA; do?apply f_equal.
    rewrite mulSnr //=.
      by rewrite Rfunctions.pow_add.    
  }

  under big len _ rewrite H.


  by rewrite -rsum_Rmul_distr_l.
Qed.




Theorem bloomfilter_collission_prob
        hashes l value (values: seq B):
       length values == l ->
       hashes_have_free_spaces hashes (l.+1) ->
       all (bloomfilter_value_unseen hashes) (value::values) ->
       uniq (value::values) ->
        d[ 
            res1 <-$ bloomfilter_query value hashes (bloomfilter_new);
            let (hashes1, init_query_res) := res1 in
            res2 <-$ bloomfilter_add_multiple hashes1 (bloomfilter_new) values;
            let (hashes2, bf) := res2 in
            res' <-$ bloomfilter_query value hashes2 bf;
            ret (res'.2)
          ] true =
((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l.+1 * k) *R*
   \rsum_(a in ordinal_finType (l * k))
      (((((a %R) ^R^ k) *R* (Factorial.fact a %R)) *R* ('C(l * k, a) %R)) *R* stirling_no_2 (l * k) a)).
Proof.
  intros; rewrite (@bloomfilter_collission_rsum _ l) => //=.
  by rewrite  subseq_conv.
Qed.

(* Local Variables: *)
(* company-coq-local-symbols: (("\\subseteq" . ?⊆)) *)
(* End: *)

