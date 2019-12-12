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

From ProbHash.Utils
     Require Import  InvMisc   seq_ext seq_subset.
From ProbHash.Computation
     Require Import Comp Notationv1.
From ProbHash.Core
     Require Import Hash.


Ltac dispatch_Rgt :=  do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply fdist_ge0_le1=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size).

Open Scope R_scope.

Notation "a '/R/' b " := (Rdefinitions.Rdiv a b) (at level 70).
Notation "a '+R+' b " := (Rdefinitions.Rplus a b) (at level 70).
Notation "a '*R*' b " := (Rdefinitions.Rmult a b) (at level 70).
Notation "a '-R-' b " := (Rdefinitions.Rminus a b) (at level 70).
Notation "a '-<-' b " := (Rdefinitions.Rlt a b) (at level 70).
Notation "a '-<=-' b " := (Rdefinitions.Rle a b) (at level 70).
Notation "a '->-' b " := (Rdefinitions.Rgt a b) (at level 70).
Notation "a '->=-' b " := (Rdefinitions.Rge a b) (at level 70).
Notation "d[ a ]" := (evalDist a) (at level 70).
Reserved Notation "a '^R^' b"  (at level 70).
Notation "a '%R' " := (Raxioms.INR a) (at level 70).
(* We'll use the definition of rpower for natural numbers as
   coq's Rpower doesn't support raising 0 to a power  *)
Notation "a '^R^' b" := (Rpow_def.pow a b).

Coercion BinInt.Z.of_nat : nat >-> BinNums.Z.
Coercion Rdefinitions.IZR : BinNums.Z >-> Rdefinitions.R.

Lemma boolR_distr (a b : bool) : (a && b %R) = ((a %R) *R* (b %R)).
Proof.
    by case: a; case: b => //=; rewrite ?mulR1 ?mul1R ?mulR0 ?mul0R //=.
Qed.

Lemma bool_neq0_true (v:bool) :
  (v %R) != BinNums.Z0 -> v = true.
Proof. by case: v => //=; move=> /eqP //=. Qed.


Lemma distbind_dist (A B C: finType) (a : dist A) (c : A -> B) (g: B -> dist C)  :
  FDistBind.d a (fun x => FDistBind.d (@FDist1.d _ (c x)) g) = FDistBind.d a (fun x =>  g (c x) ).
Proof.
  rewrite (functional_extensionality (fun x : A => FDistBind.d (FDist1.d (c x)) g) (fun x : A => g (c x))) => //= x.
    by rewrite FDistBind1f.
Qed.

Lemma rsum_Rmul_distr_l (A: finType) (pr: A -> Rdefinitions.R) x :
  x *R* \sum_(a in A) (pr a) = \sum_(a in A) (x *R* (pr a)).
Proof.
  rewrite unlock => //=; elim: (index_enum _) x => [x|] //=; first by rewrite mulR0.
  move=> y ys Hys x.
    by rewrite Raxioms.Rmult_plus_distr_l; apply f_equal; rewrite Hys. 
Qed.

Lemma rsum_Rmul_distr_r (A: finType) (pr: A -> Rdefinitions.R) x :
  \sum_(a in A) (pr a) *R*  x  = \sum_(a in A) (x *R* (pr a)).
Proof.
    by rewrite mulRC rsum_Rmul_distr_l.
Qed.

Lemma rsum_split (A B: finType) p :
  \sum_(x in [finType of (A * B)]) (p x) = \sum_(a in A) \sum_(b in B) (let x := (a,b) in (p x)).
Proof.
  unfold all => //=.
  rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
  rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
  rewrite !enumT.
  elim: (Finite.enum A); elim: (Finite.enum B); try by rewrite unlock => //=.
  - {
      rewrite unlock => //=; move=> _ xs //=.
      have ->: (flatten [seq [::] | _ <- xs] = [::]); first by move=> T; elim: xs.
        by rewrite add0R.      
    }
  - {
      move=> x xs IHx x' xs' IHx'.
        by rewrite big_allpairs !big_cons.      
    }
Qed.

Lemma rsum_pred_demote (A : finType) (b : pred A) (f: A -> Rdefinitions.R):
  \sum_(a in A | b a) (f a) = \sum_(a in A) ((b a %R) *R* (f a)).
Proof.
  apply Logic.eq_sym; rewrite (bigID (fun a => b a)) //=.   
  have->: (\sum_(i | ~~ b i) ((b i %R) *R* f i)) = (Rdefinitions.IZR 0); rewrite ?addR0.
  - {
      have<-: (\sum_(i | ~~ b i) (Rdefinitions.IZR 0)) = Rdefinitions.IZR 0; first by rewrite bigsum_card_constE mulR0.    
        by apply eq_bigr=> i /Bool.negb_true_iff ->; rewrite //= mul0R.
    }
      by apply eq_bigr=> i ->; rewrite //= mul1R.
Qed.

Lemma rsum_tuple_split (A: finType) m (f: (m.+1).-tuple A -> Rdefinitions.R) :
  \sum_(a in [finType of (m.+1).-tuple A]) (f a) =
  \sum_(aas in [finType of (A * m.-tuple A)]) (let: (x, xs) := aas in f (cons_tuple x xs)).
Proof.
  rewrite (reindex (fun (aas: (A * m.-tuple A)) => let: (x,xs) := aas in cons_tuple x xs)) //=.
  - by apply eq_bigr => [[x xs] _].
  - {
      split with (fun xs => (thead xs, tbehead xs)).      
      - {
          move=> [x xs] _ //=.
          rewrite theadE.
          apply f_equal.
          (* Now just to deal with the annoying dependant type errors *)
          rewrite /tbehead/cons_tuple //=.
          rewrite /[tuple of _] //=.
          move: (behead_tupleP _) => //=; move: xs => [xs Hxs] Hxs'.
            by rewrite (proof_irrelevance _ Hxs' Hxs).
        }
      - by move=> [[//=| x xs] Hxs] _; erewrite (tuple_eta) => //=.
    }
Qed.

Lemma rsum_distbind_d0 (A B:finType) (d_a: dist A) (g: B -> Rdefinitions.R) (f: A -> dist B):
  \sum_(b in B) ((FDistBind.d d_a f) b  *R* (g) b ) = 
  \sum_(b in B) \sum_(a in A) (d_a a *R*  ((f a) b *R* (g) b) ).
Proof.
  apply eq_bigr=> b _; rewrite FDistBind.dE.
  rewrite rsum_Rmul_distr_r; apply eq_bigr=> a _.
    by rewrite mulRC -mulRA.
Qed.

Lemma rsum_distbind_d1 (A B C:finType) (d_c: dist C)
      (g: A -> B -> Rdefinitions.R) (f: A -> Rdefinitions.R)
      (df: C -> dist A) :
  \sum_(b in B) \sum_(a in A) ((FDistBind.d d_c df) a *R*  (g a b) ) = 
  \sum_(b in B) \sum_(a in A) \sum_(c in C)
   ((d_c c) *R* (((df c) a) *R*  (g a b))).
Proof.
  apply eq_bigr=> b _;apply eq_bigr=> a _; rewrite FDistBind.dE.
  rewrite rsum_Rmul_distr_r; apply eq_bigr=> c _.
    by rewrite mulRC -mulRA.
Qed.

Lemma rsum_dist1_d0 (A B:finType) (a : A) (g: B -> Rdefinitions.R) (f: B -> A):
  \sum_(b in B) ((FDist1.d a) (f b) *R* (g) b ) = 
  \sum_(b in B) ((f b == a %R) *R* (g) b ).  
Proof.
    by apply eq_bigr=> b _; rewrite FDist1.dE.
Qed.

Lemma rsum_exchange_big1 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R):
  \sum_(a in A) \sum_(b in B) \sum_(c in C) (f a b c) = 
  \sum_(c in C) \sum_(b in B)  \sum_(a in A) (f a b c).
Proof.
  rewrite exchange_big [\sum_(c in C) _]exchange_big;apply eq_bigr=> b _.
    by rewrite exchange_big.
Qed.

Lemma rsum_exchange_big2 (A B C D: finType)
      (f: A -> B -> C -> D -> Rdefinitions.R):
  \sum_(a in A) \sum_(b in B) \sum_(c in C) \sum_(d in D) (f a b c d) = 
  \sum_(d in D)  \sum_(b in B)  \sum_(c in C)  \sum_(a in A) (f a b c d).
Proof.
  rewrite exchange_big [\sum_(d in D) _]exchange_big;apply eq_bigr=> b _.
  rewrite exchange_big [\sum_(i in D) _]exchange_big;apply eq_bigr=> c _.
    by rewrite exchange_big.
Qed.

Lemma rsum_exchange_big3 (A B C D E: finType)
      (f: A -> B -> C -> D -> E -> Rdefinitions.R):
  \sum_(a in A) \sum_(b in B) \sum_(c in C) \sum_(d in D) \sum_(e in E) (f a b c d e) = 
  \sum_(e in E)  \sum_(b in B)  \sum_(c in C) \sum_(d in D)  \sum_(a in A) (f a b c d e).
Proof.
  rewrite exchange_big [\sum_(e in E) _]exchange_big;apply eq_bigr=> b _.
  rewrite exchange_big [\sum_(i in E) _]exchange_big;apply eq_bigr=> c _.
  rewrite exchange_big [\sum_(i in E) _]exchange_big;apply eq_bigr=> d _.
    by rewrite exchange_big.
Qed.

Lemma rsum_rmul_distr_l1 (A B: finType)
      (f: A -> B -> Rdefinitions.R) (g: A -> Rdefinitions.R):
  \sum_(a in A) (g a *R* \sum_(b in B) (f a b)) = 
  \sum_(a in A) \sum_(b in B) (g a *R* (f a b)).
Proof.
  apply eq_bigr=> a _; rewrite rsum_Rmul_distr_l.
    by apply eq_bigr=> c _.
Qed.

Lemma rsum_rmul_distr_r1 (A B: finType)
      (f: A -> B -> Rdefinitions.R) (g: A -> Rdefinitions.R):
  \sum_(a in A) ( \sum_(b in B) (f a b) *R* g a) = 
  \sum_(a in A) \sum_(b in B) (g a *R* (f a b)).
Proof.
  apply eq_bigr=> a _; rewrite rsum_Rmul_distr_r.
    by apply eq_bigr=> c _.
Qed.

Lemma rsum_rmul_distr_l2 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R) (g: A -> B -> Rdefinitions.R):
  \sum_(a in A) \sum_(b in B) ((g a b) *R* \sum_(c in C) (f a b c)) = 
  \sum_(a in A) \sum_(b in B)   \sum_(c in C) (g a b *R* (f a b c)).
Proof.
  apply eq_bigr=> a _; apply eq_bigr=> b _; rewrite rsum_Rmul_distr_l.
    by apply eq_bigr=> c _.
Qed.

Lemma rsum_rmul_distr_r2 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R) (g: A -> B -> Rdefinitions.R):
  \sum_(a in A) \sum_(b in B) (\sum_(c in C) (f a b c) *R* (g a b)) = 
  \sum_(a in A) \sum_(b in B)   \sum_(c in C) (g a b *R* (f a b c)).
Proof.
  apply eq_bigr=> a _; apply eq_bigr=> b _; rewrite rsum_Rmul_distr_r.
    by apply eq_bigr=> c _.
Qed.

Lemma rsum_empty (A : finType) (f: 0.-tuple A -> Rdefinitions.R) :
  \sum_(a in [finType of 0.-tuple A]) (f a) = (f [tuple]).
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
       (\sum_(a in A | a != x) c) = ((#|A| - 1 %R) *R* (c)).
Proof.
  move=> Hlen; move: (bigsum_card_constE A c).
  rewrite natRB //= -addR_opp RIneq.Rmult_plus_distr_r mulNR mul1R addR_opp.
  rewrite (bigID (fun i => i == x)) big_pred1_eq//= addRC => <-.
    by rewrite -subRBA subRR subR0.
Qed.

Lemma rsum_pred_inv (A: finType) (f: dist A) (p: pred A) :
  \sum_(a in A | p a) (f a) = (1 -R- \sum_(a in A | ~~ p a) (f a)).
Proof.
  move: (fdist_is_fdist f) => [_ <-].
  have->: (\sum_(a in A) (f a) = (( \sum_(a in A | p a) f a) +R+ ( \sum_(a in A | ~~ p a) f a)) ); first by rewrite (bigID (fun a => p a)).
  by rewrite -subRBA subRR subR0.
Qed.


Lemma rsum_mem_pred (A: finType) k x :
  #|A| > 0 ->
       \sum_(xs in [finType of k.-tuple A] | x \in xs)
        ((Rdefinitions.Rinv (#|A| %R) ^R^ k)) =
       (1 -R- ((1 -R- (Rdefinitions.Rinv (#|A| %R)))  ^R^ k)).
Proof.
  rewrite rsum_pred_demote => Hord; elim: k x => [//=|k IHk] x;
                                                 first by rewrite rsum_empty //= mul0R subRR.
  rewrite rsum_tuple_split rsum_split //=.
  rewrite (bigID (fun a => a == x)) big_pred1_eq//=.
  (under eq_bigr => b _ do rewrite  mulRC -mulRA in_cons eq_refl); rewrite -rsum_Rmul_distr_l //=.
  under eq_bigr => b _ do rewrite mulR1.
  rewrite bigsum_card_constE.
  have->: (((#|[finType of k.-tuple A]| %R) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ k))) = (1 %R).
  - {
      rewrite card_tuple; rewrite -Rfunctions.Rinv_pow.
      rewrite natRexp;  rewrite mulRC mulVR //=; rewrite -natRexp; apply expR_neq0.
        by apply/eqP; apply RIneq.not_0_INR; apply/eqP; apply lt0n_neq0.
          by apply RIneq.not_0_INR; apply/eqP; apply lt0n_neq0.      
    }
    rewrite mulR1 //=.
    under eq_bigr => i Hi do under eq_bigr => b _ do (move/Bool.negb_true_iff: Hi => Hi; rewrite in_cons eq_sym Hi mulRC -mulRA//=).
    under eq_bigr => i _ do (rewrite -rsum_Rmul_distr_l; under eq_bigr => b _ do rewrite mulRC).
    rewrite rsum_sans_one_const //= IHk //=.
    rewrite natRB.
    rewrite -addR_opp RIneq.Rmult_plus_distr_r mulRA.
    rewrite mulRV //= ?mul1R.
    rewrite addRA addRC addRA addRC; apply Logic.eq_sym.
    have->: ((1 -R- (
                (1 -R- Rdefinitions.Rinv (#|A| %R)) *R*
                ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k)))) =
    ((1 -R- ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k)) +R+
     (Rdefinitions.Rinv (#|A| %R) *R* ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k) )).
  - {
      rewrite -[_ -R- (Rdefinitions.Rinv _)]addR_opp RIneq.Rmult_plus_distr_r mul1R.
        by rewrite mulNR !addR_opp subRB.
    }
    apply f_equal.
    rewrite addRC mulNR addR_opp mul1R.
      by rewrite RIneq.Rmult_minus_distr_l subRB mulR1 subRR add0R.
        by apply/eqP; apply RIneq.not_0_INR;apply/eqP; rewrite -lt0n.    
          by [].
Qed.

Lemma rsum_indep (A : finType) (pr : dist A) (f g : pred A) :
  (inde_events pr (finset.SetDef.finset f) (finset.SetDef.finset g)) ->
  \sum_(a in A) (pr a *R* (f a && g a %R)) =
  (\sum_(a in A) (pr a *R* (f a %R)) *R* \sum_(a in A) (pr a *R* (g a %R))).
Proof.
  rewrite /inde_events/Pr//=.
  rewrite [\sum_(a in _ (_ f)) _ ](rsum_setT) [\sum_(a in _ (_ g)) _ ](rsum_setT) //=.
  have: (\sum_(a in finset.SetDef.pred_of_set
                      (finset.setI (finset.SetDef.finset f) (finset.SetDef.finset g))) 
          pr a = \sum_(a | f a && g a) (pr a)).
    by apply eq_big => //=; move=> a //=; rewrite finset.in_setI !finset.in_set.
    move=>->.
    have: (\sum_(i in finset.SetDef.pred_of_set (finset.setTfor (Phant A)) | finset.SetDef.pred_of_set
                                                                               (finset.SetDef.finset f) i) (pr i) = \sum_(i | f i) (pr i)).
      by apply eq_big => //= a //=; rewrite !finset.in_set Bool.andb_true_l;
                          apply Logic.eq_sym;  rewrite -finset.in_set //=.
      move=>->.
      have: (\sum_(j in finset.SetDef.pred_of_set (finset.setTfor (Phant A)) | finset.SetDef.pred_of_set
                                                                                 (finset.SetDef.finset g) j) (pr j) = \sum_(j | g j) (pr j)).
        by apply eq_big => //= a //=; rewrite !finset.in_set Bool.andb_true_l;
                            apply Logic.eq_sym;  rewrite -finset.in_set //=.
        move=>-> Heq.
        have H x y z: (y = (0%R)) -> x = z -> x +R+ y = z. by move => -> ->; rewrite addR0.
        transitivity (\sum_(a | f a && g a) (pr a)).
        rewrite (bigID (fun a => f a && g a)) //=; apply H.
  - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
      by rewrite //=mulR0.
        by apply eq_bigr => a -> //=; rewrite mulR1.
        have: (\sum_(a in A) (pr a *R* (f a %R)) = \sum_(a | f a) (pr a)).      
        rewrite (bigID (fun a => f a)) //=; apply H.
  - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
      by rewrite //= mulR0.
        by apply eq_bigr => a -> //=; rewrite mulR1.
        move=> ->.
        have: (\sum_(a in A) (pr a *R* (g a %R)) = \sum_(a | g a) (pr a)).      
        rewrite (bigID (fun a => g a)) //=; apply H.
  - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
      by rewrite //= mulR0.
        by apply eq_bigr => a -> //=; rewrite mulR1.
        move=> ->.
          by [].
Qed.

Lemma rsum_bijective_eqC {A: finType} (c: Rdefinitions.R) (P Q : pred A) (p:  A -> A) :
  bijective p ->
  (forall a, P (p a) = Q a) ->
  \sum_(a in A | P a) c = \sum_(a in A | Q a) c.
Proof.
  move=> Hbij Himpl.
  rewrite (@reindex _ _ _ _ _ p) //=.
    by transitivity ( \sum_(j | Q j) c); first by apply eq_bigl => a'; rewrite Himpl.
      by apply onW_bij.
Qed.

Lemma pr_in_vec (A : finType) (ps : seq A) :
  #|A| > 0 ->
       uniq ps ->
       \sum_(ind in A) (Rdefinitions.Rinv (#|A| %R) *R* ((ind \notin ps) %R))
       = (1 -R- (Rdefinitions.Rinv (#|A| %R) *R* (length ps %R))).
  have: (\sum_(ind in A) (Rdefinitions.Rinv (#|A| %R) *R* ((ind \notin ps) %R))) = ( \sum_(ind in A) (((ind \notin ps) %R)  *R* Rdefinitions.Rinv (#|A| %R) )
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

Lemma prsumr_dep_ineq (A: finType) (f g : A -> Rdefinitions.R) :
  (forall a, 0 -<=- f a) ->  (forall a, 0 -<=- g a) ->  
  (\sum_(a in A) ((f a) *R* (g a))) -<=- (\sum_(a in A) (f a) *R* \sum_(a in A) (g a)).
Proof.
  move=> H1 H2; rewrite big_distrlr //=; apply ler_rsum => a _ //=; rewrite -rsum_Rmul_distr_l.
  apply RIneq.Rmult_le_compat_l => //=; rewrite (bigID (fun a' => a' == a)) big_pred1_eq //=.
    by apply leR_addl =>//=; dispatch_Rgt.
Qed.

Lemma prsumr_implb_ineq (A: finType) (p q : pred A) (f: A -> Rdefinitions.R):
  (forall a, 0 -<=- f a) -> (forall a, p a ==> q a ) ->
  \sum_(a  in A) ((p a %R) *R* (f a)) -<=-
   \sum_(a  in A) ((q a %R) *R* (f a)).
Proof.
  move=> Hpr Himpl.
  apply ler_rsum => a H.
  apply RIneq.Rmult_le_compat_r; try by apply Hpr.
  move: (Himpl a); case: (p a) => //=; first by move=> -> //=; apply leRR.
  move=>_;case: (q a) => //=; by apply leRR.
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
  move: (fdist_is_fdist (d[ pr])) => [_ <-].
  rewrite //= !FDistBind.dE.
  apply subR_eq;  rewrite -addRA_rsum; apply eq_bigr => a _.
  rewrite mulRC [((d[ pr]) a *R* _)]mulRC -RIneq.Rmult_plus_distr_r !FDist1.dE.
  rewrite -{1}(mulR1 (_ a)); apply Logic.eq_sym; rewrite mulRC; apply f_equal.
    by case: (f a) => //=; rewrite ?addR0 ?add0R.
Qed.

Lemma prsum_nge0p {A: finType}  f : 
  (forall a : A, 0 -<=- f a) -> (forall a : A, ~ (f a  ->- (0 %R))) -> (forall a, f a = (0 %R)).
Proof.
  move=> Hdist Hngt a; move/RIneq.Rnot_gt_le: (Hngt a) (Hdist a).
    by move=>/RIneq.Rle_antisym H /H.
Qed.

Lemma prsumr_ge0 (A : finType) (f: A -> Rdefinitions.R) : (forall a : A, (0 -<=- f a)) -> \sum_(a in A) f a <> (0 %R) <-> (exists a,  f a ->- (0 %R)).
Proof.
  have HforalleqP : (forall x, f x = (0 %R)) -> (forall x, (fun _ => true) x -> f x = (0 %R)). by [].
  have HforallgtP : (forall x, 0 -<=- f x) -> (forall x, (fun _ => true) x -> 0 -<=- f x). by [].
  move=> Hgt0.
  split.
  - {
      move=>/eqP/negP Rsumr0. 
      case Heq0: (~~ [exists a, (gtRb (f a) (0 %R))]).
      - {
          move/negP/negP:Heq0 => Heq0.
          rewrite negb_exists in Heq0.
          have Hforalleq: (forall x, ~~ (geRb (f x)  (0 %R))) -> (forall x, ~ (geRb (f x) 0)).
           {
               - by move=> Hb x; move/negP: (Hb x) => Hbool //=.
           }
           move/forallP: Heq0 => Heq0.
           have: (forall x:A, ~ (f x) ->- 0).
           { by move=> x; apply/gtRP. }
           move/(prsum_nge0p Hgt0) => H.
           have: False => //=.
          - {
           apply Rsumr0; apply/eqP.
           transitivity (\sum_(a in A) (0 %R)).
                by apply eq_bigr=> a _; rewrite H.
                  by rewrite (bigsum_card_constE A) mulR0.              
             }
        }
      - by move/negP/negP/existsP: Heq0 => [x Hx]; split with x;  move/gtRP: Hx.          
    }
  - {
      move=>[a  Ha].
      move=>/prsumr_eq0P H.
      have: (forall a: A, a \in A -> 0 -<=- f a); first by move=> a' _; apply Hgt0.
        by move=>/H H'; move: Ha; rewrite H' //= => /RIneq.Rgt_irrefl.
    }
Qed.

Lemma prsum_multeq0 (A B: finType) (pr1 :  A -> Rdefinitions.R) (pr2 : B -> Rdefinitions.R):
  (forall (a : A) (b: B), (pr1 a) *R* (pr2 b) = Rdefinitions.IZR 0) ->
  (\sum_(a in A) (pr1 a) *R* \sum_(b in B) (pr2 b)) = Rdefinitions.IZR 0.
  move=> H1.
  rewrite unlock; rewrite /index_enum/reducebig//=.
  elim: (Finite.enum _) => //=; first by rewrite mul0R.
  elim: (Finite.enum _) => [x xs Hxs |] //=; first by rewrite mulR0.
  move=> y ys Hxs x xs Hys.
  rewrite RIneq.Rmult_plus_distr_r Hys addR0 Raxioms.Rmult_plus_distr_l H1 add0R.
    by move: (Hxs x [::]) => //=; rewrite mul0R addR0 => ->.
Qed.

Lemma prsumr_sans_one (A: finType) (f: A -> Rdefinitions.R) (a': A) c:
  f a' = c ->
  \sum_(a in A) (f a) = (1 %R) ->
  \sum_(a | a != a') (f a) = (1 -R- c).
Proof.
  have: ((Rdefinitions.IZR (BinNums.Zpos BinNums.xH)) == (1 %R)). by [].
  move=> /eqP -> <- //=  <-.
  rewrite [\sum_(a in A) _](bigID (fun a => a == a')) => //=.
  rewrite big_pred1_eq.
    by rewrite addRC -subRBA subRR subR0.
Qed.

Lemma rsum_subseq_internal (m : nat) (I J: seq 'I_m) :
  m > 0 -> uniq I -> all (fun j => j \notin I) J ->
  \sum_(i in 'I_m | i \notin J) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R)) =
  (((length I %R) *R* Rdefinitions.Rinv (m %R))).
Proof.
  move=> Hm; elim: I J => [|i I IHI] J Huniq Hall; first
                            by rewrite //= ?mul0R bigsum_card_constE ?mulR0.
  under eq_bigr => i0 _ do rewrite in_cons.
  rewrite rsum_pred_demote (bigID (fun i0 => i0 == i)) big_pred1_eq //= eq_refl //= mul1R.
  move: (Hall); rewrite all_in_negP => //=/andP[-> Hall'] //=; rewrite mul1R.
  rewrite -addn1 natRD RIneq.Rmult_plus_distr_r mul1R [(_ *R* _) +R+ _]addRC; apply f_equal.
  transitivity (\sum_(i0 < m | i0 \notin (i :: J)) ((((i0 \in I) %R) *R* Rdefinitions.Rinv (m %R)))).
  - {
      rewrite rsum_pred_demote [ \sum_(i0 < _ | _) _]rsum_pred_demote; apply eq_bigr => i0 _ //=.
        by rewrite in_cons Bool.negb_orb;
          case: (_ == _);
          case: (_ \in _);
          rewrite ?mulR0 ?mul0R ?mul1R ?mulR1//=.      
    }
    apply IHI => //=.
  - by move: Huniq => //=/andP[].
  - apply/andP; split.
  - by move: Huniq => //=/andP [].  
  - move/allP: Hall => Hall; apply/allP => j Hj.   
      by move: (Hall j Hj); rewrite in_cons Bool.negb_orb =>/andP[].
Qed.

Lemma rsum_subseq (m : nat) (I : seq 'I_m) :
  m > 0 -> uniq I -> 
  \sum_(i in 'I_m) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R)) =
  (((length I %R) *R* Rdefinitions.Rinv (m %R))).
Proof.
  move=> Hm Huniq.
  transitivity ( \sum_(i in 'I_m | i \notin [::]) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R))); first
    by apply eq_bigl => i //=.
    by apply rsum_subseq_internal => //=.
Qed.

Lemma rsum_subseq_mult (m b: nat) (I: seq 'I_m):
  0 < m ->
  uniq I ->
  \sum_(ps in [finType of b.-tuple 'I_m] | ps \subseteq I)
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
      under eq_bigr => a _ do under eq_bigr => b0 _ do  rewrite Hsusp.
        by rewrite -big_distrlr //= -!rsum_pred_demote IHb 1?rsum_pred_demote 1?rsum_subseq //=.
    }
Qed.

Lemma rsum_subseq_undup_eq (m : nat) (I : seq 'I_m) : 
  \sum_(i in 'I_m) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R)) =
  \sum_(i in 'I_m) (((i \in undup I) %R) *R* Rdefinitions.Rinv (m %R)).
Proof.
     by under eq_bigr => i Hi do rewrite -mem_undup.
Qed.

Lemma rsum_subseq_mult_undup_eq (m b: nat) (I: seq 'I_m):
  \sum_(ps in [finType of b.-tuple 'I_m] | ps \subseteq I)
   ((Rdefinitions.Rinv (m %R)) ^R^ b) = 
  \sum_(ps in [finType of b.-tuple 'I_m] | ps \subseteq undup I)
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
  under eq_bigr => a _ do under eq_bigr => b0 _ do rewrite Hsusp.
  rewrite -big_distrlr //= -!rsum_pred_demote IHb 2!rsum_pred_demote big_distrl.
  apply Logic.eq_sym; rewrite rsum_pred_demote rsum_tuple_split rsum_split //=.
  apply eq_bigr=> a _;  rewrite rsum_Rmul_distr_l; apply eq_bigr=> b0 _.
    by rewrite mem_undup Hbool -mulRA -mulRA; apply f_equal;
      rewrite mulRC -mulRA; apply f_equal; rewrite mulRC.
Qed.

Lemma subseq_imd (A: finType) (m l: nat) (f: (m.+1 * l).-tuple A -> Rdefinitions.R):
  \sum_(bs in [finType of (m.+1 * l).-tuple A])
   (f bs *R* (Rdefinitions.Rinv (#|A| %R) ^R^ (m.+1 * l))) = 
  \sum_(b in [finType of l.-tuple A])
   ((Rdefinitions.Rinv (#|A| %R) ^R^ l) *R*
    \sum_(bs in [finType of (m * l).-tuple A])
      (f (cat_tuple b bs) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ (m * l)))
   ).
Proof.
  under [  \sum_(b in [finType of l.-tuple A]) _]eq_bigr => b _ do rewrite rsum_Rmul_distr_l.
  apply Logic.eq_sym.
  have Hoqv Q p q (vec : seq Q): (size vec == p.+1 * q) = (size vec == q + p * q);
    first by rewrite mulSnr addnC.
  have H: (m * l + l) = (m.+1 * l); first by rewrite mulSnr.
  transitivity (\sum_(x in [finType of (l.-tuple A * (m * l).-tuple A)%type])
                 (let (b,a) := x in ((Rdefinitions.Rinv (#|A| %R) ^R^ l) *R*
                                     (f ((cat_tuple b a)) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ m * l)))) ).
    by rewrite rsum_split //=; do ? (apply eq_bigr; intros); do ?apply f_equal => //=.
    rewrite (@reindex Rdefinitions.R Rdefinitions.R0 _ ([finType of (l.-tuple A * (m * l).-tuple A)]) _ (@tuple_split A m l)) => //=.
    rewrite rsum_pred_demote //=; under eq_bigr => a _ do rewrite mul1R.
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
