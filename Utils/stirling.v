From mathcomp.ssreflect Require Import
     ssreflect ssrbool ssrnat fintype eqtype 
     seq bigop binomial finset.

From mathcomp.ssreflect Require Import tuple.


From infotheo Require Import 
     ssrR Reals_ext   ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From ProbHash.Utils
     Require Import InvMisc seq_ext seq_subset rsum_ext.

Open Scope R_scope.


Lemma index_iota_incr m n: 
  [seq x.+1 | x <- index_iota m n] = index_iota m.+1 n.+1.
Proof.
  rewrite /index_iota subSS.
    by move: (iota_addl 1 m (n - m));  rewrite !add1n => <-.
Qed.


Section stirling_second_number.

  Definition stirling_no_2 (n k: nat):=
    Rdefinitions.Rinv (Factorial.fact k) *R* (
      \sum_(i in 'I_(k.+1)) (((Rdefinitions.Ropp 1) ^R^ i) *R*
                             ('C (k, i) %R) *R*
                             (((k %R) -R- (i %R)) ^R^ n)
                            )
    ).


  Section partitions.
    Variables l k m : nat.

    Lemma vector_sum_subset: forall v: [finType of (l * k).-tuple 'I_m.+1],
        v \in [finType of (l * k).-tuple 'I_m.+1] ->
              [set x | x \in tval v] \subset [set x |  nat_of_ord x < m + 1].
    Proof.
      (* Convert to equation in terms of elements *)
      move=> v _; rewrite unlock; apply/pred0P => x; rewrite !inE.
      (* manipulate boolean expresions *)
      apply  Bool.negb_true_iff; apply /eqP; rewrite eqb_id Bool.negb_andb Bool.negb_involutive.

        (* first term must be true *)
        by rewrite addn1 (ltn_ord x).

    Qed.

    Lemma undup_length_bound_internal: forall v: [finType of (l * k).-tuple 'I_m.+1],
        length (undup v) <= m + 1.
    Proof.
      move=> v.
      (* convert ltn to subset relation *)
      rewrite -length_sizeP addn1 -{4}(size_enum_ord (m.+1)).
      move: (enum_uniq 'I_m.+1) (undup_uniq v) =>  Huniq_enum Huniq_undup.
      move: (card_uniqP Huniq_undup ) (card_uniqP Huniq_enum ) => <- <-.
      apply subset_leq_card.
      (* convert subset to expression on elements *)
      rewrite unlock; apply/pred0P => x; rewrite !inE.
      apply  Bool.negb_true_iff; apply /eqP; rewrite eqb_id Bool.negb_andb Bool.negb_involutive.
      (* trivial *)
      apply/orP; left => //=.
      rewrite unfold_in //=.
        by apply mem_enum.
    Qed.


    Lemma undup_length_bound_ord: forall v: [finType of (l * k).-tuple 'I_m.+1],
        length (undup v) < m + 2.
    Proof.
      move=> v; rewrite addn2 ltnS -{4}addn1.
        by apply undup_length_bound_internal.
    Qed.
    

    Lemma undup_length_bound: forall v: [finType of (l * k).-tuple 'I_m.+1],
        v \in [finType of (l * k).-tuple 'I_m.+1] ->
              length (undup v) <= m + 1.
    Proof.
      move=> v _.
        by apply undup_length_bound_internal.
    Qed.
    
  End partitions.


  Lemma subset_combinations m n i (I  : {set 'I_m.+1}):
    #|pred_of_set I| == i  ->
                     \sum_(i0 in [finType of n.-tuple 'I_m.+1] | [set x in i0] \subset pred_of_set I)
                      BinNums.Zpos BinNums.xH = ((i %R) ^R^ n).
  Proof.
    move=> HI.
    rewrite rsum_pred_demote.
    under eq_bigr => a Ha do rewrite mulR1.
    elim: n => [| n IHn] //=.
    - {
        rewrite rsum_pred_demote rsum_empty //=.
        suff ->: ([set x in [tuple]] \subset pred_of_set I) = true; first by rewrite mulR1 //=.
        apply/eqP; rewrite eqb_id //=.
        rewrite unlock; apply/pred0P => x; rewrite !inE.
          by apply /Bool.negb_true_iff; rewrite Bool.negb_andb Bool.negb_involutive //= Bool.orb_true_r.
      }
    - {
        rewrite rsum_tuple_split rsum_split //=.
        have H (a : 'I_m.+1) (b : n.-tuple 'I_m.+1):
          [set x in [tuple of a :: b]] \subset pred_of_set I =
          (a \in I) && ([set x in b] \subset pred_of_set I);
          first by rewrite set_cons subUset sub1set //=.
        under eq_bigr => a _ do under eq_bigr => b _ do rewrite H boolR_distr.
        under eq_bigr => a _ do rewrite -rsum_Rmul_distr_l mulRC.
        rewrite -rsum_Rmul_distr_l //= mulRC.
        under eq_bigr => a _ do rewrite -(mulR1 ((a \in pred_of_set I) %R)).
        rewrite -rsum_pred_demote //=.
        rewrite bigsum_card_constE; move/eqP : (HI) => ->; rewrite mulR1; apply f_equal.
          by apply IHn.
      }

  Qed.



  Lemma not_in_subseq  m n (I  : {set 'I_m.+1}) (v: n.-tuple 'I_m.+1):
    ([set x in v] \subset I) ->
    ([set x in v] != I ) =
    (Ind (\bigcup_(i < #|I|) [set x : n.-tuple 'I_m.+1 | ((@enum_val _ (pred_of_set I) i) \notin x)]) v == Rdefinitions.R1).
  Proof.
    move=> Hsub; rewrite/Ind.
    case Hvin: (v \in _) => //=; try rewrite eq_refl.
    - {
        move/bigcupP: Hvin => [x' _ ] //=; rewrite in_set => Hnin.
        rewrite eqEsubset.
        rewrite Bool.negb_andb Hsub //=.
        rewrite unlock; apply/pred0Pn; exists (enum_val x'); rewrite inE //= ; apply/andP; split.
        - by rewrite in_set Hnin.
        - by apply enum_valP.
      }
    - {
        have ->: (Rdefinitions.R0 == Rdefinitions.R1) = false.
        case Heq: (Rdefinitions.R0 == Rdefinitions.R1) => //=.
          by move/eqP: Heq => Heq; move: Rstruct.R1_neq_0; rewrite eq_sym =>/Bool.negb_true_iff //=; rewrite Heq //= eq_refl //=.
          apply Bool.negb_true_iff; rewrite Bool.negb_involutive.
          move/Bool.negb_true_iff: Hvin => Hvin.
          rewrite -in_setC in Hvin.
          rewrite setC_bigcup in Hvin.
          move/bigcapP: Hvin => Hin.
          apply/eqP; apply/eqP.
          rewrite eqEsubset Hsub //=; rewrite unlock; apply/pred0P => x; rewrite !inE.
          case Hin': (x \in pred_of_set I);  rewrite ?Bool.andb_false_r ?Bool.andb_true_r //=.
          apply Bool.negb_true_iff; rewrite Bool.negb_involutive //=.
          move: (Hin (enum_rank_in Hin' x ) isT).
            by rewrite in_setC  enum_rankK_in //= in_set Bool.negb_involutive.
      }
  Qed.
  

  Lemma stirling_number_combinations (n i k: nat) (M: finType)
        (I:{set M}) (K: {set 'I_#|pred_of_set I| })
        (HpredI : #| I| == i)
        (HpredK : #|pred_of_set K| == k):
    \sum_(v : [finType of n.-tuple M] | [set x in v] \subset pred_of_set I)
     Ind (\bigcap_(j in  K) [set x : [finType of n.-tuple M] | enum_val j \notin x]) v = 
    (((i %R) -R- (k %R)) ^R^ n).
  Proof.

    elim: n => [| n IHn] //=.
    - {
        rewrite rsum_pred_demote rsum_empty //=.
        have ->: ([set x in [tuple]] \subset pred_of_set I) = true.
        {
          apply/eqP; rewrite eqb_id //=.
          rewrite unlock; apply/pred0P => x; rewrite !inE.
            by apply /Bool.negb_true_iff; rewrite Bool.negb_andb Bool.negb_involutive //= Bool.orb_true_r.
        }
        rewrite //= mul1R.
        suff ->: Ind
             (\bigcap_(j in pred_of_set K)
               [set x: 0.-tuple M | enum_val j \notin x])
             [tuple] = true;
          first by [].
        suff H: [tuple] \in \bigcap_(j in pred_of_set K) [set x : 0.-tuple M | enum_val j \notin x] = true;
          first by rewrite /Ind H //=. 
        apply/bigcapP => ind Hind //=.
          by rewrite in_set //=.
      }
    - {
        rewrite rsum_pred_demote rsum_tuple_split rsum_split //=.
        have H (a : M) (b : n.-tuple M):
          ([set x in cons_tuple a b] \subset pred_of_set I) =
          (a \in I) && ([set x in b] \subset pred_of_set I);
          first by rewrite set_cons subUset sub1set //=.

        under eq_bigr
        => a _ do under eq_bigr
        => b _ do rewrite H boolR_distr -mulRA; clear H.
        under eq_bigr => a _ do rewrite -rsum_Rmul_distr_l.
        rewrite -rsum_pred_demote //=.

        have H (N:finType) (A:{set N}) (a:N):
          Ind A a = (a \in A %R).
        {
          case Hpred: (a \in pred_of_set A) => //=.
          - by move/Ind_inP: Hpred ->.
          - by move/Ind_notinP: Hpred ->.
        }
        move: IHn; (under eq_bigr => v Hv do rewrite H); move=> IHn.

        under eq_bigr => a Ha.
        {
          rewrite -rsum_pred_demote //=.

          under eq_bigr => v Hv do rewrite H  //=.

            by over.

        }
        move=> //=; clear H.

        have H a v:
          (cons_tuple a v \in \bigcap_(j in pred_of_set K) [set x : n.+1.-tuple M  | enum_val j \notin x]) =
          (a \in \bigcap_(j in pred_of_set K) [set x | enum_val j != x])
            &&
            (v \in \bigcap_(j in pred_of_set K) [set x  | enum_val j \notin tval x]).
        {
          case Hcons: (cons_tuple _ _  \in _).
          {
            move/bigcapP:Hcons => Hcons.
              by apply Logic.eq_sym; apply/andP; split;
                apply/bigcapP => y Hy; move: (Hcons y Hy);
                                   rewrite !in_set in_cons Bool.negb_orb =>/andP [].
          }
          {
            move/Bool.negb_true_iff: Hcons.
            rewrite -in_setC setC_bigcap=>/bigcupP [y Hy].
            rewrite !in_set Bool.negb_involutive in_cons =>/orP Hor.
            apply Logic.eq_sym; apply Bool.negb_true_iff; rewrite Bool.negb_andb; apply/orP.
              by case: Hor => [Haeq| Hvin]; [left | right];
                                rewrite -in_setC setC_bigcap; apply/bigcupP;
                                  exists y => //=; rewrite !in_set Bool.negb_involutive.
          }
        }

        under eq_bigr => a Ha do under eq_bigr => v Hv do rewrite H boolR_distr; clear H.
        under eq_bigr => a Ha do rewrite rsum_pred_demote //=.
        under eq_bigr => a Ha do under eq_bigr => v Hv do rewrite  mulRC -!mulRA.
        under eq_bigr => a Ha do rewrite -rsum_Rmul_distr_l.
        rewrite -big_distrl //= mulRC.
        under eq_bigr => a Ha do rewrite mulRC.
        rewrite -rsum_pred_demote //= IHn [(_ -R- _ ) *R* _]mulRC; apply f_equal.


        rewrite rsum_pred_demote.
        under eq_bigr => a Ha do rewrite -boolR_distr -(mulR1 (pred_of_set I a && (a \in \bigcap_(j in pred_of_set K) [set x | enum_val j != x]) %R)).
        rewrite -rsum_pred_demote.
        move: (@bigID Rdefinitions.R Rdefinitions.R0 addR_comoid M (Finite.enum M)
                      (fun i0 => (i0 \in \bigcap_(j in pred_of_set K) [set x | enum_val j != x]))
                      (fun i0 => i0 \in pred_of_set I)
                      (fun _ => BinNums.Zpos BinNums.xH)
              ) => //= /subR_eq <-.

        rewrite bigsum_card_constE mulR1 //=; move/eqP: (HpredI) => {1}->.

        have H (j: 'I_(#|pred_of_set I|)): 
          ~: [set x | enum_val j != x] = [set enum_val j].
        {
          apply setP => x.
            by rewrite !in_set Bool.negb_involutive.
        }

        under eq_bigl => i0.
        {
          rewrite -in_setC //= setC_bigcap //=.
          under eq_bigr => j Hj do rewrite (H j) //=.
            by over.
        }
        clear H => //=.
        apply f_equal.

        clear -HpredK HpredI.

        have H i0: 
          (i0 \in pred_of_set I)
            && (i0 \in \bigcup_(j in pred_of_set K) [set enum_val j]) =
          (i0 \in \bigcup_(j in pred_of_set K) [set enum_val j]).
        {
          case Hin: (i0 \in \bigcup_(_ in _) _); rewrite ?Bool.andb_false_r ?Bool.andb_true_r //=.
          move/bigcupP:Hin => [y Hy]; rewrite in_set => /eqP ->.
            by apply enum_valP.
        }

        under eq_bigl => i0 do rewrite H; clear H => //=.


        have H (i0: M): (i0 \in \bigcup_(j in pred_of_set K) [set enum_val j]) =
                        (i0 \in [set (enum_val x) | x in K ]).
        {
          case Hin: (i0 \in [set (enum_val x) | x in _]).
          {
            apply/ bigcupP.
            move/imsetP: Hin => [im_i0 Him_i0 Hvld].
            exists im_i0 => //=.
              by rewrite in_set1 Hvld.
          }
          {
            apply/Bool.negb_true_iff; rewrite -in_setC setC_bigcup.
            apply/bigcapP => i1 Hi1; rewrite in_setC1.
            case Heq: (_ == _) => //=.
            have: (i0 \in [set enum_val x | x in pred_of_set K]).
            apply/imsetP; exists i1 => //=; move/eqP:Heq -> => //=.
              by rewrite Hin.
          }
        }
        under eq_bigl => i0 do rewrite H //=; clear H.
        rewrite bigsum_card_constE mulR1.
        rewrite card_in_imset; first by move/eqP:HpredK ->.
        move=> x y Hx Hy.
        apply enum_val_inj.

      }

  Qed.

  Theorem second_stirling_number_sum: forall l k m (f: nat -> Rdefinitions.R),
      (\sum_(inds in [finType of (l * k).-tuple 'I_m.+1])
        ((f (length (undup inds))))) =
      \sum_(i < (m + 2))
       (f(i) *R*
        (((Factorial.fact i %R) *R* (stirling_no_2 (l * k) i))) *R* ('C ((m.+1), i) %R)).
  Proof.

    move=> l k m f.

    rewrite (@partition_big
               _ _ _ _ _ _
               (fun (v: [finType of (l * k).-tuple 'I_m.+1]) => [set x | x \in tval v])
               (fun s => s \subset [set x |  nat_of_ord x < m + 1])
               (fun inds => f (length (undup inds)))
            ); first move => //=; last by apply vector_sum_subset.

    under eq_bigr => j Hj.
    {
      rewrite (@partition_big
                 _ _ _ _ _ _
                 (fun (v: [finType of (l * k).-tuple 'I_m.+1]) =>
                    Ordinal (undup_length_bound_ord v)
                 )
                 (fun m => true)
                 (fun inds => f (length (undup inds)))
              ) => //=;
        by over.
    }
    rewrite //= exchange_big //=.

    under eq_bigr => j Hj. {
      under eq_bigr => i Hi.
      {
        under eq_bigr => v /andP [Hset Hundup].
        {
          have: (length (undup v)) == j; first by move: Hundup => //=.
          move=>/eqP ->; rewrite -(mul1R (f j)).
            by over.
        }
        rewrite //= -big_distrl//=.
          by over.
      }
      rewrite //= -big_distrl //= mulRC.
        by over.
    }
    move=>//=.
    apply eq_bigr => i _; rewrite -mulRA; apply f_equal.

    have Hpred_eq (I : {set 'I_m.+1}) (v : (l * k).-tuple 'I_m.+1)
      : (([set x in v] == I) && (Ordinal (undup_length_bound_ord v) == i)) =
        (([set x in v] == I) && (#| I | == i)).
    {
      case HIeq: (_ == I) => //=.
      move/eqP: HIeq => <- //=.
      rewrite cardsE //=; have <-: nat_of_ord (Ordinal (undup_length_bound_ord v)) =  #|v|; last by move=>//=.
      rewrite cardE //= -length_sizeP.
      rewrite -(@undup_id _ (enum v)) //=; last by apply enum_uniq.
      apply /eqP; rewrite  eq_sym -(@uniq_size_uniq  _ (undup v) (undup (enum v))); try by apply undup_uniq.
        by move: (mem_enum (@mem _ _ v)) => Hmem v' //=; move: (Hmem v'); rewrite !mem_undup //=.
    }
    under eq_bigr => I HI do under eq_bigl => v do rewrite Hpred_eq.

    under eq_bigr => I Hi. {
      rewrite rsum_pred_demote.
      under eq_bigr => v Hv do rewrite andbC boolR_distr -!mulRA.
      rewrite -big_distrr //=.
        by over.
    }

    have H (I : {set 'I_m.+1}) : pred_of_set I \subset [set x | nat_of_ord x < m + 1].
    {
      rewrite unlock; apply/pred0P => x; rewrite !inE.    
      apply  Bool.negb_true_iff; apply /eqP; rewrite eqb_id Bool.negb_andb Bool.negb_involutive.
      apply/orP;left; rewrite addn1.
      apply ltn_ord.
    }
    under eq_bigl => I do rewrite H; move=>//=; clear H.
    rewrite -rsum_pred_demote //=.
    under eq_bigr => I Hi do rewrite -rsum_pred_demote //=.

    apply sum_partition_combinations => I Hi.
    rewrite /stirling_no_2; rewrite mulRA.
    have->: ((Factorial.fact i %R) *R* Rdefinitions.Rinv (Factorial.fact i)) = 1; last rewrite mul1R.
    {
        by rewrite RIneq.INR_IZR_INZ mulRV //=; apply/eqP;
          rewrite -!RIneq.INR_IZR_INZ; apply RIneq.not_0_INR; apply (Factorial.fact_neq_0 i).
    }

    
    (* Stirlings number proof - step 2 *)
    have H (v: (l * k).-tuple 'I_m.+1): 
      [set x in v] == I = (([set x in v] \subset I) && ([set x in v] == I)).

    {
      case Heq: (_ == _); last by rewrite Bool.andb_false_r.
      apply Logic.eq_sym; rewrite Bool.andb_true_r.
        by move/eqP:Heq ->; apply/eqP; rewrite eqb_id //=.
    }

    under eq_bigl => v do rewrite H; clear H.
    move: (@bigID
             Rdefinitions.R (Rdefinitions.R0)
             addR_comoid
             [finType of (l * k).-tuple 'I_m.+1]
             (index_enum [finType of (l * k).-tuple 'I_m.+1])
             (fun v => [set x in v] == I)
             (fun v => [set x in v] \subset pred_of_set I)
             (fun a => BinNums.Zpos BinNums.xH )) => //=.
    move=>/RIneq.Rminus_diag_eq //=; rewrite addRC subRD; move=>/RIneq.Rminus_diag_uniq <- //=.
    rewrite (@subset_combinations m (l * k) i I Hi).

    have H (v: (l * k).-tuple 'I_m.+1):
      ([set x in v] \subset pred_of_set I) && ([set x in v] != I) =
      ([set x in v] \subset pred_of_set I)
        &&
        (Ind (\bigcup_(i0 < #|pred_of_set I|) [set x | enum_val i0 \notin tval x]) v == Rdefinitions.R1).
    {
      case Hsubs: (_ \subset _) => //=.
      rewrite not_in_subseq //=. 
    }

    under eq_bigl => v do rewrite H; clear H.

    have H p1 p2: (Ind p1 p2 == Rdefinitions.R1 %R) = Ind p1 p2.
    {
      rewrite/Ind.      
      case: (_ \in _) => //=; rewrite ?eq_refl //=.

      have ->: (Rdefinitions.R0 == Rdefinitions.R1) = false.
      {
        case Heq: (Rdefinitions.R0 == Rdefinitions.R1) => //=.
          by move/eqP: Heq => Heq; move: Rstruct.R1_neq_0; rewrite eq_sym =>/Bool.negb_true_iff //=; rewrite Heq //= eq_refl //=.
      }
        by [].
    }

    rewrite rsum_pred_demote; under eq_bigr => v Hv do rewrite boolR_distr -mulRA mulR1; rewrite -rsum_pred_demote //=.

    under eq_bigr => v Hv do rewrite H; clear H.

    have H j:
      (BinNums.Zneg BinNums.xH ^R^ j - 1) = (Rdefinitions.Ropp (BinNums.Zpos BinNums.xH) ^R^ (j - 1)).
    {
        by apply f_equal => //=.
    }
    under eq_bigr => v Hv.
    {
      rewrite Ind_bigcup_incl_excl.
      move/eqP: Hi => Hi.
      rewrite {1}Hi.
      under eq_bigr => j Hj do rewrite H subn1.
        by over.
    }
    rewrite exchange_big //=.

    under eq_bigr => j Hj.
    {
      rewrite rsum_pred_demote.
      under eq_bigr => a Ha do rewrite mulRC -!mulRA.
      rewrite -rsum_Rmul_distr_l.
      under eq_bigr => a Ha do rewrite mulRC.
      rewrite -rsum_pred_demote //=.
        by over.      
    }
    under eq_bigr => v Hv do rewrite exchange_big //=.
    rewrite -addR_opp.
    rewrite big_morph_oppR.
    under eq_bigr => v Hv do rewrite RIneq.Ropp_mult_distr_l //=.

    move=> //=.

    under eq_bigr => v Hv.
    {
      rewrite (@sum_partition_combinations _ _ _ (((i %R) -R- (v %R)) ^R^ l * k)).
        by over.
        move=> I0 HI0.
          by move: (@stirling_number_combinations (l * k) i v [finType of 'I_m.+1] I I0 Hi HI0).
    }

    move=> //=; clear H.

    have H v: v > 0 -> Rdefinitions.Ropp (Rdefinitions.Ropp (BinNums.Zpos BinNums.xH) ^R^ v.-1) =
                       (Rdefinitions.Ropp (BinNums.Zpos BinNums.xH) ^R^ v).
    {
      clear; elim: v => [| [|v] IHv] //=; first by move=> _; rewrite mulR1.
      move=> Hv.
      rewrite RIneq.Ropp_mult_distr_l RIneq.Ropp_involutive mul1R.
      rewrite mulRA.
        by rewrite -RIneq.Ropp_mult_distr_r RIneq.Ropp_mult_distr_l  RIneq.Ropp_involutive mul1R mul1R.
    }

    under eq_big_nat => v /andP [H1 H2] do rewrite (H v H1).



    have Hov: (1 <= i.+1); first by [].
    move: (@big_nat_recl
             Rdefinitions.R
             Rdefinitions.R0
             addR_comoid i 0
             (fun v =>
                ((Rdefinitions.Ropp (BinNums.Zpos BinNums.xH) ^R^ v) *R*
                 ((((i %R) -R- (v %R)) ^R^ l * k) *R* ('C(#|pred_of_set I|, v) %R)))
             )
             Hov
          ) => //=.

    rewrite subR0 mul1R bin0 mulR1.
    have: \sum_(0 <= i0 < i)
           ((Rdefinitions.Ropp (BinNums.Zpos BinNums.xH) ^R^ i0.+1) *R*
            ((((i %R) -R- (i0.+1 %R)) ^R^ l * k) *R* ('C(#|pred_of_set I|, i0.+1) %R))) =
          \sum_(1 <= i0 < i.+1)
           ((Rdefinitions.Ropp (BinNums.Zpos BinNums.xH) ^R^ i0) *R*
            ((((i %R) -R- (i0 %R)) ^R^ l * k) *R* ('C(#|pred_of_set I|, i0) %R))).
    {
      
      rewrite -(@big_map
                  Rdefinitions.R Rdefinitions.R0 addR_comoid
                  _ _ (fun x => x.+1) (index_iota 0 i) (fun _ => true)
                  (fun i0 =>
                     ((Rdefinitions.Ropp (BinNums.Zpos BinNums.xH) ^R^ i0) *R*
                      ((((i %R) -R- (i0 %R)) ^R^ l * k) *R* ('C(#|pred_of_set I|, i0) %R)))
                  )
               ).
        by rewrite  index_iota_incr.
    }
    move=> //= -> <-.
    rewrite big_mkord.
      by apply eq_bigr => y Hy //=; move/eqP:Hi =>->; rewrite -!mulRA; apply f_equal; rewrite mulRC.
  Qed.


  Lemma second_stirling_number_sum_normalized: forall l k m (f: nat -> Rdefinitions.R),
      (\sum_(inds in [finType of (l * k).-tuple 'I_m.+1])
        ((Rdefinitions.Rinv (m.+1 %R) ^R^ l * k) *R*
         (f (length (undup inds)))) ) =
      \sum_(len in [finType of 'I_(m.+2)])
       (f(len) *R*
        ( ('C ((m.+1), len) %R) *R*
          (Factorial.fact len %R) *R* (stirling_no_2 (l * k) len) *R*
          (Rdefinitions.Rinv (m.+1 %R) ^R^ (l * k))
       )).
  Proof.
    move=> l k m f.
    rewrite -rsum_Rmul_distr_l.
    under [\sum_(len in [finType of 'I_m.+2]) _]eq_bigr => inds Hinds do rewrite mulRA mulRC -!mulRA.  
    rewrite -rsum_Rmul_distr_l; apply f_equal.
    rewrite second_stirling_number_sum addn2.
    apply eq_bigr => ind Hind.
      by rewrite -mulRA; apply f_equal; rewrite mulRC.
  Qed.


  About second_stirling_number_sum.
  

End stirling_second_number.
