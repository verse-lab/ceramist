From mathcomp.ssreflect Require Import
     ssreflect ssrbool ssrnat eqtype fintype choice
     ssrfun seq path bigop finfun.

From mathcomp.ssreflect Require Import tuple.

From mathcomp Require Import path.

From infotheo Require Import
      fdist ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

From ProbHash.Computation
     Require Import Comp Notationv1.

From ProbHash.Core
     Require Import Hash FixedList FixedMap.

From ProbHash.Utils
     Require Import InvMisc  seq_ext seq_subset rsum_ext.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Module HashVec (Spec: HashSpec).
  Module Hash := (Hash Spec).

  Export Hash.

  Section HashVec.
  (*
    k - number of hashes
   *)
  Variable k: nat.
  (*
    n - maximum number of hashes supported
   *)
  Variable n: nat.
  Variable Hkgt0: k >0.

  Definition hash_not_full (hsh: HashState n) : bool :=
    FixedList.fixlist_length hsh < n.

  Definition hash_unseen (b: B) (hsh: HashState n) : bool :=
    FixedMap.fixmap_find b hsh == None.

  Definition hash_has_free_spaces (s: nat) (hsh: HashState n) : bool :=
    FixedList.fixlist_length hsh + s <= n.

  Definition hashes_not_full (hashes: k.-tuple (HashState n)) : bool :=
    (* provided the finite maps of all the hash function are not full*)
    all hash_not_full (tval hashes).

  Definition hashes_value_unseen  (hashes: k.-tuple (HashState n))  (b: B) : bool :=
    (* provided the finite maps of all the hash function have not seen the value*)
    all (hash_unseen b) (tval hashes).

  Definition hashes_have_free_spaces  (hashes: k.-tuple (HashState n)) (s: nat) : bool :=
    all (hash_has_free_spaces s) (tval hashes).
  
  
  Lemma Hpredkvld: k.-1 < k.
  Proof.
       apply InvMisc.ltnn_subS.
       apply Hkgt0.
  Qed.

  Lemma Hltn_leq pos pos' (Hpos: pos < k) (Hpos': pos = pos'.+1) : pos' < k.
      by  move: (Hpos); rewrite {1}Hpos' -{1}(addn1 pos') => /InvMisc.addr_ltn .
  Qed.  

  Definition trcons A n (xs: n.-tuple A) (x: A) : (n.+1.-tuple A) :=
    match xs as t return (_ <- t; (n.+1).-tuple A) with
    | @Tuple _ _ x0 x1 =>
      (fun (xs0 : seq A) (Hsz : size xs0 == n) =>
         (Hmap <- (fun Hsz0 : size (xs0 <::< x) = n.+1 =>
                    Hrxs <- introT eqP Hsz0; Tuple Hrxs);
            eq_rect_r (fun n' : nat => size (xs0 <::< x) = n'.+1 -> (n.+1).-tuple A)
                      Hmap (elimTF eqP Hsz))
           (size_rcons xs0 x))
        x0 x1
    end.

  (* Helper lemma to perform typecast
  there's got to be a better way to do this... *)
  Lemma hash_vec_int_cast (h h' : nat) A (Hh: h = h'.+1)
        (tuple: h.-tuple A) : (h'.+1).-tuple A.
  Proof.
    move: tuple => [tval Htval]; split with tval.
      by rewrite -Hh.
  Defined.
  
  Fixpoint hash_vec_int (h: nat) (value: hash_keytype)
           (hashes:  h.-tuple (HashState n))  :
    Comp [finType of (h.-tuple (HashState n) * (h.-tuple 'I_(Hash_size.+1)))]
    :=
      (match h as h' return
             (h = h' -> h'.-tuple (HashState n) ->
              Comp [finType of (h'.-tuple (HashState n) * (h'.-tuple 'I_(Hash_size.+1)))]) with
       | 0 => (fun (Hh: h = 0) (hashes': 0.-tuple (HashState n)) =>
                ret ([tuple of [::]], [tuple of [::]]))
       | h'.+1 => (fun (Hh: h = h'.+1) (sub_hashes': (h'.+1).-tuple (HashState n)) =>
                    (* hash the remaining h' elements *)
                    remain <-$ @hash_vec_int h' value (ntuple_tail  sub_hashes');
                      let (hashes', values') := remain in        
                      (* then hash the current element *)
                      let hsh_fun := thead sub_hashes' in 
                      hash_vl <-$ hash _ value hsh_fun;
                        (* retrieve the  *)
                        let (new_hsh_fun, result) := hash_vl in  
                        ret ([tuple of new_hsh_fun :: hashes'], [tuple of result :: values'])
                 ) 
       end   
      ) (erefl h) hashes .

  End HashVec.


Open Scope R_scope.

Lemma hash_vec_insert_length n l (value: hash_keytype)
      (hashes: l.-tuple (HashState n)) (inds: l.-tuple 'I_Hash_size.+1):
  size (map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
               let (hash,ind) := pair in @hashstate_put _ value ind hash)
            (zip (tval hashes) (tval inds))) == l.
Proof.
    by rewrite size_map size_zip !size_tuple /minn ltnn //=.
Qed.

Lemma hash_vec_insert_length_consP n l (value: hash_keytype)
      (hashes: seq (HashState n)) (hash: HashState n)
      (Hhashes: size (hash :: hashes) == l.+1) (inds: seq 'I_Hash_size.+1)
      (ind: 'I_Hash_size.+1) (Hind: size (ind :: inds) == l.+1) :
  Tuple (hash_vec_insert_length value (Tuple Hhashes) (Tuple Hind)) =
  cons_tuple
    (@hashstate_put _ value ind hash) 
    (Tuple (hash_vec_insert_length value (Tuple (cons_sizeP  Hhashes))
                                   (Tuple (cons_sizeP Hind)))).
Proof.
  move: (cons_sizeP  _ ) => //= Hhashes'.
  move: (cons_sizeP  _) => //= Hinds'.
  move: (hash_vec_insert_length _ _ _) => Hinsert'.
  move: (Hinsert') => Hinsert; move: Hinsert'.
  have->:
      (map
         (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
            let (hash,ind) := pair in @hashstate_put _ value ind hash)
         (zip (Tuple Hhashes) (Tuple Hind))) = 
  (hashstate_put n value ind hash) :: (map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                                             let (hash,ind) := pair in
                                             @hashstate_put _ value ind hash)
                                          (zip (Tuple Hhashes') (Tuple Hinds'))); first by [].
  move: Hinsert =>  H1 H2.
  rewrite (proof_irrelevance _ H1 H2); clear H1.
  erewrite tuple_eta; case Heq: [tuple of _ :: _] => [[//=| x xs] Hxs].
  move: Heq; rewrite theadE.
  have: behead_tuple
          (cons_tuple (hashstate_put n value ind hash)
                      (Tuple (hash_vec_insert_length value (Tuple Hhashes')
                                                     (Tuple Hinds')))) =
        (Tuple (hash_vec_insert_length value (Tuple Hhashes') (Tuple Hinds'))).
  {
    rewrite /behead_tuple;
      move:  (hash_vec_insert_length _ _ _) (behead_tupleP _ ) => //= H3 H4.
      by rewrite (proof_irrelevance _ H3 H4). 
  }
  move=>-> [Heqx Heqxs].
  move: Hxs H2; rewrite Heqx Heqxs => //= Ha Hb.
    by rewrite (proof_irrelevance _ Ha Hb).
Qed.

Definition hash_vec_contains_value n l (value: hash_keytype)
           (hashes: l.-tuple (HashState n)) (inds: l.-tuple 'I_Hash_size.+1) : bool :=
  all (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
         let (hash,ind) := pair in @hashstate_find _ value hash == Some ind)
      (zip (tval hashes) (tval inds)).

Lemma hash_vec_contains_value_preserve n l (value value': hash_keytype)
      (hashes: l.-tuple (HashState n)) (inds inds': l.-tuple 'I_Hash_size.+1) :
  value != value' ->
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
            by rewrite ntuple_head_consE eq_refl.
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
              rewrite ntuple_head_consE Hkeq.
              rewrite ntuple_tail_consE.
                by move=> Hneq Hfind; apply IHn => //=.
            }
        }
    }
Qed.    

Lemma hash_vec_contains_value_base n l (value: hash_keytype)
      (hashes: l.-tuple (HashState n)) (inds : l.-tuple 'I_Hash_size.+1) : 
  all (fun hsh => FixedList.fixlist_length hsh + 1 <= n) hashes ->
  hash_vec_contains_value
    value (Tuple (hash_vec_insert_length value hashes inds)) inds.
Proof.
  elim: l  hashes inds => [|l IHl]  hashes inds //=.
    by rewrite !tuple0/hash_vec_contains_value //= !zip_empty_r //=.
    move=> /allP Hhashes.
    have H1: all
               (fun hsh : FixedList.fixlist [eqType of hash_keytype * hash_valuetype] n =>
                  FixedList.fixlist_length hsh + 1 <= n) (behead_tuple hashes).
    {
      apply/allP => ind Hind; apply Hhashes => //=.
        by move: Hind;
          rewrite (tuple_eta hashes) //= in_cons => ->; rewrite Bool.orb_true_r //=.
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
              rewrite /FixedList.ntuple_head //= ntuple_head_consE Hkeq.
              rewrite ntuple_tail_consE => Hlen.
                by apply IHn => //=.
            }
        }
      - {
            by rewrite eq_refl.
        }
    }
Qed.

Lemma hash_vecP n l (value: hash_keytype) (hashes: l.-tuple (HashState n))
      (inds: l.-tuple 'I_Hash_size.+1)
      (Huns: all (fun hsh => FixedMap.fixmap_find value hsh == None) hashes) :
  d[ hash_vec_int value hashes ]
   (Tuple (hash_vec_insert_length value hashes inds), inds) =
  ((Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l).
Proof.
  elim: l value hashes inds Huns => [//=| l IHl].
  - by move=> value [[|//=] Hlen] [[|//=] Hinds]; rewrite FDist1.dE //=.
  - move=> //= value [[//=| x xs] Hxs] [[//=| y ys] Hys] Huns; rewrite FDistBind.dE.   
    erewrite <- (IHl value (FixedList.ntuple_tail (Tuple Hxs))).
    rewrite /FixedList.ntuple_tail; move: (behead_tupleP _) => //= Hlen.
    transitivity (
        \sum_(hshs in [finType of l.-tuple (HashState n)])
         \sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
         \sum_(hsh in hashstate_of_finType n)
         \sum_(ind in ordinal_finType Hash_size.+1)
         ((d[ hash_vec_int value (Tuple Hlen)]) (hshs, inds) *R*
          ((d[ hash n value (thead (Tuple Hxs))]) (hsh, ind) *R*
           ([&& (hsh == hashstate_put n value y x ) &&
                (hshs == Tuple (hash_vec_insert_length value
                                                       (Tuple (cons_sizeP Hxs))
                                                       (Tuple (cons_sizeP Hys)))),
             ind == y
             & inds == Tuple (cons_sizeP Hys)] %R)
         ))
      ).
    rewrite rsum_split.
    apply eq_bigr => hshs _; apply eq_bigr => inds _ //=; rewrite FDistBind.dE //=.
    rewrite mulRC rsum_Rmul_distr_r rsum_split.
    apply eq_bigr => hsh _; apply eq_bigr => ind _ //=.
    apply f_equal; apply f_equal => //=; rewrite FDist1.dE.
    rewrite xpair_eqE.
    rewrite hash_vec_insert_length_consP.
    rewrite !xcons_eqE.
    have: (Tuple Hys = cons_tuple y (Tuple (cons_sizeP Hys))).
    rewrite (tuple_eta (cons_tuple _ _)) //= theadE;
      case Heq: [tuple of _] => [[//=| y' ys'] Hys'].
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
        have H x1 y1 z1 : (y1 = (0 %R)) -> x1 = z1 -> x1 +R+ y1 = z1.
          by move=> -> ->; rewrite addR0.
          transitivity (
              \sum_(hshs in [finType of l.-tuple (HashState n)])
               \sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
               ((d[ hash_vec_int value (Tuple Hlen)]) (hshs, inds) *R*
                ((d[ hash n value (thead (Tuple Hxs))])
                   (hashstate_put n value y x, y) *R*
                 ([&& (hshs == Tuple (hash_vec_insert_length
                                        value
                                        (Tuple (cons_sizeP Hxs))
                                        (Tuple (cons_sizeP Hys))) ) &
                   inds == Tuple (cons_sizeP Hys)] %R)))
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
            ((d[ hash_vec_int value (Tuple Hlen)])
               (Tuple (hash_vec_insert_length
                         value
                         (Tuple (cons_sizeP Hxs))
                         (Tuple (cons_sizeP Hys))), Tuple (cons_sizeP Hys)) *R*
             ((d[ hash n value (thead (Tuple Hxs))])
                (hashstate_put n value y x, y)))
          ).
        rewrite (bigID (fun hshs =>
                          hshs == Tuple (hash_vec_insert_length
                                           value
                                           (Tuple (cons_sizeP Hxs))
                                           (Tuple (cons_sizeP Hys)))))
                big_pred1_eq eq_refl //=.
        apply H.
  - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
    apply prsumr_eq0P => ind' Hind'; first by dispatch_Rgt.
      by rewrite //= !mulR0.
      rewrite (bigID (fun inds => inds == Tuple (cons_sizeP Hys))) big_pred1_eq eq_refl //=.
      apply H.
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
        move=>->; rewrite /hash/hashstate_find Hx //= FDistBind.dE.
        apply Logic.eq_sym.
        transitivity (
            \sum_(a in [finType of 'I_Hash_size.+1])
             (\sum_(a0 in ordinal_finType Hash_size.+1)
               ((Uniform.d (size_enum_equiv (size_enum_ord Hash_size.+1))) a0 *R* (FDist1.d a0) a) *R*
              ((hashstate_put n value y x == hashstate_put n value a x) && (a == y) %R))
          ).
        apply eq_bigr => a _.
          by rewrite FDistBind.dE FDist1.dE xpair_eqE (eq_sym y).
          rewrite (bigID (fun a => a == y)) big_pred1_eq eq_refl //=.   
          apply H.
  - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first (by dispatch_Rgt; dispatch_Rgt).
      by rewrite Bool.andb_false_r //= mulR0.
      rewrite eq_refl //= mulR1. 
      transitivity (
          \sum_(a0 in 'I_Hash_size.+1)
           ((Uniform.d (size_enum_equiv (size_enum_ord Hash_size.+1))) a0 *R* (a0 == y %R))
        ).
        by apply eq_bigr => a' _; rewrite FDist1.dE eq_sym.
        rewrite (bigID (fun a0 => a0 == y)) big_pred1_eq //= eq_refl mulR1 //=.
        apply H.
  - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by dispatch_Rgt.
      by rewrite mulR0.
        by rewrite Uniform.dE card_ord.
        rewrite /FixedList.ntuple_tail //=.
          by move: Huns => //= =>/andP [].
Qed.

Lemma neg_hash_vecP n l (value: hash_keytype) (hashes hashes': l.-tuple (HashState n))
      (inds: l.-tuple 'I_Hash_size.+1)
      (Huns: all (fun hsh => FixedMap.fixmap_find value hsh == None) hashes) :
  (tval hashes' != map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
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
  - move=> //= value [[//=| x xs] Hxs] [[//=| y ys] Hys] [[//=| z zs] Hzs] /allP Huns;
            rewrite FDistBind.dE //=.   
    rewrite negb_consP =>/orP [Hyneq | Hysneq].
    transitivity (  
        \sum_(hshs' in tuple_finType l (hashstate_of_finType n))
         \sum_(bf' in tuple_finType l (ordinal_finType Hash_size.+1))
         (
           (d[ hash_vec_int value (FixedList.ntuple_tail (Tuple Hxs))]) (hshs', bf') *R* 
           (
             \sum_(hshs'' in hashstate_of_finType n)
              \sum_(ind' in ordinal_finType Hash_size.+1)
              \sum_(ind'' in [finType of 'I_Hash_size.+1])
              (0%R)
           )
      )).
  - rewrite rsum_split; apply eq_bigr => hshs' _; apply eq_bigr => bf' _ //=.
    have: (thead (Tuple Hxs)) = x; last move=> ->; first by [].
    apply f_equal; rewrite FDistBind.dE rsum_split.
    apply eq_bigr => hshs'' _; apply eq_bigr => ind' _ //=.
    rewrite /hash/hashstate_find FDist1.dE.
    case Hteq: ((_,_) == _); last by rewrite bigsum_card_constE //= !mulR0.
    move/eqP: Hteq => [<- _ <- _ ] //=; rewrite mulR1.
    have Hin: (x \in Tuple Hxs); first by rewrite (tuple_eta (Tuple Hxs)) //= in_cons; apply/orP;left. 
    move/eqP: (Huns x Hin) -> => //=; rewrite FDistBind.dE.
    apply eq_bigr => ind'' _; rewrite FDist1.dE xpair_eqE.
    case Hz: (z == ind''); last by rewrite Bool.andb_false_r //= mulR0.
      by move/eqP: Hz <-; move/Bool.negb_true_iff: Hyneq -> => //=; rewrite mulR0.  
        by do ? [
                (apply prsumr_eq0P; intros; first by dispatch_Rgt; intros; dispatch_Rgt)|
                (apply RIneq.Rmult_eq_0_compat_l)
              ].
        apply prsumr_eq0P => [[hshs' bf']|]; first by intros; dispatch_Rgt.
        move=> [hshs' bf'] _; case Heq: (tval hshs' == ys); last first.
  - apply RIneq.Rmult_eq_0_compat_l => //=; rewrite FDistBind.dE.
    apply prsumr_eq0P => [[hshs'' ind']|[hshs'' ind']] _; first by dispatch_Rgt.
    rewrite //= FDist1.dE xpair_eqE //=; apply RIneq.Rmult_eq_0_compat_l => //=.
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
  - apply RIneq.Rmult_eq_0_compat_l => //=; rewrite FDistBind.dE.
    apply prsumr_eq0P => [[hshs'' ind']|[hshs'' ind']] _; first by dispatch_Rgt.
    rewrite //= FDist1.dE xpair_eqE //=; apply RIneq.Rmult_eq_0_compat_l => //=.
    suff: (Tuple Hzs == [tuple of ind' :: bf']) = false; first by move => ->; rewrite Bool.andb_false_r //=.
    rewrite (tuple_eta (Tuple Hzs)).
    have: (thead (Tuple Hzs)) = z; last move=> -> //=; first by  [].
      by rewrite tuple_eq_inj eqseq_cons [zs == _]eq_sym Hbfeq Bool.andb_false_r.
      apply RIneq.Rmult_eq_0_compat_r; apply IHl;move/eqP:Heq=>Heq;move/eqP:Hbfeq=>Hbfeq; rewrite ?Heq ?Hbfeq //=.
      clear IHl.
        by apply/allP => x' Hx'; apply Huns=> //=; rewrite in_cons;apply/orP;right.
Qed.

Lemma hash_vec_simpl (n' k': nat) (hashes: k'.-tuple (HashState n')) value inds f :
  all (fun hsh : FixedMap.fixmap hash_keytype hash_valuetype n' =>
         FixedMap.fixmap_find value hsh == None) hashes ->
  (\sum_(hshs' in [finType of k'.-tuple (HashState n')])
    ((d[ hash_vec_int value hashes]) (hshs', inds) *R* (f hshs'))) =
  ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k') *R*
   (f (Tuple (hash_vec_insert_length value hashes inds)))).
Proof.
  move=> Hall.
  rewrite (bigID (fun hshs' => hshs' == (Tuple (hash_vec_insert_length value hashes inds)))) big_pred1_eq//=.
  under eq_bigr => i Hneq do rewrite neg_hash_vecP ?mul0R //=.
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
  - by do ?(case; case => //=; intro); move=> _ //=; rewrite FDist1.dE xpair_eqE //= !tuple0 //=.
  - move=> [[//=| hash hashes] Hhashes]
            [[//=| ind inds] Hinds]
            [[//=| hash' hashes'] Hhashes']
            [[//=|ind' inds'] Hinds'] //=.
    rewrite FDistBind.dE rsum_split //=.
    have H1: (thead (Tuple Hhashes)) = hash; first by [].
    under eq_bigr => a _ do under eq_bigr => b _ do rewrite H1.
    move: (IHl (FixedList.ntuple_tail (Tuple Hhashes))
               (FixedList.ntuple_tail (Tuple Hinds))) => IHl' /allP Hcontains.
    under eq_bigr => a H3. under eq_bigr => b H4.
    rewrite IHl' ?boolR_distr -?mulRA. by over.
    {
      apply/allP => [[hsh_tail ind_tail]] //= Hin.
      have Hin': (hsh_tail, ind_tail) \in zip (Tuple Hhashes) (Tuple Hinds); first by rewrite//= in_cons Hin Bool.orb_true_r.
        by move: (Hcontains (hsh_tail, ind_tail) Hin').
    }
    move => //=; by over.
    {
      rewrite exchange_big; under eq_bigr => b _ do rewrite -rsum_pred_demote big_pred1_eq.
      rewrite -rsum_pred_demote big_pred1_eq //=.
      rewrite FDistBind.dE rsum_split //=.
      under eq_bigr => a _ do under eq_bigr => b _ do rewrite FDist1.dE xpair_eqE//=.
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
      under eq_bigr => a _ do under eq_bigr => b _ do rewrite Heq !boolR_distr mulRC -!mulRA.
      rewrite exchange_big; under eq_bigr => a _ do rewrite -rsum_pred_demote big_pred1_eq.
      rewrite -rsum_pred_demote big_pred1_eq //=.
      rewrite/Hash.hash //=.
      have ->: (Tuple Hhashes' == Tuple Hhashes) && (Tuple Hinds' == Tuple Hinds) =
      (hash == hash') && (ind == ind') &&
                      (FixedList.ntuple_tail (Tuple Hhashes') == FixedList.ntuple_tail (Tuple Hhashes)) &&
                      (FixedList.ntuple_tail (Tuple Hinds') == FixedList.ntuple_tail (Tuple Hinds)).
      {
        rewrite (tuple_eta (Tuple Hhashes'))
                (tuple_eta (Tuple Hhashes))
                (tuple_eta (Tuple Hinds))
                (tuple_eta (Tuple Hinds'))  //=.
        rewrite !ntuple_tailE //=.
        have -> : (thead (Tuple Hhashes')) = hash'; first by [].
        have -> : (thead (Tuple Hhashes)) = hash; first by [].
        have -> : (thead (Tuple Hinds')) = ind'; first by [].
        have -> : (thead (Tuple Hinds)) = ind; first by [].
        apply Logic.eq_sym.
        transitivity (
            ((hash' == hash)
               && (behead_tuple (Tuple Hhashes') ==
                   behead_tuple (Tuple Hhashes)))
              && ((ind' == ind)
                    && (behead_tuple (Tuple Hinds') == behead_tuple (Tuple Hinds)))
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
        by move: (Hcontains (hash,ind) Hin) =>/eqP -> //=; rewrite FDist1.dE eq_sym xpair_eqE boolR_distr //=.
        
    }

Qed.

Lemma hash_vec_int_id' (n' k': nat) (hashes: k'.-tuple (HashState n')) value inds ps :
  all (fun y => FixedList.fixlist_length y + 1 <= n') hashes ->
  (d[ hash_vec_int  value (Tuple (hash_vec_insert_length value hashes inds))])
    (ps, inds) = (ps == (Tuple (hash_vec_insert_length value hashes inds)) %R).
Proof.
  move: (hash_vec_insert_length _ _ _) => //=.
  elim: k' n'  inds hashes ps => [//=|k' IHk'] n' [[//=| x xs] Hxs] [[//=|y ys] Hys] ps Hprf Hprf'' //=.
  move: Hprf => //= H0; rewrite FDist1.dE xpair_eqE //=.
  apply Logic.eq_sym; case Heq: (_ == _) => //=.
    by move/eqP: Heq ->; case: ps => //= [//= []] //=; rewrite tuple0 //=.
      by case: ps Heq  => //= [//= []] //= Hprf.
      case: ps => //= [//=[]]; (try by []); move=>  p ps Hps.
      rewrite /FixedList.ntuple_tail.
      move: (behead_tupleP _ ) => //= Hprf'.
      rewrite FDistBind.dE.
      rewrite rsum_split //=; under eq_bigr => a _ do under eq_bigr => b _ do rewrite FDistBind.dE.
      under eq_bigr => a _ do under eq_bigr => b _ do rewrite rsum_split //=.
      under eq_bigr => a _ do under eq_bigr => b _ do under eq_bigr => c _ do under eq_bigr => d _ do rewrite FDist1.dE xpair_eqE //=.
      have Hsusp1 (c: HashState n') (a: k'.-tuple (HashState n')) : ( (Tuple Hps) ==  [tuple of c :: a]) = ((p == c) && (ps == a)).
        by rewrite/[tuple of _] //=.
        have Hsusp2 (d: 'I_Hash_size.+1) (b: k'.-tuple 'I_Hash_size.+1) : ( (Tuple Hxs) ==  [tuple of d :: b]) = ((x == d) && (xs == b)).
          by rewrite/[tuple of _] //=.
          under eq_bigr => a _ do under eq_bigr => b _ do under eq_bigr => c _ do under eq_bigr => d _ do rewrite Hsusp1 Hsusp2 !boolR_distr eq_sym mulRC -mulRA -mulRA -mulRA.
          under eq_bigr => a _ do under eq_bigr => b _ do rewrite exchange_big.
          under eq_bigr => a _ do under eq_bigr => b _ do under eq_bigr => c _ do rewrite -rsum_pred_demote big_pred1_eq //=.
          under eq_bigr => b _ do under eq_bigr => c _ do under eq_bigr => d _ do rewrite mulRC eq_sym -mulRA.
          under eq_bigr => b _ do under eq_bigr => c _ do rewrite -rsum_pred_demote big_pred1_eq.
          under eq_bigr => b _ do under eq_bigr => c _ do rewrite mulRC -mulRA -mulRA eq_sym.
          have H (c: k'.-tuple 'I_Hash_size.+1): (tval c == xs) = (c == (behead_tuple (Tuple Hxs))).
            by rewrite/behead_tuple //=.
            (under eq_bigr => b _ do under eq_bigr => c _ do rewrite H); clear H.
            under eq_bigr => b _ do rewrite -rsum_pred_demote big_pred1_eq//=.
            have H (b: k'.-tuple (HashState n')): (tval b == ps) = (b == (behead_tuple (Tuple Hps))).
              by rewrite/behead_tuple //=.
              under eq_bigr => b _ do rewrite mulRC -mulRA  eq_sym H.
              rewrite -rsum_pred_demote big_pred1_eq.
              move: (IHk' n' (behead_tuple (Tuple Hxs)) (behead_tuple (Tuple Hys)) (behead_tuple (Tuple Hps))) =>//=.
              move=> /(_ Hprf') -> //=; clear IHk'.
              rewrite /hash //=.
              have ->: ((thead (Tuple Hprf)) = (hashstate_put n' value x y)); first by move=>//=.
              rewrite hash_find_insert_involutive //= ?FDist1.dE ?xpair_eqE ?eq_refl //=.
              rewrite ?Bool.andb_true_r.
              have ->: ((Tuple Hps == Tuple Hprf) = ((thead (Tuple Hps)== thead (Tuple Hprf))
                                                       && (behead_tuple (Tuple Hps) == (Tuple Hprf'))));
                move=>//=.
                by rewrite !boolR_distr;apply Logic.eq_sym; rewrite mulRC; apply f_equal => //=.
                  by move: Hprf'' => //= /andP [] //=.
                    by move: Hprf'' => //= /andP [] //=.
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
    move: Hprf => //= H0; rewrite FDist1.dE xpair_eqE //=.
    apply Logic.eq_sym; case Heq: (_ == _) => //=.
      by move: Hxs Hprf''' => //=; rewrite !tuple0 => Hxs //=.
      case: ps => //= [//=[]]; (try by []); move=>  p ps Hps.
      rewrite /FixedList.ntuple_tail.
      move: (behead_tupleP _ ) => //= Hprf'.
      rewrite FDistBind.dE.
      rewrite rsum_split //=; under eq_bigr => a _ do under eq_bigr => b _ do rewrite FDistBind.dE.
      under eq_bigr => a _ do under eq_bigr => b _ do rewrite rsum_split //=.
      under eq_bigr => a _ do under eq_bigr => b _ do under eq_bigr => c _ do under eq_bigr => d _ do rewrite FDist1.dE xpair_eqE //=.
      have Hsusp1 (c: HashState n') (a: k'.-tuple (HashState n')) : ( (Tuple Hps) ==  [tuple of c :: a]) = ((p == c) && (ps == a)).
        by rewrite/[tuple of _] //=.
        have Hsusp2 (d: 'I_Hash_size.+1) (b: k'.-tuple 'I_Hash_size.+1) : ( (Tuple Hxs) ==  [tuple of d :: b]) = ((x == d) && (xs == b)).
          by rewrite/[tuple of _] //=.
          under eq_bigr => a _ do under eq_bigr => b _ do under eq_bigr => c _ do under eq_bigr => d _ do rewrite Hsusp1 !boolR_distr eq_sym mulRC -mulRA -mulRA.
          under eq_bigr => a _ do under eq_bigr => b _ do rewrite exchange_big.
          under eq_bigr => a _ do under eq_bigr => b _ do under eq_bigr => c _ do rewrite -rsum_pred_demote big_pred1_eq //=.
          rewrite exchange_big.
          under eq_bigr => a _ do under eq_bigr => b _ do rewrite !rsum_Rmul_distr_l ?rsum_Rmul_distr_r. 
          under eq_bigr => a _ do (rewrite exchange_big; under eq_bigr => c _ do under eq_bigr => d _ do rewrite mulRC eq_sym -mulRA).
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
            under eq_bigr => a _ do under eq_bigr => b _ do under eq_bigr => c _ do rewrite Hd'.
            under eq_bigr => a _ do under eq_bigr => b _ do rewrite -rsum_pred_demote  big_pred1_eq //=.
            under eq_bigr => a _ do under eq_bigr => b _ do  rewrite Hq' boolR_distr -mulRA -mulRA.
            under eq_bigr => a _ do rewrite -rsum_pred_demote big_pred1_eq.
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
      rewrite hash_find_insert_involutive //= ?FDist1.dE ?xpair_eqE ?eq_refl //=.
        by move/Bool.negb_true_iff: Hneq ->; rewrite Bool.andb_false_r //=.
          by move: Hprf'' => //= /andP [] //=.
    }
Qed.

Lemma hash_vec_simpl_inv' (n' k': nat) (hashes: k'.-tuple (HashState n')) value inds f :
  all
    (fun y : FixedList.fixlist [eqType of B * 'I_Hash_size.+1] n' =>
       FixedList.fixlist_length y + 1 <= n') hashes ->
  (\sum_(hshs' in [finType of k'.-tuple (HashState n')])
    ((d[ hash_vec_int  value (Tuple (hash_vec_insert_length value hashes inds))]) (hshs', inds) *R* (f hshs'))) =
  ((f (Tuple (hash_vec_insert_length value hashes inds)))).
Proof.
  move=> H1.
  under eq_bigr => hshs' _ do rewrite hash_vec_int_id' //=.
    by rewrite -rsum_pred_demote big_pred1_eq //=.
Qed.

Section Uniform.

  Lemma hash_uni n (hash_state: HashState n) value (hash_value: 'I_Hash_size.+1) :
    (hashstate_find _ value hash_state == None) ->
    (
      P[ ((hash n value hash_state) |> (fun h => ret (snd h ))) === hash_value ] =
      ((1 %R) /R/ (#|ordinal Hash_size.+1| %R))
    ).
  Proof.
    move=>/eqP Hhsfindnone; rewrite /hash Hhsfindnone //= FDistBindA //= FDistBindp1.
    rewrite (functional_extensionality (fun x : 'I_Hash_size.+1 => FDistBind.d (FDist1.d (hashstate_put n value x hash_state, x)) (fun b : HashState n * 'I_Hash_size.+1 => FDist1.d b.2)) (fun x : 'I_Hash_size.+1 => FDist1.d x)); first last.
      by move=> x; rewrite FDistBind1f //=.
        by  rewrite FDistBindp1 Uniform.dE div1R  //=.
  Qed.

End Uniform.

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
      under eq_bigr => a _ do rewrite pmfE.
      rewrite bigsum_card_constE card_tuple card_ord -natRexp.
      rewrite -Rfunctions.Rinv_pow ?mulRV //=.
        by apply expR_neq0; apply/eqP; apply RIneq.not_0_INR.
          by apply RIneq.not_0_INR.
    Defined.

    Lemma dE  a : dist a = ((Rdefinitions.Rinv (n.+1 %R)) ^R^ k).
    Proof. by move=> //=;rewrite ffunE. Qed.

  End definitions.

End uniform_vec.
End HashVec.

