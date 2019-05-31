From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.


Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

From BloomFilter Require Import InvMisc.




Set Implicit Arguments.

Definition ntuple_cons (A : Type) (n : nat) (a : A) (list : n.-tuple A) : (n.+1).-tuple A.
Proof.
    case list=> tval /eqP H0.
    split with (tval := (a :: tval)).
    by rewrite  -H0.
Defined.

Definition ntuple_head (A : Type) (n' : nat) (list : (n'.+1).-tuple A) : A .
Proof.
    apply (thead list).
Defined.

Definition ntuple_tail (A : Type) (n' : nat) (list : (n'.+1).-tuple A) : n'.-tuple A.
Proof.
    move: (tuple_eta list) => H.
    split with (tval := behead list).
    apply behead_tupleP.
Defined.

Lemma size_ncons_nil (A : Type) (a : A) (n : nat): (size (ncons n a [::])) == n.
Proof.
    rewrite size_ncons => //=.
    by rewrite addn0.
Defined.


Fixpoint set_tnth (A : Type) (m : nat) (list : m.-tuple A) (a : A) (n : nat) : m.-tuple A.
Proof.
    induction  m  as [|m'] eqn: Hm.
    induction n as [|n''] eqn: Hn.
        (* 0, 0 *)
        exact list.
        (* 0, n.+1 *)
        exact list.
    case n eqn: Hn.
        (* m.+1, 0 *)
        exact [tuple of a :: (ntuple_tail list)].
        (* m'.+1, n'.+1 *)
        exact [tuple of ntuple_head list ::  set_tnth A m' (ntuple_tail list) a n0].
Defined.
Lemma ltn_Snn a b : a.+1 < b.+1 -> a < b.
Proof.
  by rewrite -{1}(addn1 a) -{1}(addn1 b) ltn_add2r.
Qed.

Lemma tnth_cons A n (ls : n.-tuple A) x i :  forall (prf : i.+1 < n.+1) (prf': i < n),  tnth [tuple of x :: ls] (Ordinal prf) = tnth ls (Ordinal prf').
Proof.
  move: ls => [ls Hls].
  move=> prf prf' //=.
  by rewrite (@tnth_nth _ _ x _) (@tnth_nth _ _ x _) //=.
Qed.

Lemma tnth_set_nth_eq  A (n : nat) (ls: n.-tuple A) x (addr addr' : 'I_n) : (nat_of_ord addr) == (nat_of_ord addr') -> tnth (set_tnth ls x addr') addr = x.
Proof.
  move: addr addr' => [addr' Haddr'] [addr Haddr] //= /eqP Heq.
  move: ls => [ls ].
  move: addr addr' Heq n Haddr Haddr'.
  elim: ls => //= .
    by move=> addr addr' Heq [//=|n] Haddr Haddr' => /eqP //=.
  move=> y ys Hys addr addr' Heq [//=|n] Haddr Haddr' Hlen. move: (Hlen) => Hlen' //=.
  case Haddreqn: (addr) => [ | addr_].
      move: Haddr'.
      by rewrite Heq Haddreqn //=.
  rewrite/ntuple_head/ntuple_tail //=.
  move: (behead_tupleP _) => //=; move: Haddr'.
  rewrite Heq Haddreqn /thead //= => Haddr' Hbhd.
  rewrite tnth_cons //= Hys //=.
Qed.


Lemma tnth_set_nth_neq  A (n : nat) (ls: n.-tuple A) x (addr addr' : 'I_n) : (nat_of_ord addr) != (nat_of_ord addr') -> tnth (set_tnth ls x addr') addr = tnth ls addr.
Proof.
  move: ls addr addr' => [ls Hls] [addr Haddr] [addr' Haddr'] //=.
  move: n Hls addr addr'  Haddr Haddr'.
  elim: ls => //=.
    move=> n Hls. move:  Hls (Hls) => /eqP Hls Hls'.
    move=> addr addr' Haddr; move: Haddr (Haddr).
    by rewrite -{1}Hls.
  move=> y ys IHs //= [//=|n] Hls addr addr' .
  case Haddreqn: addr => [ | addr_].
     move=> Haddr //=.
     by case addr' => //=.
  case addr' => //= addr'_ Haddr'_.
    by rewrite tnth_cons //= (@tnth_nth _ _  x _) (@tnth_nth _ _  x _) => //=.
  rewrite !tnth_cons /ntuple_tail => //=.
  move: (behead_tupleP _ ) => //= Hbhd Hltnaddr_ Hneq.
  rewrite IHs => //=.
  by rewrite (@tnth_nth _ _  x _) (@tnth_nth _ _  x _) => //=.
Qed.



Section fixlist.
    Variable A : eqType.
Definition fixlist n := n.-tuple (option A).

    Definition fixlist_empty n : fixlist n :=
        @Tuple n
            (option A) 
            (ncons n None [::])
            (size_ncons_nil   None n).

    Definition fixlist_of n (a : A) : fixlist n:=
        @Tuple n
            (option A) 
            (ncons n (Some a) [::])
            (size_ncons_nil (Some a) n).

    (* I wanted to write this, but it wouldn't type check*)
    (* Fixpoint fixlist_insert (m : nat) (list : fixlist m.+1) (a : A) : fixlist m.+1 :=
        match tnth list (inord m) return fixlist m.+1  with
            | None => [tuple of (Some value) :: [tuple of behead list]]
            | Some value => match m return fixlist m.+1 with
                                | 0 => list
                                | m'.+1 =>  [tuple of (Some value) :: fixlist_insert m' [tuple of behead list] a ]
                                end
            end. *)


    Definition fixlist_insert {m : nat} (list : fixlist m)  :=
      nat_rect (fun m0 : nat => fixlist m0 -> A -> fixlist m0) (fun (list0 : fixlist 0) (_ : A) => list0)
       (fun (m0 : nat) (fixlist_insert : fixlist m0 -> A -> fixlist m0) (list0 : fixlist m0.+1) (a0 : A) =>
        let o := thead list0 in
        let H : thead list0 = o := erefl o in
        match o as o0 return (thead list0 = o0 -> fixlist m0.+1) with
        | Some s =>
            fun _ : thead list0 = Some s => [tuple of Some s :: [tuple of fixlist_insert (ntuple_tail list0) a0]]
        | None => fun _ : thead list0 = None => [tuple of Some a0 :: [tuple of behead list0]]
        end H) m list.

    Definition fixlist_unwrap (m : nat) (list : fixlist m) : seq A :=
        flatten (map (fun o_value => match o_value with
                            | Some value => [:: value]
                            | None => [::]
                            end) list).


    (* Lemma fixlist_insert (m : nat) (list : fixlist m) (a : A) : fixlist m. *)
    (*     move: a. *)
    (*     move: list. *)
    (*     elim m. *)
    (*     move=> list a. *)
    (*         exact list. (* can not insert anything into an empty list*) *)
    (*     move=> m0 fixlist_insert list a. *)
    (*     case (thead list) eqn:H; last first. *)
    (*         exact [tuple of (Some a) :: [tuple of behead list]]. *)
    (*         exact [tuple of (Some s) :: [tuple of fixlist_insert (ntuple_tail list) a]]. *)
    (* Defined. *)




(* 
    Lemma fixlist_remove_h (m m' : nat) : (m'.+1 = m) -> fixlist m.+1 -> fixlist m'.+2.
    Proof.
        move=> H list.
        rewrite -H in list.
        exact list.
    Qed.
 *)
    (* Fixpoint fixlist_remove (m : nat) (list : fixlist m.+1) (n : nat) : fixlist m.+1 :=
        match m as m', n return _ = m -> fixlist _ with
            | m'.+1, n'.+1 => fun epf => [tuple of ntuple_head list ::  @fixlist_remove m' (ntuple_tail list) n']
            | 0, n'.+1 => fun epf => [ tuple of [:: ntuple_head list]]
            | m'.+1, 0 => fun epf => match (tnth list (inord m'))  with
                            | None =>  list 
                            | Some v => [tuple of None :: (ntuple_tail list)]
                          end
            | 0, 0 => fun epf =>  [tuple of [:: None] ]
           end (erefl _)
           .
    *)


    (* remove will remove the nth index of the list *)
    Fixpoint fixlist_remove (m : nat) (list : fixlist m) (n : nat) : fixlist m.
        move: list.
        induction  m  as [|m'] eqn: Hm.
        induction n as [|n''] eqn: Hn.
            (* 0, 0 *)
            move=> _.
            exact [tuple of [::]].
            (* 0, n.+1 *)
            move=> list.
            exact list.
        case n eqn: Hn.
            (*m'.+1, 0 *)
            move=> list.
            exact [tuple of None :: (ntuple_tail list)].
        (* m'.+1, n0.+1 *)
        move=> list.
            exact [tuple of ntuple_head list ::  @fixlist_remove m' (ntuple_tail list) n0].
    Defined.

    (* rem will remove all instances of a in the list*)
    Lemma fixlist_rem (m : nat) (list: fixlist m) (a : A) : fixlist m.
        induction m.
            (* if m is 0, return empty list *)
            exact list.
        (* assume we have a rem function for lists of length m*)
        (* consider a list of length m.+1 *)
        case (ntuple_head list) eqn: H.
            (* if it's head is not none, *)
            case (s == a) eqn: H'.
                (* if the value of the head is equal to the value being removed*)
                (* return a list with None in the place of the first value, and all subsequent ones removed*)
                exact [tuple of None :: IHm (ntuple_tail list)].
            (* if the value of the head is not equal, just keep the head, remve from the tail*)
            exact [tuple of (Some s) :: IHm (ntuple_tail list)].
        (* if the value of the head is none, just remove from the tail*)
        exact [tuple of None :: IHm (ntuple_tail list)].
    Defined.


    (* Fixpoint fixlist_set_nth (m : nat) (list : fixlist  m.+1) (a : A) (n : nat) : fixlist m.+1 :=
         match m, n with
            | m'.+1, n'.+1 => [tuple of ntuple_head list ::  @fixlist_remove m' (ntuple_tail list) n']
            | 0, n'.+1 => [tuple of [:: ntuple_head list]]
            | m'.+1, 0 => [tuple of (Some a) :: (ntuple_tail list)] 
            | 0, 0 =>  [tuple of [:: Some a] ]
       end. *)

    Definition fixlist_set_nth (m : nat) (list : fixlist  m) (a : A) (n : nat) : fixlist m := set_tnth list (Some a) n .

    (* Definition fixlist_nth (m : nat) (default : A) (list : fixlist m) (n : nat) : A :=
        if n < m then
            match m with
                | 0 => default
                | m'.+1 => tnth list (Ordinal (m'.+1))
                end
        else default. *)

    Definition fixlist_nth (m : nat) (default : A) (list : fixlist m)  (n : nat) : A.
    Proof.
        case (n < m) eqn: H; last first.
            exact default.
        
        apply ltn_addr with (p := 1) in H .
        case m eqn: H1.
            exact default.
        move: (ltn0Sn n0)=> H''.
        move: (Ordinal H'')=> ind.
        case (tnth list ind) eqn: isSome.
            exact s.
            exact default.
    Defined.

    Definition fixlist_get_nth (m : nat)  (list : fixlist m)  (n : nat) : option A .
    Proof.
        case (n < m) eqn: H; last first.
            exact None.
        move: (Ordinal H)=> ind.
        case (tnth list ind) eqn: isSome.
          exact (Some s).
          exact None.
   Defined.
        

    (* Fixpoint fixlist_length' (m : nat) (list : fixlist  m.+1) : nat :=
        match m with 
            | 0 => match ntuple_head list with 
                | Some _ => 1 
                | None   => 0
                end
            | m'.+1 => match ntuple_head list with 
                | Some _ => 1 + fixlist_length' (ntuple_tail list)
                | None   =>  fixlist_length' (ntuple_tail list)
                end
            end. *)



    Definition fixlist_length (m : nat) (list : fixlist  m) : nat :=
      length (fixlist_unwrap list). 
    Definition fixlist_is_empty (m : nat) (list: fixlist m) : bool :=
      (fixlist_unwrap list) == [::].

    Definition fixlist_is_full (m : nat) (list : fixlist m) : bool :=
      fixlist_length list == m .




    (* a fixed list is top heavy if all the empty spaces are at the tail of the list*)
    Definition fixlist_is_top_heavy (m : nat) (list : fixlist m) : bool :=
      nat_rect (fun m0 : nat => fixlist m0 -> bool) xpredT
       (fun (m0 : nat) (fixlist_is_top_heavy : fixlist m0 -> bool) (list0 : fixlist m0.+1) =>
          let o := thead list0 in
          let H : thead list0 = o := erefl o in
          match o as o0 return (thead list0 = o0 -> bool) with
          | Some s => fun _ : thead list0 = Some s => fixlist_is_top_heavy [tuple of behead list0]
          | None => fun _ : thead list0 = None => fixlist_is_empty [tuple of behead list0]
          end H) m list
      .



    (* Proof. *)
    (*   move: list. *)
    (*   elim m. *)
    (*     move=> list. *)
    (*     exact true. *)
    (*   move=> m0 fixlist_is_top_heavy list. *)
    (*   case (thead list) eqn: H; last first. *)
    (*   exact (fixlist_is_empty [tuple of behead list]). *)
    (*   exact (fixlist_is_top_heavy [tuple of behead list]). *)
    (* Defined. *)



    (* Fixpoint fixlist_filter (m : nat) (P : pred A) (list : fixlist m) : fixlist m :=
        match m with
            | 0 => list
            | m'.+1 => match ntuple_head list with
                | Some a => if P a then [tuple of (Some a) :: fixlist_filter (ntuple_tail list)]
                                    else [tuple of fixlist_filter (ntuple_tail list)]
                | None => [tuple of fixlist_filter (ntuple_tail list)]
                end
            end. *)
    Fixpoint fixlist_filter (m : nat) (P : pred A) (list : fixlist m) : fixlist m.
        case m eqn: H.
            exact list.
        case (ntuple_head list).
            move=> a.
            case (P a) eqn: H'.
                exact [tuple of (Some a) :: fixlist_filter n P (ntuple_tail list)].
            exact [tuple of None :: fixlist_filter n P (ntuple_tail list)].
        exact [tuple of None :: fixlist_filter n P (ntuple_tail list)].
    Defined.




    (* Fixpoint fixlist_contains (m : nat) (a : A) (list : fixlist m) : bool :=
        match m with
            | 0 => false
            end
            | m'.+1 => match ntuple_head list with 
                | Some a' => if a' == a then true else fixlist_contains (ntuple_tail list)
                | None => fixlist_contains (ntuple_tail list)
                end
            end. *)

    Definition fixlist_contains (m : nat) (a : A) (list : fixlist m) : bool :=
      has (fun x => x == a) (fixlist_unwrap list).


    Fixpoint fixlist_index_of' (m : nat) (n: nat) (a : A) (list : fixlist m) : option nat. 
        case m eqn: H.
            exact None.
        case (ntuple_head list).
            move=> a'.
            case (a' == a) eqn: H'.
                exact (Some n).
                exact (fixlist_index_of' n0 n.+1 a (ntuple_tail list)).
            exact (fixlist_index_of' n0 n.+1 a (ntuple_tail list)).
    Defined. 

    Definition fixlist_index_of (m : nat) (a : A) (list : fixlist m) : option nat := 
        fixlist_index_of' 0 a list.

    (* uses a fixlist like a fixed length queue, inserting at the start and removing from the end*)
    Fixpoint fixlist_enqueue (m : nat) (a : option A) (list: fixlist m) : (fixlist m * option A).
     (* :=
        match m with 
            | 0     => list  (* simply drop the a *)
            | m'.+1 => [tuple of a :: fixlist_shiftl' (ntuple_head list) (ntuple_tail list)]
            end. *)
        case m eqn: H.
            exact (list, a).
        case (@fixlist_enqueue _ (ntuple_head list) (ntuple_tail list)) => shifted_tail output.
        exact ([tuple of a :: shifted_tail], output).
    Defined.

    Definition option_rcons B (ls : seq.seq B) (a : option B) :=
      if a is Some v
      then rcons ls v
      else ls.

    Definition option_cons B  (a : option B) (ls : seq.seq B) :=
      if a is Some v
      then cons v ls 
      else ls.


    Definition fixlist_shiftl (m : nat) (list: fixlist m) : fixlist m :=
        let: (result, output) := fixlist_enqueue None list in
        result.


    
    Lemma eqn_incr a b : a == b -> a.+1 == b.+1.
    Proof. by move=>/eqP/(f_equal S)/eqP. Qed.

    Lemma size_incr (X : Type) (m : nat) (ls : seq X) (o: X) : (size ls == m) -> (size (o::ls) == m.+1).
    Proof. by []. Qed.

    Lemma fixlist_coerce_some (m : nat) (ls : seq (option A)) (o: (A)) (pf: size ls == m) (pf': size ((Some o) :: ls) == m.+1) :
      (fixlist_unwrap (Tuple pf')) = o :: (fixlist_unwrap (Tuple pf)). 
      Proof.
        move: pf pf'.
        by elim ls => //.
      Qed.

    Lemma fixlist_coerce_none (m : nat) (ls : seq (option A)) (pf: size ls == m) (pf': size (None :: ls) == m.+1) :
      (fixlist_unwrap (Tuple pf')) = (fixlist_unwrap (Tuple pf)). 
      Proof.
        move: pf pf'.
        by elim ls => //.
      Qed.

     Lemma fixlist_insert_coerce_none (m : nat) (ls : seq (option A)) (o: (A)) (pf: size ls == m) (pf': size (None :: ls) == m.+1) :
      (fixlist_unwrap (fixlist_insert (Tuple pf') o) = o :: (fixlist_unwrap (Tuple pf))). 
      Proof.
        move: ls pf pf' .
        by elim m => //=.
      Qed.


      Lemma ntuple_tail_coerce (m : nat) (T: Type) (y  x: T) xs : forall (pf' : (size [:: y, x & xs] == m.+2)) (pf: size [:: x & xs] == m.+1),
        (ntuple_tail (Tuple (n:=m.+2) (tval:=[:: y, x & xs]) pf')) = (Tuple (n:=m.+1) (tval:=[:: x & xs]) pf).
      Proof.
        move: x y m.
        case: xs => [x y |x0 xs x y].
        move=> m Hpf' Hpf.
        move: (Hpf') (Hpf).
        move/eqP:Hpf => Hpf.
        move=> pf' pf.
        rewrite /ntuple_tail //=.
        generalize (behead_tupleP (Tuple (n:=m.+2) (tval:=[:: y; x]) pf')) as H_tail.
        have Hobv: (behead (Tuple (n:=m.+2) (tval:=[:: y; x]) pf')) = ([:: x] ). by []. 
        have Hobv': m.+2.-1 = m.+1. by [].
        move=> H_tail.
        dependent rewrite Hobv in H_tail.
        dependent rewrite Hobv' in H_tail.
        by rewrite (proof_irrelevance _  H_tail pf).

        move=> m pf' pf .
        rewrite /ntuple_tail //=.
        generalize (behead_tupleP (Tuple (n:=m.+2) (tval:=[:: y, x, x0 & xs]) pf')) as H_tail.
        move=> H_tail.
        have Hobv: (behead (Tuple (n:=m.+2) (tval:=[:: y, x, x0 & xs]) pf')) = [:: x, x0 & xs]. by [].
        have Hobv': m.+2.-1 = m.+1. by [].

        dependent rewrite Hobv in H_tail.
        dependent rewrite Hobv' in H_tail.
        by rewrite (proof_irrelevance _  H_tail pf).

      Qed.



      Lemma fixlist_insert_size_idem  (m : nat) (ls : fixlist m) (a : A) : size (fixlist_insert ls a) = size ls.
      Proof.
        destruct ls as [ls Hls].
        move: ls Hls .
        elim: m=> //= m Ihm xs Hxs.
        case: (thead _) => [s//=|//=]; last first.
        move: Hxs.
        by case xs => //=.
        move: Hxs.
        case: xs => //= x xs Hxs'.
        move: (Hxs').
        move/eqP: Hxs'=>Hxs'.
        case:Hxs'=>/eqP Hxs.
        move: (Ihm xs Hxs) => IHm.
        move=> Hxs'//=.
        case x => //=; last first.
        rewrite /ntuple_tail//=.
        generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=None :: xs) Hxs')) as H_tail.
        move=> H_tail.
        have Hobv: (behead (Tuple (n:=m.+1) (tval:=None :: xs) Hxs')) = xs. by []. 
        have Hobv': m.+1.-1 = m. by[].
        dependent rewrite Hobv in H_tail.
        dependent rewrite Hobv' in H_tail.
        rewrite -IHm.
        by rewrite (proof_irrelevance _  H_tail Hxs).
        move=> s'.
        rewrite /ntuple_tail//=.
        generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=Some s' :: xs) Hxs')) as H_tail.
        move=> H_tail.
        have Hobv: (behead (Tuple (n:=m.+1) (tval:=Some s' :: xs) Hxs')) = xs. by[].
        have Hobv': m.+1.-1 = m. by[].
        dependent rewrite Hobv in H_tail.
        dependent rewrite Hobv' in H_tail.
        rewrite -IHm.
        by rewrite (proof_irrelevance _  H_tail Hxs).
  Qed. 


      Lemma tval_injectivitiy (T:Type) n (t: n.-tuple T) (pf: size t == n) : Tuple (n:=n) (tval:=tval t) pf =  t. 
      Proof.
        destruct t as [t t_pf].
        move=>//=.
          by rewrite (proof_irrelevance _ pf t_pf).
      Qed.







     Lemma fixlist_insert_coerce_some (m : nat) (ls : seq (option A)) (s o: A) (pf: size ls == m) (pf': size (Some s :: ls) == m.+1) :
      (fixlist_unwrap (fixlist_insert (Tuple pf') o) = s :: fixlist_unwrap (fixlist_insert (Tuple pf) o)). 
      Proof.
        rewrite fixlist_coerce_some.
        by rewrite fixlist_insert_size_idem .
        rewrite /ntuple_tail//= .
        generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=Some s :: ls) pf')) as H_tail.
        move=> H_tail.
        have Hobv: (behead (Tuple (n:=m.+1) (tval:=Some s :: ls) pf')) = ls. by [].
        have Hobv': m.+1.-1 = m. by [].
        dependent rewrite Hobv in H_tail.
        dependent rewrite Hobv' in H_tail.
        clear Hobv.
        clear Hobv'.
        move=>Hpf.
        suff: (Tuple (n:=m) (tval:=fixlist_insert (Tuple (n:=m) (tval:=ls) H_tail) o) Hpf) = (fixlist_insert (Tuple (n:=m) (tval:=ls) pf) o).
        by move=> ->.
        rewrite (proof_irrelevance _ pf H_tail).
        by rewrite tval_injectivitiy.
    Qed.



      Lemma fixlist_contains_obv a m' xs Hxs : fixlist_contains a (fixlist_insert (Tuple (n:=m') (tval:=xs) Hxs) a) =
  has (eq_op^~ a) (fixlist_unwrap (fixlist_insert (Tuple (n:=m') (tval:=xs) Hxs) a)).
        Proof.
          apply/eqP=>//=.
        Qed.
        

    Lemma fixlist_has_eq (m : nat) (list: fixlist m) (a : A) (P: pred A) :
       (has P (fixlist_unwrap (fixlist_insert list a))) = has P (fixlist_unwrap list) || [ && P a, fixlist_contains a (fixlist_insert list a) & ~~ has P (fixlist_unwrap list)].
      Proof.
        destruct list as [xs Hxs].
        move: m Hxs .
        elim: xs => //=.
        move=> m xs.
        case H: (P a).
        move: (xs).
        by move/eqP: xs => <- //=.
        move=> //=.
        by induction m=>//=.

        move=> x xs IHx m.
        case m.
        by move=> Hxs; move/eqP:(Hxs)=>Hwrong; inversion Hwrong.
        case x =>[s m'|]; last first.
        move=> m' Hxs.
        rewrite  (@fixlist_insert_coerce_none ) //=.
        rewrite fixlist_coerce_none.
        move: (Hxs).
        move/eqP: Hxs => Hxs.
        case: Hxs => /eqP Hxs Hxs'.
        case (has P (fixlist_unwrap (Tuple (n:=m') (tval:=xs) Hxs'))) => //=.
        by apply orbT.
        rewrite Bool.orb_false_r.
        case (P a) => //=.
        rewrite /fixlist_contains//=.
        have :a == a. by[].
        by move=> ->.

        move=> Hxs'.
        rewrite  (@fixlist_insert_coerce_some m' xs s a) .
        rewrite fixlist_coerce_some /fixlist_contains.
        rewrite fixlist_insert_coerce_some //=.
        case Hps: (P s) => //=.
        move: (Hxs').
        move/eqP: Hxs' => Hxs'.
        case: Hxs' => /eqP Hxs'.
        move=> Hxs.
        rewrite IHx.
        case (has P (fixlist_unwrap (Tuple (n:=m') (tval:=xs) Hxs))) => //=.
        case Hpa: (P a) => //=.
        case Heq: (s == a) => //= .
        move/eqP: Heq => Heq.
        rewrite -Heq in Hpa.
        rewrite Hpa in Hps.
        by inversion Hps.
  Qed.


      Lemma fixlist_length_coerce (m : nat) (ls : fixlist m) ( x : A) pf :
              fixlist_length [tuple of Some x :: (Tuple (n:=m) (tval:=ls) pf)] = (fixlist_length (Tuple pf)).+1.
        Proof.
          destruct ls as [ls Hls].
          move: ls Hls pf.
          by elim: m=> //= m IHx [//|o_x] xs .
        Qed.


      Lemma fixlist_insert_length_incr (m : nat) (ls : fixlist m) (a : A) :
        fixlist_length ls < m ->
        fixlist_length (fixlist_insert ls a) = (fixlist_length ls).+1.
      Proof.
        destruct ls as [ls Hls].
        move: ls Hls .
        elim: m=> //= m Ihm xs .
        case: xs => //= o_x xs IHxs.
        move: (IHxs); move/eqP: IHxs =>  IHxs; case: IHxs => /eqP IHxs IHxs'.

        case: o_x => //=.
        move=> x.
        
        have: fixlist_length (Tuple (n:=m.+1) (tval:=Some x :: xs) IHxs') < m.+1 -> fixlist_length (Tuple IHxs) < m.
        by rewrite /fixlist_length//=.
        move=> H /H Hlen.

        move: (Ihm xs IHxs Hlen) => IHn.
        clear Ihm.
        rewrite /ntuple_tail .
        generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=Some x :: xs) IHxs')) => //= Ht'.
        rewrite (proof_irrelevance _ Ht' IHxs) => //=.
        rewrite fixlist_length_coerce => //=.
        rewrite tval_injectivitiy.
        rewrite IHn.
        by rewrite /fixlist_length => //=.
      Qed.


 


      Lemma fixlist_is_empty_top_heavy (m : nat) (ls : fixlist m) :
        fixlist_is_empty ls -> fixlist_is_top_heavy ls.
      Proof.
        case: ls => ls Hls.
        move: m Hls.
        elim ls => //=.
        by move=>m ls_H; move: (ls_H); move/eqP: ls_H => <-.
        move=> o_x xs IHm [//|m'] Hls .
        by case o_x => //=.
      Qed.


      Lemma fixlist_empty_is_empty (m : nat) : fixlist_is_empty (fixlist_empty m).
      Proof.
        by elim m=> //=.
      Qed.

      Lemma fixlist_empty_is_top_heavy (m : nat) : fixlist_is_top_heavy (fixlist_empty m).
      Proof.
        by apply fixlist_is_empty_top_heavy; exact (fixlist_empty_is_empty m).
      Qed.

      Lemma fixlist_top_heavy_coerce_some (m : nat) (xs : seq (option A)) (x a: A) (pf: size xs == m) (pf': size (Some x :: xs) == m.+1) :
        fixlist_is_top_heavy (fixlist_insert (Tuple pf') a) = fixlist_is_top_heavy (fixlist_insert (Tuple pf) a).
        Proof.

        move:  m pf' pf.
        elim: xs => [m pf pf' |o_x xs IHx m pf pf'].
          move=> //=.
          move: (pf'); move/eqP: pf' => Hpf.
          move: pf.
          by rewrite -Hpf .
          move: pf pf'.
        case o_x => [//= x'|].
        move=> pf pf'.
        rewrite /ntuple_tail.
        generalize  (behead_tupleP (Tuple (n:=m.+1) (tval:=[:: Some x, Some x' & xs]) pf)) => Ht'.
        have Hht'rew: size (behead (Tuple (n:=m.+1) (tval:=[:: Some x, Some x' & xs]) pf)) == m.+1.-1 = (size (o_x :: xs) == m). by []. 
        dependent rewrite Hht'rew in Ht' => //=.
        rewrite/tuple.
        rewrite /behead_tuple.
        generalize  (behead_tupleP
          (Tuple (n:=m.+1) (tval:=Some x :: fixlist_insert (Tuple (n:=m) (tval:=Some x' :: xs) Ht') a)
             (let
              '@Tuple _ _ _ tP as t :=
               cons_tuple (Some x)
                 (Tuple (n:=m) (tval:=fixlist_insert (Tuple (n:=m) (tval:=Some x' :: xs) Ht') a)
                    (let
                     '@Tuple _ _ _ tP as t := fixlist_insert (Tuple (n:=m) (tval:=Some x' :: xs) Ht') a
                      return (size t == m) in tP)) return (size t == m.+1) in tP))) => //= Ht.
           have: (Tuple (n:=m) (tval:=fixlist_insert (Tuple (n:=m) (tval:=Some x' :: xs) Ht') a) Ht) = (fixlist_insert (Tuple (n:=m) (tval:=Some x' :: xs) pf') a).

           rewrite tval_injectivitiy.
           by rewrite (proof_irrelevance _ Ht' pf').
          by move=> ->.

          move=> pf pf'//=.
        rewrite /ntuple_tail.
        generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=[:: Some x, None & xs]) pf)) => Ht'.
        have Hht'rew: size (behead (Tuple (n:=m.+1) (tval:=[:: Some x, None & xs]) pf)) == m.+1.-1 = (size (None :: xs) == m). by [].
        dependent rewrite Hht'rew in Ht' => //=.

        rewrite/tuple.
        rewrite /behead_tuple.

        generalize  (behead_tupleP
          (Tuple (n:=m.+1) (tval:=Some x :: fixlist_insert (Tuple (n:=m) (tval:=None :: xs) Ht') a)
             (let
              '@Tuple _ _ _ tP as t :=
               cons_tuple (Some x)
                 (Tuple (n:=m) (tval:=fixlist_insert (Tuple (n:=m) (tval:=None :: xs) Ht') a)
                    (let
                     '@Tuple _ _ _ tP as t := fixlist_insert (Tuple (n:=m) (tval:=None :: xs) Ht') a
                      return (size t == m) in tP)) return (size t == m.+1) in tP))) => //= Ht.
       have: (Tuple (n:=m) (tval:=fixlist_insert (Tuple (n:=m) (tval:=None :: xs) Ht') a) Ht) = (fixlist_insert (Tuple (n:=m) (tval:=None :: xs) pf') a).
           rewrite tval_injectivitiy.
           by rewrite (proof_irrelevance _ Ht' pf').
          by move=> ->.
      Qed.




    Lemma fixlist_insert_preserves_top_heavy (m : nat) (ls : fixlist m) (a : A) :
        fixlist_is_top_heavy ls -> fixlist_is_top_heavy (fixlist_insert ls a).
      Proof.
        case: ls => ls Hls.
        move: ls Hls a.
        elim: m .
        move=> ls Hls' a.
        move: (Hls'); move/eqP: Hls'=>/size0nil Hls'. 
        by rewrite Hls'.
        move=> m IHn [//|x] xs Hxs a.
        have Hxseq: size (x :: xs) == m.+1 = (size xs == m). by []. 
        dependent rewrite Hxseq in Hxs.
        case x; last first.
        move => //=.
          move=>/fixlist_is_empty_top_heavy.
          rewrite /tuple.
          rewrite /behead_tuple.
          generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=None :: xs) Hxs)) as H_tail => //= H_tail.
          generalize (behead_tupleP
            (Tuple (n:=m.+1) (tval:=Some a :: xs)
              (valP (sT:=tuple_subType m (option A)) (Tuple (n:=m) (tval:=xs) H_tail)))) as H_tail' => //= H_tail'.
          by rewrite (proof_irrelevance _ H_tail H_tail').

        move: (IHn xs Hxs a) => IHn'.
        move=> x'.
        have Heq: fixlist_is_top_heavy (Tuple (n:=m.+1) (tval:=Some x' :: xs) Hxs) = fixlist_is_top_heavy (Tuple (n:=m) (tval:=xs) Hxs).
          move=> //=.
          rewrite/tuple.
          rewrite /behead_tuple.
          generalize ((behead_tupleP (Tuple (n:=m.+1) (tval:=Some x' :: xs) Hxs))) => //= Ht.
          by rewrite (proof_irrelevance _ Ht Hxs).

          move=> Hbase.
          rewrite (@fixlist_top_heavy_coerce_some m xs x' a Hxs).
          apply IHn.
          by rewrite -Heq.
    Qed.

    Lemma fixlist_insert_rewrite (m : nat) (ls : fixlist m) (a : A) :
        fixlist_is_top_heavy ls -> fixlist_length ls < m -> fixlist_unwrap (fixlist_insert ls a) = rcons (fixlist_unwrap ls)  a.
      Proof.
        case: ls => ls Hls.
        move: ls Hls.
        elim: m => //= m IHn ls .
        case ls => //= x xs Hls.
        case: x => //=; last first.
          rewrite/tuple.
          rewrite /behead_tuple.
          generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=None :: xs) Hls)) => //= Ht.
          rewrite /fixlist_is_empty =>/eqP His_empty.
          rewrite fixlist_coerce_none.
          rewrite His_empty //=.
          move=> H //=.
          rewrite fixlist_coerce_some.
          by rewrite His_empty.
        move=> x.
        rewrite /tuple.
        rewrite /behead_tuple.
        generalize  (behead_tupleP (Tuple (n:=m.+1) (tval:=Some x :: xs) Hls)) => //= Ht.
        move=> His_top_heavy.
        move=> Hvlen.
        move: (Hvlen).
        move: Hvlen.
        rewrite {1}/fixlist_length.
        rewrite {1}/fixlist_unwrap //=.
        rewrite -{1}(addn1 m).
        rewrite -{1}(addn1 (length _)).
        rewrite ltn_add2r => Hlen Hvlen.
        have Hlenfxlen:  length (flatten [seq match o_value with
                              | Some value => [:: value]
                              | None => [::]
                              end | o_value <- xs]) = (fixlist_length (Tuple Ht)). by [].
       rewrite  Hlenfxlen in Hlen.

        rewrite /ntuple_tail.
        rewrite fixlist_coerce_some . by rewrite fixlist_insert_size_idem.
        move: (IHn xs Ht His_top_heavy Hlen) => IHn'.
        clear His_top_heavy.
        clear Hlenfxlen.
        clear Hlen.
        have: (forall pf, fixlist_unwrap (fixlist_insert (Tuple (n:=m) (tval:=xs) pf) a) =
         rcons (fixlist_unwrap (Tuple (n:=m) (tval:=xs) pf)) a).
        move=> pf.
        move: IHn'.
        by rewrite (proof_irrelevance _ pf Ht).
        clear IHn'.
        move=> IHn'.
        clear Hvlen.
        clear Ht.
        clear ls.
        clear IHn.



        have Hrew:
             (size
                (fixlist_insert
                    (Tuple (n:=m) (tval:=behead (Tuple (n:=m.+1) (tval:=Some x :: xs) Hls))
                           (behead_tupleP (Tuple (n:=m.+1) (tval:=Some x :: xs) Hls))) a) == m) =
             (size xs == m) .
          generalize  (behead_tupleP (Tuple (n:=m.+1) (tval:=Some x :: xs) Hls)) => //=.
          move=> Ht''.
          by rewrite fixlist_insert_size_idem //=.
          move=> Ht.
       suff: (Tuple (n:=m)
          (tval:=fixlist_insert
                   (Tuple (n:=m) (tval:=behead (Tuple (n:=m.+1) (tval:=Some x :: xs) Hls))
                      (behead_tupleP (Tuple (n:=m.+1) (tval:=Some x :: xs) Hls))) a) Ht) = (fixlist_insert (Tuple (n:=m) (tval:=xs) Hls) a).
       move=> ->.
       by rewrite IHn'.



        rewrite tval_injectivitiy.
        generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=Some x :: xs) Hls)) => //= Ht'.
        by rewrite (proof_irrelevance _ Ht' Hls).
  Qed. 



  Lemma fixlist_insert_contains (m : nat) (ls : fixlist m) (a : A) :
        fixlist_is_top_heavy ls -> fixlist_length ls < m -> fixlist_contains a (fixlist_insert ls a) .
  Proof.
        case: ls => ls Hls.
        move: ls Hls.
        elim: m => //= m IHn ls .
        case ls => //= o_x xs Hls.
        case: o_x => //=; last first.
          rewrite/tuple.
          rewrite /behead_tuple.
          generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=None :: xs) Hls)) => //= Ht.
          rewrite /fixlist_is_empty =>/eqP His_empty.
          move=> Hlen.
          rewrite /fixlist_contains.
          rewrite fixlist_coerce_some => //=.
          have: (a == a). by [].
          by move=> ->.

        move=> x.
        move: (Hls).
        move/eqP: Hls => Hls.
        case: Hls => /eqP Hls Hls'.
        move: (IHn xs Hls) => IHn'.
        clear IHn.
        rewrite /tuple.
        rewrite /behead_tuple.
        generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=Some x :: xs) Hls')) => //= Hls''.
        rewrite (proof_irrelevance _ Hls'' Hls).
        move=> /IHn' IHn.
        clear IHn'.
        rewrite /fixlist_length => //=.
        rewrite -{1}(addn1  (length _)).
        rewrite -{1}(addn1  m).
        rewrite ltn_add2r => Hvlen.
        have Hlenfxlen:  length (flatten [seq match o_value with
                              | Some value => [:: value]
                              | None => [::]
                              end | o_value <- xs]) = (fixlist_length (Tuple Hls)). by [].
 
        rewrite Hlenfxlen in Hvlen.
        apply IHn in Hvlen.
        clear IHn.
        clear Hlenfxlen.
        clear Hls''.
        have Hls'_rem : (size xs).+1 == m.+1 = (size xs == m). by[].
        dependent rewrite Hls'_rem in Hls'.
        rewrite (proof_irrelevance _ Hls' Hls).
        clear Hls'.

        rewrite /fixlist_contains.
        rewrite fixlist_coerce_some. by rewrite fixlist_insert_size_idem .
        move=> Hsz //=.
        case (x == a) => //=.
        rewrite /ntuple_tail//=.
        rewrite tval_injectivitiy.
        generalize (behead_tupleP (Tuple (n:=m.+1) (tval:=Some x :: xs) Hls)) => //= Ht'.
        rewrite -/fixlist_contains.
        move: Hvlen.
        rewrite /fixlist_contains.
        by rewrite (proof_irrelevance _ Hls Ht').
        Qed.





    Lemma fixlist_length_unwrap_ident : forall (m : nat) (ls : fixlist m), length (fixlist_unwrap ls) = fixlist_length ls.
    Proof.
      move => m.
      elim: m => //=.
    Qed.
     


    Lemma fixlist_empty_find_index' (n acc: nat) k (ls : fixlist n) : 
      fixlist_is_empty ls  ->
      fixlist_index_of' acc k ls = None.
    Proof.
      move:   ls acc k => [].
      elim: n=> //=  n IHs.
      move=> [//=| x xs].
      rewrite/fixlist_is_empty/fixlist_unwrap/ntuple_head/thead /ntuple_tail => prf acc k.
      rewrite (tnth_nth x) //=.
      move: (behead_tupleP _) => //=.
      move: prf.
      case: x => //= _ prf Hempty.
      apply IHs.
      by rewrite /fixlist_is_empty/fixlist_unwrap.
    Qed.

    Lemma fixlist_empty_find_index (n acc: nat) k (ls : fixlist n) : 
      fixlist_is_empty ls  ->
      fixlist_index_of k ls = None.
    Proof.
      rewrite /fixlist_index_of => Hisempty.
      by rewrite fixlist_empty_find_index' => //=.
    Qed. 


    Lemma fixlist_index_pred (n acc ind : nat) (ls : fixlist n) k :
        acc > 0 ->
        fixlist_index_of' acc k ls = Some ind ->
        fixlist_index_of' acc.-1 k ls = Some ind.-1.
      move: ls acc k => [ ] .
      elim: n .
           by move=> [ ] //=.
      move=> n IHn [ //= | x xs] .
      move=>  Hls acc k ; move: (Hls); move: Hls => //= /eqP [] /eqP Heqn Hls.
      rewrite/ntuple_head/thead //= (tnth_nth x) //=.
      case: x => //= [x | ].
        move: (erefl _).
        case: (_  == _) => //=.
          by move=> _ _ [] ->.
        move=> _.
        rewrite/ntuple_tail//=.
        move: (behead_tupleP _) => //= Htemp Hacc; rewrite (proof_irrelevance _ Htemp Heqn); clear Htemp.
        have HSacc : 0 < acc.+1. by [].
        move=>/(IHn xs Heqn acc.+1 k HSacc) .
        by rewrite prednK //=.

      rewrite/ntuple_tail//=.
      move: (behead_tupleP _) => //= Htemp Hacc; rewrite (proof_irrelevance _ Htemp Heqn); clear Htemp.
      have HSacc : 0 < acc.+1. by [].
      move=>/(IHn xs Heqn acc.+1 k HSacc) .
      by rewrite prednK //=.
   Qed.



    Lemma fixlist_index_of_lt (n ind : nat) (ls: fixlist  n ) k :  fixlist_is_top_heavy ls ->
                                    fixlist_index_of k ls = Some ind -> ind < fixlist_length ls.
    Proof.
      move: ls k ind => [ ] .
      elim: n .
           by move=> [ ] //=.
      move=> n IHn [ //= | x xs] .
      move=>  Hls k ind; move: (Hls); move: Hls => /eqP [] /eqP Heqn Hls Hith Hfind .
      move: IHn (Hith) (Hfind) .
      rewrite /fixlist_index_of //= /ntuple_head/thead/tnth//= /ntuple_tail => IHn.
      move: (erefl _).
      move: (behead_tupleP _) => //=.
      move=> Htemp; rewrite (proof_irrelevance _ Htemp Heqn); clear Htemp.
      move: Hls Hith Hfind .
      case: x => [ x| ] Hith' Hfind'; last first.
        by move=>  Hempty; rewrite fixlist_empty_find_index' //=.
      move=> Hfindt; move: (Hfindt).
      rewrite/tuple; rewrite/behead_tuple; move: (behead_tupleP _) => //= Htemp;
      rewrite (proof_irrelevance _ Htemp Heqn); clear Htemp.
      move=>   Hith .
      move: (erefl _) Hith; case Heqk: (_ == _) =>  _; last first.
        move=> Hflind _ Hith /(fixlist_index_pred ) Hind.
        have Hosn: (0 < 1). by [].
        apply Hind in Hosn. clear Hind; move: Hosn => //= Hind.
        move: (IHn xs Heqn k ind.-1 Hith Hind).
        rewrite /fixlist_length/fixlist_unwrap //= -subn1.
        case: (length _) => [|len].
          by rewrite ltn0.
          by rewrite !ltnS leq_subLR addnC addn1.
     by move=> Hlen _ Hith [] <-; rewrite /fixlist_length/fixlist_unwrap//=.
  Qed.






  Lemma fixlist_index_set_is_top_heavy n (fls: fixlist n) k ind: fixlist_is_top_heavy fls ->
                                    fixlist_index_of k fls = Some ind ->
                          fixlist_is_top_heavy (fixlist_set_nth fls k ind ).
  Proof.
      move: fls k ind => [ ] .
      elim: n .
        by move=> [ ] //=.
      move=> n IHn [ //= | x xs] Heqn k ind Hith_base Hind_of .
      move: (Hith_base) (Hind_of); move: IHn.
      rewrite /fixlist_set_nth//=/thead (tnth_nth x) //= => IHn.
      move: (erefl _) => //=.
      move: (erefl _) => //=.
      move: Heqn Hith_base Hind_of .
      case: x => [x | ] Heqn Hith_base Hind_of //=; last first.
        move=> prf _ Hisempty.
        by rewrite fixlist_empty_find_index //=.
      move: Heqn Hith_base Hind_of .
      case: ind => [ | ind]  Heqn Hith_base Hind_of Hlen //=.
        move=>    _ Hith Hind.
        move: Hith.
        rewrite /tuple/behead_tuple/ntuple_tail;
        move:  (behead_tupleP _) => //= prf' ;
        move: (behead_tupleP _) => //= prf''.
        by rewrite (proof_irrelevance _ prf' prf'').
      move=> _ .
      rewrite /tuple/ntuple_tail//=.
      move: (behead_tupleP _) => //= Heqn'.
      move: (behead_tupleP _) => //= Hsz.
      have: ((Tuple (n:=n) (tval:=set_tnth (Tuple (n:=n) (tval:=xs) Heqn') (Some k) ind) Hsz) =
        set_tnth (Tuple (n:=n) (tval:=xs) Heqn') (Some k) ind).
        move: Hsz.
        by case: (set_tnth _) => //= ls prf0 prf1; rewrite (proof_irrelevance _ prf0 prf1) //=.
      move=> -> Hith .

      move: IHn Hind_of; rewrite /fixlist_index_of => IHn Hind_of //=.
      move: (erefl _); case Hxkeqn: (_ == _) => _ //=.
      move=> /fixlist_index_pred Hsn.
      have Hfindof: (0 < 1). by []. apply Hsn in Hfindof; clear Hsn; move: Hfindof => //=.
      rewrite /ntuple_tail; move: (behead_tupleP _) => //= Htemp.
      rewrite (proof_irrelevance _ Htemp Heqn); clear Htemp => Hindof.
      apply IHn => //=.
      by rewrite (proof_irrelevance _ Heqn' Heqn).

    Qed.

  Lemma option_rcons_coerce B (xs : seq.seq B) x y : option_rcons (x :: xs) y = x :: (option_rcons xs y).
  Proof.
    by case: y =>//=.
  Qed.
  Lemma fixlist_unwrap_eq (m : nat)  (xs ys : fixlist m) :
      tval xs = tval ys ->
      fixlist_unwrap xs = fixlist_unwrap ys.
  Proof.
    move: xs ys => [xs Hxs] [ys Hys]; move: xs ys Hxs Hys.
    elim: m => //= [ [ |  //= ] [ | //= ] Hxs Hys _ | m IHm [ //= | x xs] [ //= | y ys] Hxs Hys ].
    by rewrite (proof_irrelevance _ Hxs Hys).
    by move=> Heq; move: Hxs Hys; rewrite Heq => Hxs Hys; rewrite (proof_irrelevance _ Hxs Hys).
  Qed.

  Lemma option_cons_ident B (ls : seq.seq B) : ls = option_cons None ls.
  Proof.
      by [].
  Qed.

  Lemma option_rcons_ident B (ls : seq.seq B) : ls = option_rcons ls None .
  Proof.
      by [].
  Qed.


  Lemma fixlist_length_bounds (m : nat) (ls : fixlist m) : fixlist_length ls  < m.+1.
  Proof.
    move: ls => []; elim: m => [ | m IHm ] [//= | ] x xs Hxs.
    by move: Hxs => //=.
    case: x Hxs => [ x | ] Hxs.
      move: Hxs (Hxs) => /eqP  Heqxs Hxs.
      move: Heqxs => //= []/eqP Heqxs.
      rewrite /fixlist_length fixlist_coerce_some//= -(addn1 (fixlist_length _)) -(addn1 m.+1).
      by rewrite ltn_add2r; apply IHm.
    rewrite /fixlist_length fixlist_coerce_none -(addn1 m.+1); apply ltn_addr.
    by apply IHm.
  Qed.


  Lemma fixlist_enqueue_unwrap' (m : nat) (a : option A) (list : fixlist m) :
    m > 0 ->
    let: (list', result) := fixlist_enqueue (a) list  in 
        option_rcons (fixlist_unwrap list') result = option_cons a (fixlist_unwrap list).
  Proof.
    case Henq: (fixlist_enqueue (a) list) => [[n_ls Hn_ls] result].
    move: list a n_ls Hn_ls result  Henq => [].
    elim: m => //= m IHm  [//= | x xs] Hxs a [//=| y ys] Hys result .
    rewrite /ntuple_head/thead (tnth_nth x) //=.
    case Henq_eq : (fixlist_enqueue _ ) => [[xs' Hxs''] x'] [Hay Hxs' Hx'].
    move: Henq_eq.
    rewrite /ntuple_tail; move: (behead_tupleP _) => //= Hlenq.
    move: Hys.
    rewrite -Hx' -Hay -Hxs' => Hys Henq .
    rewrite ltnS leq_eqVlt => /orP [/eqP Hmeq0 | Hmlt ].
    move: (Hlenq); rewrite -{1}Hmeq0 => /eqP/size0nil Hnil.
    move: Hxs Hlenq Henq ; rewrite Hnil //= => Hxs Hleqn .
    move:  Hleqn (Hleqn) IHm xs Hnil xs' Hxs'' Hxs' Hys Hmeq0 Hxs => /eqP <- //=.
    move=>  Hleqn IHm xs Hnil [ | x0 xs0] .
      move=> Hxs'' _ Hys _ Hxs [] -> //=.
      have Hprf: (size [:: Some a] == 1). by[].
      rewrite /fixlist_unwrap/option_rcons/option_cons//=.
      by case: x' Hx' => //=; case: a Hay Hprf => //=.
    by move=> Hxs'' Hys0 Hys _ Hxs [] //=.

    move: Hys (Hys) => /eqP [] /eqP Hlx' Hys.
    case: a Hay Hys => [a Hay Hys | Hay Hys] .
      rewrite fixlist_coerce_some.
      rewrite option_rcons_coerce.
      rewrite (@IHm xs _ x xs') //=; last first.
        by rewrite Henq (proof_irrelevance _ Hxs'' Hlx').

      case: x Hxs Henq => [ x | ] Hxs Henq.
        by rewrite fixlist_coerce_some //=.
      by rewrite fixlist_coerce_none //=.
    rewrite fixlist_coerce_none.
    case: x Hxs Henq => [ x | ] Hxs Henq; last first.
    rewrite fixlist_coerce_none.
    rewrite -(IHm _ _ _ xs' _ x') //=.
    by rewrite Henq (proof_irrelevance _ Hxs'' Hlx').
    rewrite fixlist_coerce_some /option_cons.
    by rewrite (IHm xs _ (Some x)) => //=; rewrite Henq (proof_irrelevance _ Hxs'' Hlx').
  Qed.

  Lemma fixlist_enqueue_unwrap (m : nat) (a result: option A) (list : fixlist m) list' :
    m > 0 ->
      (list', result) = fixlist_enqueue (a) list -> 
        option_rcons (fixlist_unwrap list') result = option_cons a (fixlist_unwrap list).
  Proof.
    move=>/fixlist_enqueue_unwrap' H Heqn.
    move: (H a list).
    by rewrite -Heqn => //=.
  Qed.




  Lemma fixlist_enqueue_unwrap_some (m : nat) (a : A) (list list': fixlist m) result :
    m > 0 ->
      (list', result) = fixlist_enqueue (Some a) list  ->
        option_rcons (fixlist_unwrap list') result = a :: (fixlist_unwrap list).
  Proof.
    move=> Hlvd Henq.
    by rewrite (@fixlist_enqueue_unwrap _ (Some a) _ list) => //=.
  Qed.


  Lemma fixlist_enqueue_preserves_full (m : nat) (a : A) (list list': fixlist m) :
    m > 0 -> 
    fixlist_is_full list ->
    fst (fixlist_enqueue (Some a) list) = list' ->
    fixlist_is_full list'.
  Proof.
    move: list list' => [xs Hxs] [ys Hys]; move: a xs ys Hxs Hys.
    elim: m => //= m IHm a [ //= | x xs] [ //= | y ys] Hxs Hys.
      rewrite ltnS leq_eqVlt => /orP [].
      move=>/eqP Hm0.
      rewrite /fixlist_is_full //=.
      move: Hxs Hys; rewrite -Hm0 => Hxs Hys; rewrite /fixlist_length //=.
      case: x Hxs => //= [x | ] Hxs.
          move=>/eqP [] => His_empty.
          rewrite/tuple //=/ntuple_tail; move: (behead_tupleP _) => //= Hln; move: Hln (Hln).
          move=>/eqP/size0nil-> //= Hlen.
          move: (valP _) => //= Hlen'.
          by move=> []  => <- Heqn; move: Hys; rewrite -Heqn => //=.
      rewrite fixlist_coerce_none //= => H1.
      move=> [Hay Hxn].
      move: Hys; rewrite -Hay -Hxn => Hys //=.
      move: H1; rewrite /fixlist_unwrap //=.
      by move: Hxs => /eqP [] /size0nil -> //=.
    move=> Hmltn; rewrite /fixlist_is_full/fixlist_length.
    case: x Hxs => [x|] Hxs.
      move: Hxs (Hxs) => /eqP [] /eqP Hx'eqn Hxs.
      rewrite fixlist_coerce_some //= => /eqP [] /eqP Hlen.
      rewrite /ntuple_head/thead (tnth_nth (some x)) //=.
      rewrite /ntuple_tail//=; move: (behead_tupleP _) => //= Hxs_sz.
      case Henq: (fixlist_enqueue _) => [[result Hresult] output] => [[ Hay Hres]].
      move: Hys; rewrite -Hay => Hys; move: Hys (Hys) => /eqP [] /eqP Hybeq Hys; rewrite fixlist_coerce_some //=.
      apply/eqP/f_equal/eqP.
      apply IHm with (xs:= xs) (Hxs:= Hxs_sz) (a:=x) => //=.
      rewrite Henq //=; clear Henq.
      move: Hresult; rewrite Hres => Hresult.
      by rewrite (proof_irrelevance _ Hresult Hybeq).
    move: Hxs (Hxs) => /eqP [] /eqP Hxs_len Hxs.
    rewrite fixlist_coerce_none => Hxslen.
    move: (fixlist_length_bounds (Tuple (n:=m) (tval:=xs) Hxs_len)) .
    rewrite ltn_neqAle => /andP [/negP Hlt Hlen].
    by move: (Hlt Hxslen).
  Qed.

  Lemma tnth_tuple_cons B m n (x : B) xs : forall prf0 prf1 prf2 prf3,
    tnth (Tuple (n:=m.+1) (tval:=x :: xs) prf0) (Ordinal (n:=m.+1) (m:=n.+1) prf1) =
    tnth (Tuple (n:=m) (tval:=xs) prf2) (Ordinal (n:=m) (m:=n) prf3).
  Proof.
    move: n; elim: m => [//=|] m IHm n.
    move=> Hprf0 Hprf1 Hprf2 Hprf3.
    rewrite (tnth_nth x) //=.
    rewrite (tnth_nth x) //=.
  Qed.


  Lemma fixlist_get_nth_coerce m (xs : fixlist m) x n : forall Hxxs Hxs,
    fixlist_get_nth (Tuple (n:=m.+1) (tval:=x :: xs) Hxxs) n.+1 =
    fixlist_get_nth (Tuple (n:=m) (tval:=xs) Hxs) n.
  Proof.
    move=> Hxxs Hxs.
    rewrite /fixlist_get_nth//=.
    move:  {1}(erefl (_ < _)).
    case Hnlm: {2 3}(n.+1 < m.+1); move: Hnlm;
    rewrite -{1}(addn1 m) -{1}(addn1 n) {1}ltn_add2r => Hlmn;
    move: (erefl ( _ < _)); rewrite {2 3}Hlmn => Htmp //=.
    move: xs x Hxxs Hxs => [xs Hxxslen] x Hxxs //= Hxs.
    rewrite (proof_irrelevance _ Hxs Hxxslen); clear Hxs.
    rewrite (proof_irrelevance _ Htmp Hlmn); clear Htmp => Hprf.
    move: {1}(erefl _); case Htnth_eq: (tnth _) => [v] _.
      move: Htnth_eq => //= <-.
      rewrite (@tnth_tuple_cons _ _ _ _ _ Hxxs Hprf  Hxxslen Hlmn) //=.
      by move: (erefl _); case Htnth_eq: (tnth _).
    move: Htnth_eq => {1}<- .
    rewrite (@tnth_tuple_cons _ _ _ _ _ Hxxs Hprf  Hxxslen Hlmn) //=.
    by move: (erefl _); case Htnth_eq: (tnth _).
  Qed.

  Lemma fixlist_get_nth_full_succeed m (ls:fixlist m) n :
    n < m ->
    fixlist_is_full ls ->
    exists a, (fixlist_get_nth ls n) = Some a.
  Proof.
    move: ls n => []; elim: m =>  [//= | ] m IHm [//= | x xs] Hxs n .
    move: x xs Hxs.
    elim: n =>  [//= | n IHn ] x xs Hxs.
      case: x Hxs => [x | ] Hxs.
        by move=> Hlen; exists x; rewrite /fixlist_get_nth //=.
      rewrite /fixlist_is_full//= /fixlist_length fixlist_coerce_none=> _ Hxslen.
      move: (fixlist_length_bounds (Tuple (n:=m) (tval:=xs) Hxs)) .
      rewrite ltn_neqAle => /andP [/negP Hlt Hlen].
      by move: (Hlt Hxslen).
    move: Hxs (Hxs) => /eqP [] /eqP Hxs' Hxs.
    case: xs Hxs Hxs' => [ //=  | x0 xs] Hxs Hxs'.
      case: n IHn => //= n IHn.
      by move: IHn; move/eqP: (Hxs) => {1}<-; rewrite ltnn.
      by move/eqP: (Hxs) => {1}<- //=.
    move/eqP: (Hxs) =>  [] Hxlen.
    have Hxlen': (size (x0 :: xs) == m). by [].
    rewrite -{1}(addn1 n) -{1}(addn1 m) ltn_add2r => Hnltm Hfful.
    move: (IHm (x0 :: xs) Hxlen' n Hnltm) => [].
    move: (fixlist_length_bounds (Tuple Hxlen')).
    move: Hfful; rewrite /fixlist_is_full/fixlist_length//=.
    by case x=> //=; rewrite fixlist_coerce_none => /eqP ->; rewrite ltnn.
    move=> x' Hgnth; exists x'.
    by rewrite (@fixlist_get_nth_coerce m (Tuple Hxs') x n) => //=.
  Qed.

  Lemma fixlist_get_nth_base m (ls : fixlist m) a :
    m > 0 ->
    fixlist_get_nth (fixlist_enqueue (Some a) ls).1 0 = Some a.
  Proof.
    move: ls a => []; elim: m => [//=| ] m IHm [//= | x xs] Hxxs a.
    rewrite ltnS leq_eqVlt => /orP [/eqP Hm0 | H0ltm].
      by move: Hxxs; rewrite -Hm0 => //= .
    rewrite /fixlist_enqueue/ntuple_tail/ntuple_head/thead//=.
    rewrite -/fixlist_enqueue (tnth_nth x) //=.
    move: (behead_tupleP _) => //= Hlen.
    rewrite /fixlist_get_nth //=.
    move: (erefl (tnth  _ _)) => //=.
    by case: (fixlist_enqueue _) => //=.
  Qed.


  Lemma fixlist_get_nth_increment m (ls : fixlist m) n x :
    n.+1 < m ->
    fixlist_get_nth ls n = fixlist_get_nth (fixlist_enqueue x ls).1 n.+1.
  Proof.
    move: ls x n => []; elim: m => [//= | ] m IHm [//= | y ys] Hys x n Hltn.
    move: Hltn (Hltn); rewrite -{1}(addn1 n) -{1}(addn1 m) ltn_add2r => Hltnm Hltn.
    case: n Hltnm Hltn => [ | n ]//= Hltnm Htln .
      rewrite /ntuple_head/ntuple_tail/thead//= (tnth_nth y) //=.
      move: (behead_tupleP _) => //= Hlen.
      case Henq: (fixlist_enqueue _) => //= [[ls Hls] l].
      rewrite fixlist_get_nth_coerce//=.
      rewrite {2}/fixlist_get_nth //=.
      move: (erefl _).
      rewrite {2 3}Hltnm => //= Htmp.
      rewrite (proof_irrelevance _ Htmp Hltnm); clear Htmp.
      case: ls Hls Henq => [ | k ks].
        by move=> //= Hls; move: Hls (Hls) => /eqP Hm0;  move: Hltnm (Hltnm); rewrite -{1}Hm0.
      move=> Hls Henq.
      rewrite (tnth_nth k) => //=.
      have: (match k as o return (k = o -> option A) with
                | Some s => fun _ : k = Some s => Some s
                | None => fun _ : k = None => None
              end (erefl k)) = k. by case k => //=.
      move=> ->.
      have Hsm: (0 < m.+1). by[].
      rewrite /fixlist_get_nth//=; move:(erefl _) => Hprf.
      rewrite (tnth_nth y) //=.
      have: (match y as o return (y = o -> option A) with
              | Some s => fun _ : y = Some s => Some s
              | None => fun _ : y = None => None
            end (erefl y)) = y. by case y => //=.
      move=> ->.
      move: Henq; rewrite /fixlist_enqueue.
      rewrite /ntuple_head/thead /ntuple_tail//=.
      case: m Hlen Hls Hsm Hprf Hltnm Htln IHm Hys => //=.
      move=> m Hlen Hls Hsm Hprf Hltnm Htln IHm Hys .
      rewrite -/fixlist_enqueue.
      by case: (fixlist_enqueue _) => //= ls0 ls1 [].
    have Hyspred: size ys == m. by move: Hys => //=.
    rewrite (@fixlist_get_nth_coerce m (Tuple Hyspred)) //=.
    rewrite (IHm _ _ y) => //=.
    rewrite /ntuple_head/thead/ntuple_tail //= (tnth_nth y) //=.
    move: (behead_tupleP _) => //= Htmp; rewrite (proof_irrelevance _ Htmp Hyspred).
    case: (fixlist_enqueue _) => //= [[ls Hls]].
    by rewrite fixlist_get_nth_coerce //=.
  Qed.

  Lemma fixlist_get_nth_final m (ls : fixlist m)  x :
    0 < m -> 
    fixlist_get_nth ls (m.-1) = (fixlist_enqueue x ls).2.
  Proof.
    move: ls x => []; elim: m => [//=  | m IHm [//=| y ys] ] Hprf x .
    rewrite ltnS leq_eqVlt => /orP [/eqP Hme0 | Hmlt].
      move: Hprf; rewrite -Hme0 => //= Hprf.
      move: Hprf (Hprf) => /eqP [] /size0nil Hy0 Hprf.
      rewrite /fixlist_get_nth/ntuple_head//=/thead !(tnth_nth y) //=.
      by move: (erefl _); case: y => //=.
    case: m Hmlt Hprf IHm => [//= | m ] Hmlt Hprf IHm.
    move: Hprf.
    have: (m.+2.-1 = m.+1.-1.+1). by [].
    move=> -> Hprf.
    have Hys: size ys == m.+1. by move: Hprf => //=.
    move: (@fixlist_get_nth_coerce m.+1 (Tuple Hys) y m.+1.-1) => //= ->.
    have: m = m.+1.-1. by [].
    move=> {3}->.
    rewrite (IHm _ _ x) => //=.
    rewrite /ntuple_head/ntuple_tail/thead //= .
    move: (behead_tupleP _) => //=  Hsize.
    move: (behead_tupleP _) => //= Hsize'.
    move: (behead_tupleP _) => //= Hsize''.
    rewrite (@tnth_nth m.+2 _ y) //=.
    case: ys Hprf Hys Hsize Hsize' Hsize'' => //= y' ys.
    move=> Hprf Hys Hsize Hsize' Hsize'' .
    rewrite (proof_irrelevance _ Hsize' Hys); clear Hsize'.
    rewrite (proof_irrelevance _ Hsize'' Hsize); clear Hsize''.
    by case: (fixlist_enqueue _ ) => //=.
  Qed.


  (* A couple of nicer forms of the lemmas for use in the main proof *)

  Lemma fixlist_get_nthP_base (P : option A -> Prop) m (ls ls' : fixlist m)  a :
    m > 0 ->
    ls' = (fixlist_enqueue (Some a) ls).1 ->
    P (Some a) ->
    P (fixlist_get_nth ls' 0).
  Proof.
    move=> Hmvld -> Hbase .
    by rewrite fixlist_get_nth_base //=.
  Qed.

  Lemma fixlist_get_nthP_increment (P : option A -> Prop) m (ls ls' : fixlist m) n k x :
    n.+1 < m ->
    k = n.+1 ->
    ls' = (fixlist_enqueue x ls).1 ->
    P (fixlist_get_nth ls n) ->
    P (fixlist_get_nth ls' k).
  Proof.
    by move=> Hnvld -> -> Hbase; rewrite -fixlist_get_nth_increment.
  Qed.

  Lemma fixlist_get_nthP_final (P : option A -> Prop) m (ls : fixlist m) n x a :
    0 < m -> 
    n = m.-1 ->
    a = (fixlist_enqueue x ls).2 ->
    P (fixlist_get_nth ls n) ->
    P (a).
  Proof.
    by move=> Hnvld -> -> Hbase; rewrite -fixlist_get_nth_final.

  Qed.


  Lemma fixlist_get_nth_empty m  n  :
    fixlist_get_nth (fixlist_empty m) n = None.
  Proof.
    rewrite /fixlist_empty.
    rewrite /fixlist_get_nth//=.
    case: {2 3}(n < m) (erefl _) => //= Hltn.
    case Htnth: (tnth _) (erefl _)=> [res]//=.
    elim: n Hltn Htnth => //= [ | n ].
      by case: m => //=.
    
    case: m => //= m  IHn Hltn.
    rewrite !(tnth_nth None) //=.
    have Hobv (a b : nat) : nth None (ncons a None [::]) b =  None.
      elim: a b => [//= | //= a IHa b].
        by case => //=.
      by case: b => //=.
    by rewrite Hobv.
  Qed.


End fixlist.


Notation "[ ls <- x ]" := (@fixlist_insert _ _ ls x).
Notation "[ x -> ls ]" := (@fixlist_enqueue _ _ x ls).
Notation "[length  ls ]" := (@fixlist_length _ _ ls).
Notation "[unwrap  ls ]" := (@fixlist_unwrap _ _ ls).
Notation "[unwrap  ls <- x ]" := (@fixlist_unwrap _ _ (@fixlist_insert _ _ ls x)).
Notation "[unwrap  x -> ls ]" := (@fixlist_unwrap _ _ (@fixlist_enqueue _ _ x ls)).
Notation " ls <::< x " := (rcons ls x) (at level 50).




