(** * Structures/BloomFilter/BloomFilter_Probability.v
-----------------

Proves the standard properties required to instantiate the
AMQProperties interface for a Bloom Filter - i.e proving false
negative and false positive rates of a BloomFilter using the
definitions defined in
[Structures/BloomFilter/BloomFilter_Definitions.v].  *)

From mathcomp.ssreflect Require Import
     ssreflect ssrbool ssrnat eqtype fintype
     choice ssrfun seq path bigop finfun binomial.

From mathcomp.ssreflect Require Import tuple.

From mathcomp Require Import path.

From infotheo Require Import
      fdist ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

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
     Require Import InvMisc seq_ext seq_subset rsum_ext stirling tactics.

From ProbHash.BloomFilter
     Require Import BloomFilter_Definitions.



Open Scope R_scope.

Module BloomFilterProbability (Spec: HashSpec).

  Module BloomfilterCore :=  (BloomFilterAMQ Spec).
  Module BloomfilterDefinitions :=  BloomfilterCore.BloomFilterDefinitions.
  Module BasicHashVec :=  BloomfilterCore.BasicHashVec.
  Module BloomfilterAMQ :=  BloomfilterCore.AMQ.
  Module BloomfilterOperations :=  AMQ.AMQOperations (BasicHashVec)  (BloomfilterCore.AMQ).

  Export BloomfilterDefinitions.
  Export BasicHashVec.
  Export BloomfilterAMQ.
  Export BloomfilterOperations.

  Section BloomFilter.
  (**
    k - number of hashes
   *)
  Variable k: nat.
  (**
    n - maximum number of hashes supported
   *)
  Variable n: nat.
  (** k must be valid *)
  Variable Hkgt0: k >0.


  Lemma bloomfilter_add_internal_prob bf x l:
    ~~ tnth (bloomfilter_state bf) x ->
    \sum_(b in [finType of l.-tuple 'I_Hash_size.+1])
     ((tnth (bloomfilter_state (bloomfilter_add_internal b bf)) x %R) *R*
      ((Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l)) = 
    (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l)).
  Proof.
    elim: l x bf=> [|l IHl] x bf Hnth //=.
    - {
        by rewrite rsum_empty mulR1 subRR;
             move/Bool.negb_true_iff: Hnth => //= ->; rewrite //= mul0R add0R.     
      }
    - {
        rewrite rsum_tuple_split rsum_split//=.
        rewrite (bigID (fun a => a == x)) big_pred1_eq //=.

        under eq_bigr => b _ do
        (rewrite bloomfilter_add_internal_preserve; first rewrite mul1R;
          last by rewrite /bloomfilter_set_bit/bloomfilter_state FixedList.tnth_set_nth_eq).            
        rewrite bigsum_card_constE//=.
        under eq_bigr => i Hneq do under eq_bigr => ? _ do rewrite mulRA mulRC mulRA mulRC.
        under eq_bigr => i Hneq do (rewrite -rsum_Rmul_distr_l; under eq_bigr => ? _ do rewrite mulRC).
        under eq_bigr => i Hneq do ( rewrite IHl; last by rewrite (FixedList.tnth_set_nth_neq) //=  eq_sym).
        rewrite bigsum_card_constE//= card_tuple  cardC1 card_ord //=.
        have->: (((Hash_size.+1 ^ l %R) *R*
                  (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) =
                 Rdefinitions.Rinv (Hash_size.+1 %R)
                ).
        {
          rewrite -{3}(mulR1 (Rdefinitions.Rinv _)) mulRA mulRC mulRA mulRC ; apply f_equal.
          rewrite -natRexp; clear; elim: l => [|l IHl] //=; rewrite ?mulR1//=.
          transitivity (
              (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Hash_size.+1 %R)) *R*
              (((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R* (((Hash_size.+1 %R) ^R^ l)))
            ).
          {
            rewrite -mulRA -mulRA mulRC mulRA mulRC; apply f_equal.
            rewrite  mulRC mulRA mulRC; apply f_equal.
              by rewrite mulRC.                    
          }
          rewrite !Raxioms.Rinv_l ?mul1R ?IHl //=.
            by apply RIneq.not_0_INR =>//=.
        }
        rewrite !RIneq.Rmult_minus_distr_l addRA //= mulR1.
        rewrite -{1}(mul1R (Rdefinitions.Rinv _)) -RIneq.Rmult_plus_distr_r.
        have: (Rdefinitions.IZR 1 = (1 %R)); last move=>->; first by [].
        rewrite -natRD add1n RIneq.Rinv_r //= .
        rewrite addR_opp mulRA.
        have->: (((Hash_size %R) *R* Rdefinitions.Rinv (Hash_size.+1 %R))) =
        ((1 %R) -R- Rdefinitions.Rinv (Hash_size.+1 %R)).
        {
          rewrite -{2}(mulR1 (Rdefinitions.Rinv _)) //=.
          have: (1 %R) = Rdefinitions.IZR 1; last move=>->; first by [].
          rewrite -{1}(RIneq.Rinv_r (Hash_size.+1 %R)).
          rewrite [(_.+1 %R) *R* Rdefinitions.Rinv _]mulRC.
          rewrite -(RIneq.Rmult_minus_distr_l).
          have: (Rdefinitions.IZR 1 = (1 %R)); last move=>->; first by [].
            by rewrite -natRB //= subn1 //= mulRC.              
              by apply RIneq.not_0_INR =>//=.
        }
        have->: (1 %R) = Rdefinitions.IZR 1; by [].
          by apply RIneq.not_0_INR =>//=.        
      }
  Qed.


  Lemma bloomfilter_addn (hashes: AMQHash (n,k.-1)) (ind: 'I_(Hash_size.+1)) (bf: AMQState I) (value: B):
    (* provided the bloom filter is not full *)
    AMQHash_hashstate_available_capacity hashes 1 ->
    (* and that the bloom filter has not set the value *)
    AMQHash_hashstate_unseen hashes value ->
    (* the bit in question is not set  *)
    ~~ bloomfilter_get_bit ind bf ->
    P[
        (
          (* bf' is the result of inserting into bf *)
          res <-$ AMQ_add  bf hashes value;
            let: (new_hashes, bf') := res in
            (* the probability of the given bit being set is *)
            ret (~~ bloomfilter_get_bit ind bf')
        )
      ] = 
    ((1 -R- Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ k).
  Proof.
    rewrite /AMQ_add/AMQHash_hashstate_available_capacity
            /AMQHash_hashstate_unseen/HashVec.hash_unseen
            /hash_not_full /bloomfilter_get_bit  => /allP Hnfl /allP Husn Hunset //= .  
    time comp_normalize.
    time comp_simplify.
    rewrite exchange_big //=.
    move: (Hpredkvld Hkgt0).
    move:  Hkgt0 hashes Hnfl Husn; rewrite /AMQHash //=.
    elim: k   => //=; clear k Hkgt0; case=> [ _  |k IHk] Hkgt0 hashes Hnfl Husn.
    {
      - move=> _ //=.
        rewrite mulR1.
        comp_normalize.
        rewrite /HashVec.Hash.hash/HashVec.Hash.hashstate_find.
        have Hthead: (thead hashes) \in hashes; first by clear; rewrite (tuple_eta hashes) theadE//=; apply mem_head. 
        move/eqP: (Husn (thead hashes) Hthead) ->.
        rewrite exchange_big (bigID (fun values'' => values'' == ind)).
        have H x y z: y = (0 %R) -> x = z -> y +R+ x = z; first by move=> -> ->; rewrite add0R.
        apply H.
        {
          - apply prsumr_eq0P => ind' /eqP ->; first by dispatch_Rgt.
            move: (@bloomfilter_add_internal_hit bf ind (ind :: [::]) );
              rewrite/bloomfilter_state/bloomfilter_add_internal => //= ->.
            apply prsumr_eq0P => i' _; first by dispatch_Rgt.
              by rewrite mul0R.
                by apply mem_head.
        }
        transitivity ( 
          \sum_(i in 'I_Hash_size.+1 | i != ind)
           \sum_(i0 in hashstate_of_finType n)
           ((d[ rnd <-$ gen_random; ret (hashstate_put n value rnd (thead hashes), rnd)]) (i0, i))
        ).
        {
          - apply eq_bigr => ind' /andP [_ Hnind].
            apply eq_bigr => vl _.
            move: (@bloomfilter_add_internal_miss  bf ind (ind' :: [::])); rewrite /bloomfilter_state/bloomfilter_add_internal => //= ->.
              by rewrite eq_refl //= mul1R.
                by [].
                  by rewrite mem_seq1 eq_sym. 
        }
        comp_normalize.
        comp_simplify.
        apply prsumr_sans_one => //=.
          by rewrite card_ord.
          rewrite bigsum_card_constE card_ord RIneq.Rinv_r //=.
            by apply RIneq.not_0_INR => //=.
    }
    (* Base case completed *)           
    - {
        move=> Hpredkvld.
        rewrite -(IHk _ (FixedList.ntuple_tail hashes)); clear IHk; last first.
        { - by rewrite -pred_Sn. }
        {
          - destruct hashes eqn: Hhashes => ls.
            clear Hnfl; move: tval i Hhashes Husn => [//= | x [//=| y xs]] Hprf Heq Hnfl.
            rewrite FixedList.ntuple_tail_coerce => Hin; apply Hnfl => //=.
              by move: Hin; rewrite [ls \in [:: x, y & xs]]in_cons /tval => ->; rewrite Bool.orb_true_r.
        }
        {
          - destruct hashes eqn: Hhashes => ls.
            clear Husn; move: tval i Hhashes Hnfl => [//= | x [//= | y xs]] Hprf Heq Husn.
            rewrite FixedList.ntuple_tail_coerce => Hin; apply Husn => //=.
              by move: Hin; rewrite [ls \in [:: x, y & xs]]in_cons /tval => ->; rewrite Bool.orb_true_r.
        }
        { - by apply ltn0Sn. }
        {
          move=> //=.
          comp_normalize.
          move=>//=.
          comp_simplify_n 1.
          comp_simplify_n 1.
          exchange_big_outwards 3.
          apply eq_bigr => result _.
          exchange_big_outwards 2 => //=.
          rewrite rsum_Rmul_distr_l.
          apply eq_bigr => exp_hashes _.
          rewrite rsum_Rmul_distr_l.
          exchange_big_outwards 2.
          apply eq_bigr => exp_hashes' _//=.
          rewrite rsum_Rmul_distr_l.
          exchange_big_outwards 2.
          apply eq_bigr => inds _//=.
          apply Logic.eq_sym.
          comp_normalize=> //=.
          rewrite mulRA mulRC -!mulRA.
          apply Logic.eq_sym.
          under_all ltac:(rewrite  !mulRA mulRC mulRA mulRC).
          under eq_bigr do rewrite -rsum_Rmul_distr_l;  rewrite -rsum_Rmul_distr_l.
          apply f_equal => //=.
          under eq_bigr do rewrite -rsum_Rmul_distr_l;  rewrite -rsum_Rmul_distr_l.
          apply f_equal => //=.
          apply Logic.eq_sym.
          have H:(thead hashes \in hashes); first by rewrite (tuple_eta hashes) in_cons theadE eq_refl //=.
          under_all ltac:(rewrite  /HashVec.Hash.hash/HashVec.Hash.hashstate_find; move/eqP: (Husn _ H) => ->); clear H.
          comp_normalize.
          comp_simplify.
          rewrite (bigID (fun i => i == ind)) //=.      
          apply Logic.eq_sym.
          have H x y z: x = (0 %R) -> y = z -> x +R+ y = z; first by move=> -> -> //=; rewrite add0R.
          apply H.
          {
            - apply prsumr_eq0P => i /eqP ->; first by do?dispatch_eq0_obligations.
              rewrite eq_sym eqb_id/AMQ_add_internal//=.
              rewrite bloomfilter_add_internal_preserve; first by rewrite //= mul0R.
              rewrite bloomfilter_set_bitC.
              rewrite/bloomfilter_state/bloomfilter_set_bit//=.
              by rewrite tnth_set_nth_eq //=.
          }
          under eq_bigr => ? ? do rewrite eq_sym eqb_id.
          apply Logic.eq_sym; rewrite  eq_sym eqb_id; apply Logic.eq_sym.
          case Hind: (ind \in result).              
          {
            - rewrite !bloomfilter_add_internal_hit //= ?mulR0.
              apply prsumr_eq0P => hshs' _; first (by do ?dispatch_eq0_obligations).
                rewrite bloomfilter_add_internal_hit //= ?mul0R //=.
                by rewrite !in_cons Hind !Bool.orb_true_r.
                by rewrite !in_cons Hind !Bool.orb_true_r.
          }
          case Hres: (inds == ind).
          {
            rewrite /AMQ_add_internal //=.
            move/eqP:Hres ->; rewrite bloomfilter_add_internal_preserve;
              last by move: (bloomfilter_set_get_eq ind bf); rewrite /bloomfilter_get_bit.
            rewrite //= mulR0.
            apply prsumr_eq0P => i Hineq;  first by do?dispatch_eq0_obligations.
            rewrite bloomfilter_add_internal_preserve; first (by rewrite //= mul0R);
              last by move: (bloomfilter_set_get_eq ind (bloomfilter_set_bit i bf)); rewrite /bloomfilter_get_bit.
          }
          rewrite /AMQ_add_internal //=.
          rewrite bloomfilter_add_internal_miss; [
          | by move/Bool.negb_true_iff:
                 Hres => Hres; rewrite/bloomfilter_state/bloomfilter_set_bit tnth_set_nth_neq 1?eq_sym//=
          | by move/Bool.negb_true_iff:Hind]; rewrite mulR1.
          under eq_bigr => i Hi.
          {
            rewrite bloomfilter_add_internal_miss;
              by [ rewrite //= mul1R; over
                 | move/Bool.negb_true_iff:
                     Hres => Hres; rewrite/bloomfilter_state/bloomfilter_set_bit !tnth_set_nth_neq 1?eq_sym //=
                 |  move/Bool.negb_true_iff:Hind ].
          }
          apply prsumr_sans_one => //=.
            by rewrite card_ord.
            rewrite bigsum_card_constE card_ord RIneq.Rinv_r //=.
              by apply RIneq.not_0_INR => //=.
        }
      }
      (* DONE!!!! *)
  Qed.

  Lemma bloomfilter_add_multiple_unfold A (hshs: AMQHash (n,k.-1)) bf x xs (f: _ -> Comp A):
    d[ res <-$ AMQ_add_multiple hshs bf (x :: xs);
         f (res) ] =
    d[
        res1 <-$ AMQ_add_multiple hshs bf xs;
          let (hshs', bf') := res1 in  
          res2 <-$ @AMQ_add _ I bf' hshs' x;
            f (res2)
      ].
  Proof.
    apply fdist_ext => a //=.
    rewrite FDistBindA //=.
      by rewrite !FDistBind.dE; apply eq_bigr => [[hshs' bf']] _; apply f_equal => //=.
  Qed.
  

  Lemma bloomfilter_add_multiple_find_preserve value  inds
        (hashes hashes': AMQHash (n,k.-1)) (bf bf': AMQState I) xs:
    AMQHash_hashstate_contains hashes  value inds ->
    ((d[ AMQ_add_multiple hashes bf xs]) (hashes', bf') != (0 %R)) ->
    hash_vec_contains_value value hashes' inds.
  Proof.
    move=> Hcontains.
    elim: xs hashes inds  Hcontains hashes' bf' => [//=| x xs IHxs] hashes inds Hcontains hashes' bf'.
    - {
        rewrite FDist1.dE xpair_eqE.
        case Hhashes: ((hashes') == _) => /eqP //= /eqP.
        case Hbf: ((bf') == _) => /eqP //= /eqP _.
          by move/eqP: Hhashes -> .
      }
    - {
        move=> //=. rewrite FDistBind.dE //= rsum_split // /AMQ_add.
        comp_possible_decompose => hashes_internal' bf_prev Heq0.
        rewrite/AMQHash_hash //.
        have H (T T1 T2:finType) (f: Comp T)
             (g: T -> Comp [finType of (T1 * T2)]) a b:
          ((d[ hash_res <-$ f; (g hash_res)])) (a,b) =
          FDistBind.d (d[ f]) (fun b0 : T => d[ g b0]) (a, b); first by [].
        rewrite H; clear H; rewrite FDistBind.dE rsum_split //.
        comp_possible_decompose => inds' inds''.
        have H: (let x0 := (inds', inds'') in
                 (d[ HashVec.hash_vec_int x hashes_internal']) x0 *R*
                 (d[ let (new_hashes, hash_vec) := x0 in
                     ret (new_hashes, AMQ_add_internal bf_prev hash_vec)])
                   (hashes', bf')) = 
                ((d[ HashVec.hash_vec_int x hashes_internal'])
                   (inds',inds'') *R*
                 (d[ ret (inds', AMQ_add_internal bf_prev inds'')])
                   (hashes', bf')); first by [].
        rewrite H; clear H.
        comp_possible_decompose => Hhashes //=; rewrite FDist1.dE.
        move=>/bool_neq0_true; rewrite xpair_eqE=>/andP[/eqP -> _].
        move: Heq0 => //= /IHxs Heq0. 
        move: (Heq0 _ Hcontains); clear Heq0 => Hcontains_internal.
            case Hneq: (value == x).
            - {
                move: Hcontains_internal Hhashes.
                move/eqP: Hneq <- =>Hcontains_internal.
                rewrite/HashVec.Hash.hash.
                erewrite hash_vec_find_simpl =>//=; last by exact Hcontains_internal.
                move=>/eqP; rewrite RIneq.INR_IZR_INZ; case Hand: (_ && _) => //= _.
                move/andP: Hand => [/eqP ->] //=.
              }
              move/Bool.negb_true_iff: Hneq => Hneq.
              move: Hneq Hcontains_internal Hhashes; clear.
              move: k inds inds'' hashes_internal' inds';clear k.
              rewrite /AMQHashValue/AMQHash => k.
              change ((n, k.-1).2.+1) with (k.-1.+1).
              change ((n, k.-1).1) with (n).
              elim (k.-1.+1) => [ //=| ]; clear k; last move=> k IHk.
            - {
                do 5!intro; rewrite !tuple0 //= FDist1.dE xpair_eqE => H3.
                by move=>/bool_neq0_true/andP[/eqP -> _] //=.
              }
            - {
                move=> [[//=| ind inds] Hinds] [[//=| hash hashes] Hhashes] [[//=| hash' hashes'] Hhashes'].
                move=> [[//=|ind' inds'] Hinds'] Hneq.
                comp_normalize.
                  rewrite
                  (tuple_eta (Tuple Hhashes'))
                  (tuple_eta (Tuple Hinds))
                  (tuple_eta (Tuple Hhashes))
                  (tuple_eta (Tuple Hinds')).
                rewrite !ntuple_tailE theadE//=.
                have->: ( thead (Tuple Hhashes)) = hash; first by [].
                have->: ( thead (Tuple Hhashes')) = hash'; first by [].
                have->: ( thead (Tuple Hinds)) = ind; first by [].
                have->: ( thead (Tuple Hinds')) = ind'; first by [].
                rewrite/hash_vec_contains_value //= => /andP[Hfind Hcontains].
                comp_possible_decompose.
                move=> b' b hsh_val ind_val Hint Hhash .
                rewrite !xpair_eqE !cons_tuple_eq_tuple !xcons_eqE.
                move=>/bool_neq0_true/andP [/andP [/eqP Hhsheq /eqP Htupleeq] /andP [/eqP Hindeq /eqP Hindstupleeq]].
                have Hcont':
                  hash_vec_contains_value value (behead_tuple (Tuple Hhashes')) (FixedList.ntuple_tail (Tuple Hinds));
                  first by rewrite/hash_vec_contains_value //=.
                move:
                  (IHk (FixedList.ntuple_tail (Tuple Hinds))  b (behead_tuple (Tuple Hhashes')) b' Hneq Hcont' Hint);

                  clear IHk; rewrite/hash_vec_contains_value //= -Htupleeq => ->; rewrite Bool.andb_true_r.
                move:  Hneq Hfind Hhash.
                rewrite Hhsheq /HashVec.Hash.hash; clear.
                case: ( HashVec.Hash.hashstate_find n x hash') => //=.
                - {
                    move=> ind_val' Hneq; rewrite FDist1.dE xpair_eqE=> Hfind'/eqP.
                    case Hand: (_ && _) => //= _.
                      by move/andP: Hand => [/eqP ->] //=.
                  }
                - {
                    move=> Hneq Hfind //=; comp_normalize.
                    comp_possible_decompose.
                    move=> ind1 ind2 /bool_neq0_true; rewrite xpair_eqE=>/andP[/eqP-> /eqP <-] _/bool_neq0_true/eqP ->.
                    move: Hneq Hfind; clear.
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
                          by rewrite ntuple_head_consE eq_refl.                                  }
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
                              by rewrite ntuple_head_consE Heq ntuple_tail_consE.
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
  Qed.            

  Lemma bloomfilter_add_multiple_preserve x xs l m hshs hshs' bf bf'
        (Huniq: uniq (x :: xs))
        (Hlen: length xs == l) 
        (Hfree: hashes_have_free_spaces hshs  ((l+m).+1))
        (Huns:      all (hashes_value_unseen hshs) (x :: xs)):
    ((d[ @AMQ_add_multiple (n,k.-1) I hshs bf xs]) (hshs', bf') != (0 %R)) ->
    (hashes_have_free_spaces hshs' (m.+1)) && (hashes_value_unseen hshs' x).
  Proof.
    (* First clean up the proof *)
    move: hshs hshs' bf bf' Hfree Huns.
    rewrite/AMQHash/AMQState.
    change ((n, k.-1).2.+1) with (k.-1.+1).
    change ((n, k.-1).1) with n.
    move => hshs hshs' bf bf' Hfree Huns.
    move=> //=.
    rewrite -all_predI /predI //=.
    move: m hshs Hfree Huns bf bf' hshs'.
    move/eqP: Hlen <-; clear l.
    have all_cons P y ys : all P (y :: ys) =  P y && all P ys. by [].
    move=> m hshs Hfree; rewrite all_cons => /andP []; move: x m hshs Huniq Hfree; clear all_cons.
    rewrite/hashes_have_free_spaces/hash_has_free_spaces/hashes_value_unseen/hash_unseen.
    (* proof has been cleaned up *)
    elim: xs => [//= | y ys IHy] x m hshs Huniq /allP Hfree /allP Huns Hx  bf bf' hshs'.
    - comp_normalize=>/bool_neq0_true; rewrite xpair_eqE =>/andP[/eqP -> _].
      apply /allP=> hsh Hin //=; apply/andP; split; by [apply Hfree | apply Huns].
    - move: Hx; have all_cons P z zs : all P (z :: zs) =  P z && all P zs. by [].
      rewrite all_cons => /andP [/allP Hfindy /allP Hfindys].
      have H1: uniq (x :: ys); first
        by move: Huniq => //=/andP [Hcons /andP [_ ->]]; move: Hcons; rewrite !in_cons Bool.negb_orb=>/andP[_ ->].
      have H2: all (fun hsh : HashState n => FixedList.fixlist_length hsh + (length ys + m.+1).+1 <= n) hshs;
        first by apply/allP => vec Hvec; move: (Hfree vec Hvec) => //=; rewrite addSn !addnS.
      have H3: all (fun hsh : HashState n => FixedMap.fixmap_find x hsh == None) hshs;
        first by apply /allP.
      have H4: all (fun b : B => all (fun hsh : HashState n => FixedMap.fixmap_find b hsh == None) hshs) ys;
        first by apply/allP.
      move: (IHy x m.+1 hshs H1 H2 H3 H4); clear IHy H1 H2 H3 H4 => IHy.
      move=>//=; rewrite FDistBind.dE rsum_split //.
      comp_possible_decompose => d_hshs' d_bf.

      have ->:
        (let x0 := (d_hshs', d_bf) in
         (d[ @AMQ_add_multiple (n,k.-1) I hshs bf ys]) x0 *R*
         (d[ let (hsh, bf0) := x0 in @AMQ_add (n,k.-1) I bf0 hsh y]) (hshs', bf')) =
        ((d[ @AMQ_add_multiple (n,k.-1) I hshs bf ys]) (d_hshs',d_bf) *R*
         (d[ @AMQ_add (n,k.-1) I d_bf d_hshs' y]) (hshs', bf')); first by [].
      rewrite /AMQ_add.
      have H (T T1 T2:finType) (f: Comp T)
             (g: T -> Comp [finType of (T1 * T2)]) a b:
          ((d[ hash_res <-$ f; (g hash_res)])) (a,b) =
          FDistBind.d (d[ f]) (fun b0 : T => d[ g b0]) (a, b); first by [].
      rewrite H; clear H.
      rewrite FDistBind.dE.
      rewrite mulR_neq0' => /andP[ Haddm ].
      comp_possible_decompose => [[d_hshs'' d_ind]].
      rewrite/AMQHash_hash => Hint //=.
      comp_normalize.
      move: Haddm Hint.
      move=>/(IHy).
      clear IHy all_cons bf Hfree Huns Hkgt0 Hfindys .
      move=> Hall Hint /bool_neq0_true; rewrite xpair_eqE=>/andP[/eqP -> _].
      clear hshs'.
      move: k d_hshs' d_hshs'' d_ind Hint Hall; clear hshs Hfindy k=>k.
      rewrite/AMQHash/AMQState/AMQHashValue.
      change ((n, k.-1).2.+1) with (k.-1.+1).
      change ((n, k.-1).1) with n.
      elim: (k.-1.+1); clear k.
    - by move=> hs1 hs2 vec1 //=; comp_normalize => /bool_neq0_true; rewrite xpair_eqE=>/andP[/eqP -> _] //=.
    - move=> k IHk hs1 hs2 vec1 //=; comp_normalize; comp_possible_decompose.
      move=> hs3 vec2 state1 ind1.
      move=>/IHk;clear IHk => IHk Hhash /bool_neq0_true; rewrite xpair_eqE => /andP[/eqP -> _ ] //= Hall.
      move: Hhash; rewrite/HashVec.Hash.hash/HashVec.Hash.hashstate_find.
      have Hthead: (thead hs1 \in hs1); first by rewrite (tuple_eta hs1) theadE in_cons eq_refl //=.
      case: (FixedMap.fixmap_find _ _) => [val //=|]. 
      - {
          comp_normalize => /bool_neq0_true; rewrite xpair_eqE => /andP[/eqP -> _]; apply/andP; split => //=.
          - by move/allP: Hall => /(_ _ Hthead) //=; rewrite !addnS => /andP [/ltnW -> ->] //=.
          -  apply IHk; apply/allP => v Hin; move/allP:Hall => Hall; apply/Hall.
             by move: Hin; rewrite (tuple_eta hs1) ntuple_tailE in_cons => ->; apply/orP; right.
      }
      - {
          comp_normalize; comp_possible_decompose
          => ind2 ind3 /bool_neq0_true;rewrite xpair_eqE=>/andP[/eqP -> Hind'] Hinv /bool_neq0_true/eqP ->.
          apply/andP;split;last first.
          - apply IHk; apply/allP => v Hv //=; move/allP:Hall => Hall; apply/Hall.
              by move: Hv; rewrite (tuple_eta hs1) ntuple_tailE in_cons => ->; apply/orP; right.
          - move/allP: Hall => /(_ _ Hthead) //= /andP[].
            rewrite !addnS -addSn addnC -ltn_subRL => Hlen Hfind; apply/andP;split.
            {
              rewrite addnC -ltn_subRL.
              apply (@leq_ltn_trans  (FixedList.fixlist_length (thead hs1)).+1) => //=.              
              clear Hlen IHk Hthead hs2 hs3 state1; move: (thead _) => [ls Hls]; clear hs1 Hfind.
              elim: n ls Hls => [//=|]; clear n => n IHn [//=|l ls] Hls //=.
              have->: (FixedList.ntuple_head (Tuple Hls)) = l; first by [].
              case: l Hls => [[k' v']|] Hls; last first; last case Heq: (_ == _).
              - by move: Hls (eq_ind _ _ _ _ _) => //=. 
              - by move: Hls (eq_ind _ _ _ _ _) => //= Hls Hls'. 
              - {
                  rewrite /FixedList.ntuple_tail; move: (behead_tupleP _) => //= Hls'.
                  move: (IHn ls Hls') => IHn'.
                  rewrite/FixedList.fixlist_length/FixedList.ntuple_cons.
                    by case Hput: ( HashVec.Hash.hashstate_put _) => [ms Hms] //=; move: IHn';rewrite Hput.
                }
            }
            {
              rewrite /hashstate_put.
              move: Huniq => //=/andP[];rewrite in_cons Bool.negb_orb=>/andP[Hneq _ _].
                by rewrite fixmap_find_neq //=. 
            }
        }
  Qed.


  Lemma bloomfilter_addn_Nuns  ind bf hashes x :
    bloomfilter_get_bit ind bf ->
    (d[ res <-$ @AMQ_add (n,k.-1) I bf hashes x;
          (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true = (0 %R).
  Proof.
    move: hashes bf; rewrite /AMQHash/AMQ_add/AMQHash_hash/AMQ_add_internal/AMQHashValue.
    change  (AMQHash (n, k.-1)) with ([finType of k.-1.+1.-tuple (HashVec.Hash.HashState n)]).
    change ((n, k.-1).2.+1) with (k.-1.+1).
    change ((n, k.-1).1) with n.
    rewrite (@prednK k Hkgt0).
    move=> hashes bf.
    move=> Htnth; comp_normalize.
    comp_impossible_decompose.
    move=> hashes' _ bf' _ hashes'' _ hvec _ Hnbit /eqP <- /eqP Hbf; clear hashes''.
    move: Hbf Hnbit => ->; clear bf'.
    rewrite/bloomfilter_get_bit.
      by rewrite bloomfilter_add_internal_preserve //=.
  Qed.
  
  

  Lemma bloomfilter_addn_insert_multiple hashes l (ind: 'I_Hash_size.+1) (bf: BloomFilter) (values: seq B):
    length values == l ->
    hashes_have_free_spaces hashes l ->
    all (hashes_value_unseen hashes) values ->
    uniq values ->
    ~~ bloomfilter_get_bit ind bf ->
    (d[ res <-$ @AMQ_add_multiple (n,k.-1) I  hashes bf values;
          (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true =
    ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k * l)).
  Proof.
    move: hashes bf bloomfilter_add_multiple_preserve bloomfilter_addn bloomfilter_addn_Nuns ;
      rewrite /AMQHash/AMQ_add/AMQHash_hash/AMQ_add_internal/AMQHashValue;
    rewrite/AMQHash_hashstate_available_capacity/AMQHash_hashstate_unseen.
    change  (AMQHash (n, k.-1)) with ([finType of k.-1.+1.-tuple (HashVec.Hash.HashState n)]).
    change ((n, k.-1).2.+1) with (k.-1.+1).
    change ((n, k.-1).1) with n.
    move=> hashes bf bloomfilter_add_multiple_preserve bloomfilter_addn bloomfilter_addn_Nuns .
    elim: l ind bf values hashes => [|l IHl] ind bf values hashes0 .
    {
      case: values => //= _ _ _ _ Htnth; rewrite muln0; comp_normalize.
      - by comp_simplify; rewrite eq_sym eqb_id; rewrite Htnth.
    }
    {
    - rewrite mulnS.
      case: values => [//= | x xs] Hlen Hfree Huns Huniq Hnb.
      rewrite bloomfilter_add_multiple_unfold.
      rewrite RealField.Rdef_pow_add.
      erewrite <- (IHl ind bf xs hashes0) => //=; clear IHl.
      rewrite mulRC.
      rewrite FDistBind.dE rsum_split.
      move: bloomfilter_addn_Nuns  (bloomfilter_add_multiple_preserve x xs l 0 hashes0) bloomfilter_addn; clear bloomfilter_add_multiple_preserve.
      rewrite/AMQ_add_multiple/AMQState/AMQ_add/AMQ_add_internal/AMQHash_hash.
      change  (AMQHash (n, k.-1)) with ([finType of k.-1.+1.-tuple (HashVec.Hash.HashState n)]).
      change  (AMQHashValue (n, k.-1)) with ([finType of k.-1.+1.-tuple 'I_Hash_size.+1]).
      change ((n, k.-1).2.+1) with (k.-1.+1).
      change ((n, k.-1).1) with n.
      move: hashes0 Hfree Huns .
      rewrite (@prednK k Hkgt0).
      move=> hashes0 Hfree Huns bloomfilter_addn_Nuns bloomfilter_add_multiple_preserve bloomfilter_addn.
      comp_normalize.
      exchange_big_outwards 2 => //=; exchange_big_outwards 3 => //=.
      comp_simplify_n 1.
      comp_simplify_n 1.
      apply eq_bigr => hshs' _; apply eq_bigr => bf' _.
      move=>//=.
      under eq_bigr do rewrite -rsum_Rmul_distr_l; rewrite -rsum_Rmul_distr_l.
      move: (@bloomfilter_add_multiple_preserve hshs' bf bf'); clear bloomfilter_add_multiple_preserve.
      set bloomfilter_add_multiple :=
        foldr
         (fun val : AMQHashKey =>
          (Bind
             (B:=[finType of k.-tuple (HashVec.Hash.HashState n) *
                             BloomfilterCore.BloomFilterDefinitions.BloomFilter]))^~ 
          (fun
             res_1 : k.-tuple (HashVec.Hash.HashState n) *
                     BloomfilterCore.BloomFilterDefinitions.BloomFilter =>
           let (hsh, bf0) := res_1 in
           hash_res <-$ HashVec.hash_vec_int val hsh;
           (let (new_hashes, hash_vec) := hash_res in
            ret (new_hashes,
                BloomfilterCore.BloomFilterDefinitions.bloomfilter_add_internal hash_vec bf0))))
         (ret (hashes0, bf)) xs.        
      move=> bloomfilter_add_multiple_preserve.
      case Hnz: (d[ bloomfilter_add_multiple ] (hshs', bf') == (0 %R));
        first by move/eqP: Hnz ->; rewrite !mul0R mulR0.
      move/Bool.negb_true_iff: Hnz => Hnz.
      move: Hfree; rewrite -(addn0 l) => Hfree.
      move: (bloomfilter_add_multiple_preserve  Huniq Hlen Hfree Huns Hnz) => /andP [].
      rewrite /hashes_have_free_spaces/hashes_value_unseen => Hfree' Huns'.
      apply Logic.eq_sym; rewrite mulRA mulRC mulRA mulRC; apply f_equal; apply Logic.eq_sym.
      case Htnth': (~~ bloomfilter_get_bit ind bf').
    - have <-: (Rdefinitions.IZR 1) = (BinNums.Zpos BinNums.xH); first by [].
      erewrite <-  (@bloomfilter_addn hshs' ind bf' x) => //=.
      by apply Logic.eq_sym; comp_normalize; comp_simplify_n 2; apply Logic.eq_sym; comp_simplify_n 1.
    - move /Bool.negb_false_iff: Htnth' => Htnth'; rewrite FDist1.dE // mul0R.
       by move: (@bloomfilter_addn_Nuns ind bf' hshs' x Htnth'); comp_normalize; comp_simplify.
    - move/allP: Hfree => Hfree; apply/allP => cell Hcell.        
    - move: (Hfree cell Hcell); rewrite /hash_has_free_spaces.
        by rewrite addnS => /ltnW.
    - move /allP: Huns => Huns; apply/allP => x' Hx'.
    - apply Huns => //=.
        by rewrite in_cons Hx' Bool.orb_true_r.
          by move: Huniq => //= /andP [].
    }
  Qed.
  

  Lemma bloomfilter_add_internal_indep l bf' x xs :
    tnth (bloomfilter_state bf') x ->
    uniq (x :: xs) ->
    length (x::xs) < Hash_size.+1 ->
    \sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
     (((tnth (bloomfilter_state (bloomfilter_add_internal inds bf')) x &&
             all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs) %R) *R*
      (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) =
    ((\sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
       (((tnth (bloomfilter_state (bloomfilter_add_internal inds bf')) x) %R) *R*
        (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) *R*
     (\sum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
       ((( all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs) %R) *R*
        (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))).
  Proof.
    have H x1 y1 z1: y1 = (0 %R) -> x1 = z1 -> x1 +R+ y1 = z1. by move=> -> ->; rewrite addR0.
    elim: l bf' x xs=> [//=|l IHl] bf' x xs.
    -  move=> Htnth /andP[Hnin Huniq] Hlen.
       by comp_normalize; rewrite boolR_distr mulRC.
    - move=> Htnth Huniq Hlength.
      comp_normalize.
      rewrite rsum_tuple_split rsum_split=>//=.
      under_all ltac:(rewrite mulRC -mulRA).
      under eq_bigr => ? ? do rewrite -rsum_Rmul_distr_l.
      under eq_bigr => ? ? do under eq_bigr => ? ? do rewrite mulRC.
      under eq_bigr =>  i HI; first rewrite IHl; first over; try by [].
      {
        case Haeq: (x == i); first by
            rewrite /bloomfilter_set_bit/bloomfilter_state FixedList.tnth_set_nth_eq //=.
          by rewrite FixedList.tnth_set_nth_neq //=;  move/Bool.negb_true_iff: Haeq.        
      }
      under [  \sum_(a in [finType of (l.+1).-tuple _]) _]eq_bigr => ? ? do under eq_bigr
      => ? ? do rewrite -{1}(mulR1 (Rdefinitions.Rinv _ *R* _)) mulRC bloomfilter_add_internal_preserve //= !mulR1.
      rewrite bigsum_card_constE.
      rewrite -[\sum_(i in 'I_Hash_size.+1) _]rsum_Rmul_distr_l.
      under eq_bigr => a _; first under eq_bigr => inds _.
      {
        rewrite bloomfilter_add_internal_preserve; first (rewrite mul1R; over).
        rewrite/bloomfilter_state/bloomfilter_set_bit.
        case Haeq:(x == a); first by rewrite FixedList.tnth_set_nth_eq //=.
          by move/Bool.negb_true_iff: Haeq=>Haeq; rewrite FixedList.tnth_set_nth_neq//=.
      }
        by over.
      rewrite //= bigsum_card_constE -!rsum_Rmul_distr_l [(#| [finType of (l.+1).-tuple _] | %R) *R* _]mulRC  -!mulRA;
        apply f_equal.
      rewrite mulRA [(#| [finType of l.-tuple _] | %R) *R* _]mulRC -mulRA; apply f_equal.
      under_all ltac:(rewrite mulRC).
      under eq_bigr => ? ? do rewrite -rsum_Rmul_distr_l; rewrite -rsum_Rmul_distr_l.
      rewrite mulRA [(#|[finType of l.-tuple _]| %R) *R* _ ]mulRC -mulRA.
      apply Logic.eq_sym; under eq_bigr
      => ? ? do rewrite mulRC; rewrite -rsum_Rmul_distr_l mulRC [(Rdefinitions.Rinv _) *R* _] mulRC -!mulRA;
           apply f_equal; rewrite mulRC -mulRA mulRC; apply Logic.eq_sym.
      rewrite !card_tuple //=; rewrite expnSr card_ord natRM mulRC.
      apply Logic.eq_sym; rewrite mulRC rsum_tuple_split rsum_split //=; apply Logic.eq_sym; apply f_equal; apply Logic.eq_sym.
      rewrite -mulRA mulRC mulRV ?exp1R//= ?mul1R //=.
        by rewrite RIneq.INR_IZR_INZ; apply/eqP => //=.
  Qed.

  Lemma bloomfilter_addn_insert_multiple_inv hashes l (ind: 'I_Hash_size.+1) (bf: BloomFilter) (values: seq B):
    length values == l ->
    hashes_have_free_spaces hashes l ->
    all (hashes_value_unseen hashes) values ->
    uniq values ->
    ~~ bloomfilter_get_bit ind bf ->
    (d[ res <-$ @AMQ_add_multiple (n,k.-1) I hashes bf values;
          (let '(_, bf') := res in ret bloomfilter_get_bit ind bf')]) true =
    (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k * l))).
  Proof.
    move=> Hlen Hhashes Huns Huniq Hnth.
    transitivity (
        (d[ res <-$ @AMQ_add_multiple (n,k.-1) I hashes bf values;
            ret (fun res' => (let '(_, bf') := res' in bloomfilter_get_bit ind bf')) res]) true
      ).
    - by rewrite //= !FDistBind.dE; apply/eq_bigr=>[[hs' bf']] _ //=.
      rewrite -(prsumr_neg1 ).
      transitivity (
          (1 -R- (d[ res <-$ @AMQ_add_multiple (n,k.-1) I hashes bf values;
                     (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true)
        ).
    - by rewrite //= !FDistBind.dE; apply f_equal; apply/eq_bigr=>[[hs' bf']] _ //=.
        by rewrite (@bloomfilter_addn_insert_multiple _ l).       
  Qed.


  Lemma bloomfilter_hits_preserve (xs : seq B) (l : nat_eqType) (m : nat)
        hshs hshs'
        (bf bf' : bloomfilter_finType) inds :
   length xs == l ->
   all (bloomfilter_get_bit^~ bf) inds ->
   (d[ @AMQ_add_multiple (n,k.-1) I hshs bf xs]) (hshs', bf') != (0 %R) ->
   all (bloomfilter_get_bit^~ bf') inds.
  Proof.
    move: hshs hshs'.
    rewrite/AMQ_add_multiple/AMQState/AMQ_add/AMQ_add_internal/AMQHash_hash.
    change  (AMQHash (n, k.-1)) with ([finType of k.-1.+1.-tuple (HashVec.Hash.HashState n)]).
    change  (AMQHashValue (n, k.-1)) with ([finType of k.-1.+1.-tuple 'I_Hash_size.+1]).
    change ((n, k.-1).2.+1) with (k.-1.+1).
    change ((n, k.-1).1) with n.
    rewrite (@prednK k Hkgt0).
    move=> hshs hshs'.
    elim: l xs bf inds hshs' bf' => [//= [|//=]| l IHl [//=| x xs]] bf inds hshs' bf' Hlen Hall //=.
    - by comp_normalize =>/bool_neq0_true; rewrite xpair_eqE => /andP[_/eqP->].
    - {
        comp_normalize.
        comp_possible_decompose.
        move=> hshs1 bf1 hsh2 bf2 Haddm Hint/bool_neq0_true;rewrite xpair_eqE=>/andP[_/eqP->].
        have H1: length xs == l; first by move/eqP: Hlen => [->].
        move: Haddm; move=>/(@IHl xs _ _ hshs1 bf1 H1  Hall) //=.
        move=>/allP Hget; apply/allP => ind Hind.
        apply bloomfilter_add_internal_preserve.
        move: (Hget ind Hind) => //=.
      }
  Qed.
  
  
  Theorem bloomfilter_addn_bits
          hashes b (inds: seq 'I_Hash_size.+1) (bf: BloomFilter) (value: B):
    b < k ->
    length inds == b ->
    @AMQHash_hashstate_available_capacity (n,k.-1) hashes 1 ->
    (@AMQHash_hashstate_unseen (n,k.-1) hashes value)  ->
    uniq inds ->
    all (fun ind => ~~ bloomfilter_get_bit ind bf) inds ->
    (d[ res <-$ @AMQ_add (n,k.-1) I bf  hashes value;
          (let '(_, bf') := res in ret (all (bloomfilter_get_bit^~ bf') inds))]) true = 
    \sum_(i in tuple_finType k (ordinal_finType Hash_size.+1))
     ((((inds \subseteq i) == true) %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k)).
  Proof.
    move: hashes.
    rewrite/AMQ_add_multiple/AMQState/AMQ_add/AMQ_add_internal/AMQHash_hash/AMQHash_hashstate_available_capacity/AMQHash_hashstate_unseen.
    change  (AMQHash (n, k.-1)) with ([finType of k.-1.+1.-tuple (HashVec.Hash.HashState n)]).
    change  (AMQHashValue (n, k.-1)) with ([finType of k.-1.+1.-tuple 'I_Hash_size.+1]).
    change ((n, k.-1).2.+1) with (k.-1.+1).
    change ((n, k.-1).1) with n.
    rewrite (@prednK k Hkgt0).
    move=> hashes.
    have H x1 y1 z1: y1 = (0 %R) -> x1 = z1 -> x1 +R+ y1 = z1; first by move=> -> ->; rewrite addR0.
    move =>  //= Hb Hlen Hfree Huns Huniq Hall.
    comp_normalize; comp_simplify.
    rewrite exchange_big //=.
    under eq_bigr => i0 _ do rewrite (bigID (fun i => i == Tuple (hash_vec_insert_length value hashes i0))) big_pred1_eq //=.
    rewrite addRA_rsum.
    erewrite H; last by []; last first.
    {
      do 1!(apply prsumr_eq0P; intros; first by intros; dispatch_Rgt).
      apply prsumr_eq0P => i Hneq; first by intros; dispatch_Rgt.
        by rewrite neg_hash_vecP //=; first rewrite !mulR0.
    }
    under eq_bigr => i _ do rewrite hash_vecP //=.
    have Hpred_eq i: (all (bloomfilter_get_bit^~ (bloomfilter_add_internal i bf)) inds = all (fun ind => ind \in i) inds).
    {
      apply eq_in_all => ind Hinds.
      case HinI: (ind \in i); first by rewrite /bloomfilter_get_bit bloomfilter_add_internal_hit //=.
      apply/Bool.negb_true_iff; rewrite /bloomfilter_get_bit bloomfilter_add_internal_miss //=;
                                        first by move/allP: Hall => /(_ ind Hinds) .
        by rewrite HinI.
    }
    under eq_bigr => i _ do rewrite Hpred_eq eq_sym //=.
      by [].
  Qed.

  Lemma bloomfilter_add_multiple_unwrap_internal bf
        hashes l value (values: seq B) inds:
    length values == l ->
    @AMQHash_hashstate_available_capacity (n,k.-1) hashes (l.+1) ->
    all (@AMQHash_hashstate_unseen (n,k.-1) hashes) (value::values) ->
    \sum_(a in [finType of k.-1.+1.-tuple (HashState n) * BloomFilter])
     ((d[ @AMQ_add_multiple (n,k.-1) I (Tuple (hash_vec_insert_length value hashes inds)) bf
                                   values]) a *R*
      (d[ let (hashes2, bf) := a in res' <-$ bloomfilter_query value hashes2 bf; ret res'.2]) true) =
    \sum_(a in [finType of k.-1.+1.-tuple (HashState n) * BloomFilter])
     ((d[ @AMQ_add_multiple (n,k.-1) I (Tuple (hash_vec_insert_length value hashes inds)) bf
                                   values]) a *R*
      (bloomfilter_query_internal inds a.2 == true %R)).
  Proof.
    move: hashes inds bloomfilter_add_multiple_find_preserve.
    rewrite/AMQ_add_multiple/AMQState/AMQ_add/AMQ_add_internal/AMQHash_hash/AMQHash_hashstate_available_capacity/AMQHash_hashstate_unseen/AMQHash_hashstate_contains.
    change  (AMQHash (n, k.-1)) with ([finType of k.-1.+1.-tuple (HashVec.Hash.HashState n)]).
    change  (AMQHashValue (n, k.-1)) with ([finType of k.-1.+1.-tuple 'I_Hash_size.+1]).
    change ((n, k.-1).2.+1) with (k.-1.+1).
    change ((n, k.-1).1) with n.
    rewrite (@prednK k Hkgt0).
    move=> hashes inds bloomfilter_add_multiple_find_preserve.

    move=>  Hlen Hfree Hall; apply eq_bigr => [[hshs' bf']] _.

    move: (@bloomfilter_add_multiple_find_preserve value inds (Tuple (hash_vec_insert_length value hashes inds)) hshs' bf bf' values  ); clear bloomfilter_add_multiple_find_preserve.
    set bloomfilter_add_multiple :=
      (d[ foldr
            (fun val : AMQHashKey =>
               (Bind
                  (B:=[finType of [finType of k.-tuple (HashVec.Hash.HashState n)] *
                       [finType of BloomfilterCore.BloomFilterDefinitions.BloomFilter]]))^~ (fun res_1 : [finType of [finType of k.-tuple (HashVec.Hash.HashState n)] *
                                 [finType of BloomfilterCore.BloomFilterDefinitions.BloomFilter]] =>
           let (hsh, bf0) := res_1 in
           hash_res <-$ HashVec.hash_vec_int val hsh;
           (let (new_hashes, hash_vec) := hash_res in
            ret (new_hashes,
                BloomfilterCore.BloomFilterDefinitions.bloomfilter_add_internal hash_vec bf0))))
         (ret (Tuple (hash_vec_insert_length value hashes inds), bf)) values]).      
    move=> bloomfilter_add_multiple_find_preserve.
    case Hzro: (bloomfilter_add_multiple (hshs', bf') == 0); first by move/eqP:Hzro -> ; rewrite !mul0R.
    move/Bool.negb_true_iff: Hzro => Hzro.
    apply f_equal.
    comp_normalize; comp_simplify.
    have Hallleq: all
                    (fun hsh : FixedList.fixlist [eqType of hash_keytype * hash_valuetype] n =>
                       FixedList.fixlist_length hsh + 1 <= n) hashes.
    {
      move: Hfree;rewrite/hashes_have_free_spaces/hash_has_free_spaces=>/allP Hfree;apply/allP=>ind Hind.
      by move: (Hfree ind Hind); rewrite/HashVec.hash_has_free_spaces; rewrite addn1 addnS =>/ltn_weaken.    
    }
    move: (@hash_vec_contains_value_base _ _ value hashes inds Hallleq) => Hcontains'.
    move: (@bloomfilter_add_multiple_find_preserve Hcontains' Hzro) => Hcontains''.
    under eq_bigr => a0 _ do under eq_bigr => b _ do rewrite (@hash_vec_find_simpl n k value hshs' _ inds _ Hcontains'') //=.
    by under eq_bigr => ? ? do under eq_bigr => ? ? do rewrite boolR_distr; comp_simplify; rewrite eq_sym.
  Qed.

  Lemma bloomfilter_add_multiple_unwrap_base 
        hashes l (values: seq B) others inds:
    uniq values ->
    length values == l ->
    @AMQHash_hashstate_available_capacity (n,k.-1) hashes l ->
    all (@AMQHash_hashstate_unseen (n,k.-1) hashes) (values) ->
    \sum_(a in [finType of (k.-1.+1.-tuple (HashState n) * BloomFilter)]%type)
     ((d[ @AMQ_add_multiple (n,k.-1) I hashes bloomfilter_new values]) a *R*
      ((all (bloomfilter_get_bit^~ (bloomfilter_add_internal others a.2)) inds == true) %R)) =
    \sum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
     ((inds \subseteq hits ++ others) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l * k)).
  Proof.
    move: hashes bloomfilter_add_multiple_preserve.
    rewrite/AMQ_add_multiple/AMQState/AMQ_add/AMQ_add_internal/AMQHash_hash/AMQHash_hashstate_available_capacity/AMQHash_hashstate_unseen/AMQHash_hashstate_contains.
    change  (AMQHash (n, k.-1)) with ([finType of k.-1.+1.-tuple (HashVec.Hash.HashState n)]).
    change  (AMQHashValue (n, k.-1)) with ([finType of k.-1.+1.-tuple 'I_Hash_size.+1]).
    change ((n, k.-1).2.+1) with (k.-1.+1).
    change ((n, k.-1).1) with n.
    rewrite (@prednK k Hkgt0).
    move=> hashes bloomfilter_add_multiple_preserve.
    elim: l others values inds => [//=| l IHl] others [//=|//= value values] inds Huniq Hlen Hfree Hunseen.
    - {
        comp_normalize; comp_simplify; rewrite mulR1 //=.
        rewrite eqb_id RIneq.INR_IZR_INZ; do?apply f_equal.
        apply eq_in_all => ind _; clear.
        case Hin: (ind \in others) => //=.
          by apply bloomfilter_add_internal_hit => //=.
          apply/Bool.negb_true_iff; apply bloomfilter_add_internal_miss => //=.
            by apply bloomfilter_new_empty_bits.
              by move/Bool.negb_true_iff: Hin.
      }
    - {
        move=>//=.
        move: (@subseq_imd ([finType of 'I_Hash_size.+1]) l k (fun hits => inds \subseteq hits ++ others)) => //=.
        rewrite card_ord => ->.
        have Hsusp b bs:  (inds \subseteq (b ++ bs) ++ others) = (inds \subseteq bs ++ (others ++ b)); first
          by rewrite -subseq_consA subseq_consC -subseq_consA.
        under [\sum_(b in [finType of k.-tuple _]) _]eq_bigr => b _ do under eq_bigr => bs _ do rewrite Hsusp.
        under  [\sum_(b in [finType of k.-tuple _]) _]eq_bigr => b _. {
          rewrite -(IHl (others ++ b) values inds) //=.
            by over.          
              by move/andP: Huniq => [].
              move: Hfree;rewrite /HashVec.hashes_have_free_spaces=>/allP Hall; apply/allP=> y Hy; move: (Hall y Hy);

              rewrite/HashVec.hash_has_free_spaces addnS => /ltnW.
                by move/andP:Hunseen => [].
                by move/andP: Hunseen => [].
        }
         comp_normalize; comp_simplify_n 2.
        apply Logic.eq_sym; under eq_bigr => ? ? do rewrite rsum_Rmul_distr_l; rewrite exchange_big //=.
        comp_normalize; apply eq_bigr => hshs' _ ; apply eq_bigr => bf' _.
        rewrite exchange_big; apply eq_bigr => inds' _; rewrite mulRC -!mulRA; apply Logic.eq_sym.
        under eq_bigr => i ? do rewrite mulRC  -!mulRA; rewrite -rsum_Rmul_distr_l.
        move: (@bloomfilter_add_multiple_preserve
                 value
                 values l 0 hashes hshs' bloomfilter_new bf' ); clear bloomfilter_add_multiple_preserve.

        set bloomfilter_add_multiple := (d[ foldr
         (fun val : AMQHashKey =>
          (Bind
             (B:=[finType of [finType of k.-tuple (HashVec.Hash.HashState n)] *
                             [finType of BloomfilterCore.BloomFilterDefinitions.BloomFilter]]))^~ 
          (fun
             res_1 : [finType of [finType of k.-tuple (HashVec.Hash.HashState n)] *
                                 [finType of BloomfilterCore.BloomFilterDefinitions.BloomFilter]] =>
           let (hsh, bf) := res_1 in
           hash_res <-$ HashVec.hash_vec_int val hsh;
           (let (new_hashes, hash_vec) := hash_res in
            ret (new_hashes,
                BloomfilterCore.BloomFilterDefinitions.bloomfilter_add_internal hash_vec bf))))
         (ret (hashes, bloomfilter_new)) values]).
        move=> bloomfilter_add_multiple_preserve.
        case Hzr0: (bloomfilter_add_multiple (hshs', bf') == 0);
          first by move/eqP: Hzr0 ->;rewrite ?mulR0 ?mul0R //=.
        move/Bool.negb_true_iff: Hzr0 => Hzr0.
        apply f_equal.
        clear IHl.
        have H1:   (uniq (value :: values)); first by [].
        have H2: length values == l; first by move: Hlen =>/eqP [->].
        have H3: hashes_have_free_spaces hashes (l + 0).+1; first by rewrite addn0.
        have H4: all (hashes_value_unseen hashes) (value :: values); first by [].
        move: (@bloomfilter_add_multiple_preserve
                 H1 H2 H3 H4 Hzr0
              ) => /andP [Hfree' Huns'].
        by rewrite hash_vec_simpl => //=; rewrite mulRC bloomfilter_add_multiple_cat //=.
      }
  Qed.

  (** Proves the validity of the analogy used by Bose et al, wherin
   the false positives of a bloom filter can be thought of as
   equivalent to throwing balls into urns*)
  Lemma bloomfilter_add_multiple_unwrap 
        hashes l value (values: seq B) inds:
    uniq (value::values) ->
    length values == l ->
    @AMQHash_hashstate_available_capacity (n,k.-1) hashes (l.+1) ->
    all (@AMQHash_hashstate_unseen (n,k.-1) hashes) (value::values) ->
    \sum_(a in [finType of k.-1.+1.-tuple (HashState n) * BloomFilter])
     ((d[ @AMQ_add_multiple (n,k.-1) I (Tuple (hash_vec_insert_length value hashes inds)) bloomfilter_new
                                   values]) a *R*
      (d[ let (hashes2, bf) := a in res' <-$ bloomfilter_query value hashes2 bf; ret res'.2]) true) =
    \sum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
     ((inds \subseteq hits) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l * k)).
  Proof.      
    rewrite/bloomfilter_query //= => Huniq Hlen Hfree Hunseen.
    rewrite (@bloomfilter_add_multiple_unwrap_internal _ _ l) => //=.
    rewrite //= /bloomfilter_query_internal.
    move: Huniq => //=/andP[Hnin Huniq].
    move: (@bloomfilter_add_multiple_unwrap_base
             (Tuple (hash_vec_insert_length value hashes inds)) l values [::] inds Huniq Hlen
          ) => //=.
    under [   \sum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1]) _]eq_bigr => a _ do rewrite cats0.
    move=>-> //=.
    - {
        move: Hfree; rewrite/hashes_have_free_spaces/hash_has_free_spaces//=; clear.
        move=>/allP Hfree; apply/allP => [ //= hsh' /mapP [[hsh ind] /mem_zip/andP [Hhsh Hind] ->]].
        rewrite/hashstate_put/HashVec.hash_has_free_spaces //=.
        move: (Hfree hsh Hhsh); clear.      
        rewrite/FixedList.fixlist_length => //=.
        move=> H; apply/ fixedlist_add_incr;move: H.
        by rewrite/HashVec.hash_has_free_spaces addnS.
      }
    - {
        move/andP: Hunseen Hnin => [Huns ]; clear.
        rewrite/hashes_value_unseen //=; move=>/allP Hfree Hnin.
        apply/allP => [//= value' Hvalue]; move: (Hfree value' Hvalue)=>/allP  Hfree'.
        apply/allP => //= [ hsh' /mapP [[hsh ind] /mem_zip/andP [Hhsh Hind] ->]].
        move: (Hfree' hsh Hhsh ).
        move/memPn: Hnin => /(_ value' Hvalue); clear; rewrite /hash_unseen/hashstate_put.
          by move=> Hnew Hfind; apply fixmap_find_neq => //=.
      }
  Qed.    
  
  Theorem bloomfilter_collision_rsum
          hashes l value (values: seq B):
    length values == l ->
    @AMQHash_hashstate_available_capacity (n,k.-1) hashes (l.+1) ->
    all (@AMQHash_hashstate_unseen (n,k.-1) hashes) (value::values) ->
    uniq (value::values) ->
    d[ 
        res1 <-$ @AMQ_query (n,k.-1) I  (AMQ_new I) hashes value;
          let (hashes1, init_query_res) := res1 in
          res2 <-$ @AMQ_add_multiple (n,k.-1) I hashes1 (bloomfilter_new) values;
            let (hashes2, bf) := res2 in
            res' <-$ @AMQ_query (n,k.-1) I  bf hashes2 value;
              ret (res'.2)
      ] true =
    \sum_(inds in [finType of k.-tuple ('I_Hash_size.+1)])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (\sum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
        ((( inds \subseteq hits) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l * k)))))).
  Proof.
    (* expand to simplify k.-1.+1 to normal form *)
    move: hashes bloomfilter_add_multiple_unwrap.
    rewrite/AMQ_query/AMQ_query_internal/AMQ_new/AMQ_add_multiple/AMQState/AMQ_add/AMQ_add_internal/AMQHash_hash/AMQHash_hashstate_available_capacity/AMQHash_hashstate_unseen/AMQHash_hashstate_contains.
    change  (AMQHash (n, k.-1)) with ([finType of k.-1.+1.-tuple (HashVec.Hash.HashState n)]).
    change  (AMQHashValue (n, k.-1)) with ([finType of k.-1.+1.-tuple 'I_Hash_size.+1]).
    change ((n, k.-1).2.+1) with (k.-1.+1).
    change ((n, k.-1).1) with n.
    rewrite (@prednK k Hkgt0).
    move=> hashes bloomfilter_add_multiple_unwrap.
    have H x y z: (y = (0%R)) -> x = z -> x +R+ y = z. by move => -> ->; rewrite addR0.
    move=>//= Hlen Hfree /andP[Huns Halluns]/andP[Hnin Huniq].
    comp_normalize; comp_simplify_n 2.
    exchange_big_outwards 5 => //=; comp_simplify_n 1.
    exchange_big_outwards 4 => //=; comp_simplify_n 1.
    apply Logic.eq_sym.
    under eq_bigr => inds _ do (rewrite
                                -(@bloomfilter_add_multiple_unwrap hashes l value values)
                                   1?rsum_Rmul_distr_l //=; try (by apply/andP;split => //=)).
    comp_normalize.
    exchange_big_outwards 4 => //=; comp_simplify_n 1.
    exchange_big_outwards 3 => //=; comp_simplify_n 1.
    rewrite exchange_big; apply eq_bigr => hshs' _ //=.
    rewrite exchange_big; apply eq_bigr => bf' _ //=.
    rewrite exchange_big; apply Logic.eq_sym => //=; exchange_big_outwards 2 => //=; apply eq_bigr => hshs'' _.
    exchange_big_outwards 2 => //=; apply Logic.eq_sym; rewrite exchange_big; apply eq_bigr => inds' _. 
    rewrite exchange_big; apply eq_bigr => inds _; apply Logic.eq_sym=> //=.
    rewrite hash_vec_simpl //.
  Qed.

  Lemma subseq_conv l:
    \sum_(inds in [finType of k.-tuple ('I_Hash_size.+1)])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (\sum_(hits in [finType of (l * k).-tuple 'I_Hash_size.+1])
        ((( inds \subseteq hits) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l * k)))))) =
    ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l.+1 * k) *R*
     \sum_(a in ordinal_finType (Hash_size.+2))
      (((((a %R) ^R^ k) *R* (Factorial.fact a %R)) *R* ('C(Hash_size.+1, a) %R)) *R* stirling_no_2 (l * k) a)).
  Proof.
    under eq_bigr => inds _ do rewrite rsum_Rmul_distr_l.
    rewrite exchange_big.
    under eq_bigr => inds _ do under eq_bigr => inds' _ do rewrite mulRA mulRC.
    under eq_bigr => inds _ do rewrite -rsum_Rmul_distr_l.
    under eq_bigr => inds _ do under eq_bigr => inds' _ do rewrite mulRC.
    have Hbool inds' inds: (inds' \subseteq inds %R) = (inds' \subseteq inds); first by rewrite RIneq.INR_IZR_INZ.
    under eq_bigr => inds _ do under eq_bigr => ps _ do rewrite -Hbool.
    under eq_bigr => inds _ do rewrite -rsum_pred_demote.
    under eq_bigr => inds _.
    rewrite rsum_subseq_mult_undup_eq rsum_subseq_mult //=.
    by over.
      by apply undup_uniq.
      move=>//=.
      move:  ( second_stirling_number_sum_normalized l k Hash_size
                                         (fun len => (((len %R) *R* Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k))
             ) => //= ->.
      have H len: ((((len %R) *R* Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k) *R*
                   (((('C(Hash_size.+1, len) %R) *R* (Factorial.fact len %R)) *R* stirling_no_2 (l * k) len) *R*
                    (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l * k))) = (
                    (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l.+1 * k)) *R* (
                      ((len %R) ^R^ k) *R*
                      (Factorial.fact len %R) *R*
                      ('C (Hash_size.+1, len) %R) *R*
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
      under eq_bigr => len _ do rewrite H.
      by rewrite -rsum_Rmul_distr_l.
  Qed.

  Theorem bloomfilter_collision_prob
          hashes l value (values: seq B):
    length values == l ->
    @AMQHash_hashstate_available_capacity (n,k.-1) hashes (l.+1) ->
    all (@AMQHash_hashstate_unseen (n,k.-1) hashes) (value::values) ->
    uniq (value::values) ->
    d[ 
        res1 <-$ @AMQ_query (n,k.-1) I  (AMQ_new I) hashes value;
          let (hashes1, init_query_res) := res1 in
          res2 <-$ @AMQ_add_multiple (n,k.-1) I hashes1 (bloomfilter_new) values;
            let (hashes2, bf) := res2 in
            res' <-$ @AMQ_query (n,k.-1) I  bf hashes2 value;
              ret (res'.2)
      ] true =
    ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l.+1 * k) *R*
     \sum_(a in ordinal_finType (Hash_size.+2))
      (((((a %R) ^R^ k) *R* (Factorial.fact a %R)) *R* ('C(Hash_size.+1, a) %R)) *R* stirling_no_2 (l * k) a)).
  Proof.
    intros; rewrite (@bloomfilter_collision_rsum _ l) => //=.
      by rewrite  subseq_conv.
  Qed.
End BloomFilter.

(** Proves the standard properties of AMQs for Bloom Filters *)
Module BloomFilterProperties <:  AMQ.AMQProperties (BasicHashVec) (BloomfilterAMQ).
  Module AmqOperations :=  BloomfilterOperations.
  Export AmqOperations.

  Definition AMQ_false_positive_probability (hash:  AMQHashParams) (state: AMQStateParams) (l: nat) : Rdefinitions.R :=
((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l.+1 * hash.2.+1) *R*
     \sum_(a in ordinal_finType (Hash_size.+2))
      (((((a %R) ^R^ hash.2.+1) *R* (Factorial.fact a %R)) *R* ('C(Hash_size.+1, a) %R)) *R* stirling_no_2 (l * hash.2.+1) a)).

  Section Properties.
    Variable h : AMQHashParams.
    Variable s: AMQStateParams.

    Variable hashes: AMQHash h.

    Section FalseNegatives.

      Variable amq: AMQState s.

      Lemma AMQ_no_false_negatives:
        forall (l:nat_eqType) (x:AMQHashKey) (xs: seq AMQHashKey),
          uniq (x :: xs) -> length xs == l ->

          AMQ_valid amq -> AMQ_available_capacity h amq l.+1 ->

          AMQHash_hashstate_valid hashes ->
          AMQHash_hashstate_available_capacity hashes l.+1 ->
          all (AMQHash_hashstate_unseen hashes) (x::xs) ->
          (d[ res1 <-$ AMQ_add amq hashes x;
                let '(hsh1, amq1) := res1 in
                res2 <-$ AMQ_add_multiple hsh1 amq1 xs;
                  let '(hsh2, amq2) := res2 in
                  res3 <-$ AMQ_query amq2 hsh2 x;
                    ret (snd res3) ] true) = (1 %R).
      Proof.
        apply AMQ_no_false_negatives.
      Qed.

    End FalseNegatives.

    Theorem AMQ_false_positives_rate: forall  l value (values: seq _),
        length values == l ->

        AMQHash_hashstate_valid hashes ->
        AMQHash_hashstate_available_capacity hashes (l.+1) ->


        AMQ_available_capacity h (AMQ_new s) l.+1 ->
        all (AMQHash_hashstate_unseen hashes) (value::values) ->
        uniq (value::values) ->
        d[ 
            res1 <-$ AMQ_query (AMQ_new s) hashes value;
              let (hashes1, init_query_res) := res1 in
              res2 <-$ AMQ_add_multiple hashes1 (AMQ_new s) values;
                let (hashes2, amq) := res2 in
                res' <-$ AMQ_query amq  hashes2 value;
                  ret (res'.2)
          ] true = AMQ_false_positive_probability h s l.
    Proof.
      move: h hashes => [n k]; clear hashes=> hashes.
      move=> l value values Hlen Hvalid Havail Hcap Huns Huniq.
      move: (@bloomfilter_collision_prob k.+1 n).
      Set Printing Implicit Defensive.
      change (k.+1.-1) with (k); rewrite/AMQ_false_positive_probability.
      change (n, k).2.+1 with k.+1.
      move=>H; rewrite (@H _ _ l) //=.
    Qed.
  End Properties.
End  BloomFilterProperties.

End BloomFilterProbability.

(* Local Variables: *)
(* company-coq-local-symbols: (("\\subseteq" . ?⊆)) *)
(* End: *)
