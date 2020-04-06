From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path bigop finfun binomial.

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path.

From infotheo Require Import
      fdist ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From ProbHash.Computation
     Require Import Comp Notationv1.

From ProbHash.Core
     Require Import Hash HashVec FixedList AMQ AMQHash.

From ProbHash.Utils
     Require Import InvMisc seq_ext seq_subset rsum_ext stirling tactics.

From ProbHash.BlockedAMQ
     Require Import BlockedAMQ.

From ProbHash.BloomFilter
     Require Import BloomFilter_Definitions BloomFilter_Probability.

From ProbHash.CountingBloomFilter
     Require Import CountingBloomFilter_Definitions CountingBloomFilter_Probability.

From ProbHash.QuotientFilter
     Require Import QuotientFilter_Definitions QuotientFilter_Probability.

Module BlockedBloomFilter (Spec: HashSpec) (BlockedAMQSpec: BlockedAMQSpec).
  Module BloomFilterCore :=  BloomFilterProbability Spec.
  Module BloomFilterAMQ := BloomFilterCore.BloomfilterAMQ.
  Module BloomFilterProperties :=  BloomFilterCore.BloomFilterProperties.
  Module BloomFilterHash :=  BloomFilterCore.BasicHashVec.
  Module BlockedBloomFilter := BlockedAMQ
                                 (BlockedAMQSpec)
                                 (BloomFilterHash)
                                 (BloomFilterAMQ).

  Module BlockedBloomFilterAMQ := BlockedBloomFilter.AMQ.
  Module BlockedBloomFilterProperties := BlockedBloomFilter.BlockedAMQProperties (BloomFilterProperties).

  Lemma BlockedBloomFilter_false_positives:
    forall (h : BlockedBloomFilter.MetaHash.AMQHashParams) (s : BlockedBloomFilter.AMQ.AMQStateParams)
           (hashes : BlockedBloomFilter.MetaHash.AMQHash h) (l : nat)
           (value : BlockedBloomFilter.MetaHash.AMQHashKey)
           (values : seq BlockedBloomFilter.MetaHash.AMQHashKey),
      length values == l ->
      BlockedBloomFilter.MetaHash.AMQHash_hashstate_valid hashes ->
      BlockedBloomFilter.MetaHash.AMQHash_hashstate_available_capacity hashes l.+1 ->
      BlockedBloomFilter.AMQ.AMQ_available_capacity h (BlockedBloomFilter.AMQ.AMQ_new s) l.+1 ->
      all (BlockedBloomFilter.MetaHash.AMQHash_hashstate_unseen hashes) (value :: values) ->
      uniq (value :: values) ->
      (d[ res1 <-$
               BlockedBloomFilterProperties.AmqOperations.AMQ_query (BlockedBloomFilter.AMQ.AMQ_new s) hashes
               value;
            (let (hashes1, _) := res1 in
             res2 <-$
                  BlockedBloomFilterProperties.AmqOperations.AMQ_add_multiple hashes1
                  (BlockedBloomFilter.AMQ.AMQ_new s) values;
               (let (hashes2, amq) := res2 in
                res' <-$ BlockedBloomFilterProperties.AmqOperations.AMQ_query amq hashes2 value; ret res'.2))])
        true =
  \sum_(i < l.+1)
     (((('C(l, i) %R) *R*
        (Rdefinitions.Rinv (#|BlockedBloomFilter.MetaHash.BasicMetaHash.AMQHashValue h.1| %R) ^R^ i)) *R*
       ((1 -R- Rdefinitions.Rinv (#|BlockedBloomFilter.MetaHash.BasicMetaHash.AMQHashValue h.1| %R))
        ^R^ l - i)) *R*
      ((Rdefinitions.Rinv (Spec.Hash_size.+1 %R) ^R^ i.+1 * h.2.2.+1) *R*
       \sum_(a in ordinal_finType Spec.Hash_size.+2)
          (((((a %R) ^R^ h.2.2.+1) *R* (Factorial.fact a %R)) *R*
            (binomial.binomial Spec.Hash_size.+1 a %R)) *R* stirling_no_2 (i * h.2.2.+1) a))).
  Proof.
    by apply BlockedBloomFilterProperties.AMQ_false_positives_rate. (* trivial... *)
  Qed.

End BlockedBloomFilter.

Module BlockedCountingBloomFilter (Spec: HashSpec) (BlockedAMQSpec: BlockedAMQSpec).
  Module CountingBloomFilterCore :=   CountingBloomFilter Spec.
  Module CountingBloomFilterAMQ := CountingBloomFilterCore.CountingBloomFilterDefinitions.AMQ.
  Module CountingBloomFilterProperties :=  CountingBloomFilterCore.CountingBloomFilterProperties.
  Module CountingBloomFilterHash :=  CountingBloomFilterCore.CountingBloomFilterDefinitions.BloomFilterProbability.BasicHashVec.
  Module CountingBlockedBloomFilter := BlockedAMQ
                                 (BlockedAMQSpec)
                                 (CountingBloomFilterHash)
                                 (CountingBloomFilterAMQ).

  Module CountingBlockedBloomFilterAMQ := CountingBlockedBloomFilter.AMQ.
  Module CountingBlockedBloomFilterProperties := CountingBlockedBloomFilter.BlockedAMQProperties (CountingBloomFilterProperties).

  Lemma CountingBlockedBloomFilter_false_positives:
    forall (h : CountingBlockedBloomFilter.MetaHash.AMQHashParams)
           (s : CountingBlockedBloomFilter.AMQ.AMQStateParams)
           (hashes : CountingBlockedBloomFilter.MetaHash.AMQHash h) (l : nat)
           (value : CountingBlockedBloomFilter.MetaHash.AMQHashKey)
           (values : seq CountingBlockedBloomFilter.MetaHash.AMQHashKey),
      length values == l ->
      CountingBlockedBloomFilter.MetaHash.AMQHash_hashstate_valid hashes ->
      CountingBlockedBloomFilter.MetaHash.AMQHash_hashstate_available_capacity hashes l.+1 ->
      CountingBlockedBloomFilter.AMQ.AMQ_available_capacity h (CountingBlockedBloomFilter.AMQ.AMQ_new s)
                                                            l.+1 ->
      all (CountingBlockedBloomFilter.MetaHash.AMQHash_hashstate_unseen hashes) (value :: values) ->
      uniq (value :: values) ->
      (d[ res1 <-$
               CountingBlockedBloomFilterProperties.AmqOperations.AMQ_query
               (CountingBlockedBloomFilter.AMQ.AMQ_new s) hashes value;
            (let (hashes1, _) := res1 in
             res2 <-$
                  CountingBlockedBloomFilterProperties.AmqOperations.AMQ_add_multiple hashes1
                  (CountingBlockedBloomFilter.AMQ.AMQ_new s) values;
               (let (hashes2, amq) := res2 in
                res' <-$ CountingBlockedBloomFilterProperties.AmqOperations.AMQ_query amq hashes2 value;
                  ret res'.2))]) true =
  \sum_(i < l.+1)
     (((('C(l, i) %R) *R*
        (Rdefinitions.Rinv (#|CountingBlockedBloomFilter.MetaHash.BasicMetaHash.AMQHashValue h.1| %R)
         ^R^ i)) *R*
       ((1 -R-
         Rdefinitions.Rinv (#|CountingBlockedBloomFilter.MetaHash.BasicMetaHash.AMQHashValue h.1| %R))
        ^R^ l - i)) *R*
      ((Rdefinitions.Rinv (Spec.Hash_size.+1 %R) ^R^ i.+1 * h.2.2.+1) *R*
       \sum_(a in ordinal_finType Spec.Hash_size.+2)
          (((((a %R) ^R^ h.2.2.+1) *R* (Factorial.fact a %R)) *R* ('C(Spec.Hash_size.+1, a) %R)) *R*
           stirling_no_2 (i * h.2.2.+1) a))).
  Proof.
    by apply CountingBlockedBloomFilterProperties.AMQ_false_positives_rate. (* trivial... *)
  Qed.

End BlockedCountingBloomFilter.
  
Module BlockedQuotientFilter (Spec: QuotientFilterSpec) (BlockedAMQSpec: BlockedAMQSpec).
  Module QuotientFilterCore :=   QuotientFilterProbability Spec.
  Module QuotientFilterAMQ := QuotientFilterCore.QuotientFilterAMQ.
  Module QuotientFilterProperties :=  QuotientFilterCore.QuotientFilterProperties.
  Module QuotientFilterHash :=  QuotientFilterCore.BasicHash.

  Module BlockedQuotientFilter := BlockedAMQ
                                 (BlockedAMQSpec)
                                 (QuotientFilterHash)
                                 (QuotientFilterAMQ).

  Module BlockedQuotientFilterAMQ := BlockedQuotientFilter.AMQ.
  Module BlockedQuotientFilterProperties := BlockedQuotientFilter.BlockedAMQProperties (QuotientFilterProperties).

  Lemma CountingBlockedBloomFilter_false_positives:
    forall (h : BlockedQuotientFilter.MetaHash.AMQHashParams)
           (s : BlockedQuotientFilter.AMQ.AMQStateParams) (hashes : BlockedQuotientFilter.MetaHash.AMQHash h)
           (l : nat) (value : BlockedQuotientFilter.MetaHash.AMQHashKey)
           (values : seq BlockedQuotientFilter.MetaHash.AMQHashKey),
      length values == l ->
      BlockedQuotientFilter.MetaHash.AMQHash_hashstate_valid hashes ->
      BlockedQuotientFilter.MetaHash.AMQHash_hashstate_available_capacity hashes l.+1 ->
      BlockedQuotientFilter.AMQ.AMQ_available_capacity h (BlockedQuotientFilter.AMQ.AMQ_new s) l.+1 ->
      all (BlockedQuotientFilter.MetaHash.AMQHash_hashstate_unseen hashes) (value :: values) ->
      uniq (value :: values) ->
      (d[ res1 <-$
               BlockedQuotientFilterProperties.AmqOperations.AMQ_query (BlockedQuotientFilter.AMQ.AMQ_new s)
               hashes value;
            (let (hashes1, _) := res1 in
             res2 <-$
                  BlockedQuotientFilterProperties.AmqOperations.AMQ_add_multiple hashes1
                  (BlockedQuotientFilter.AMQ.AMQ_new s) values;
               (let (hashes2, amq) := res2 in
                res' <-$ BlockedQuotientFilterProperties.AmqOperations.AMQ_query amq hashes2 value; ret res'.2))])
        true =
  \sum_(i < l.+1)
     (((('C(l, i) %R) *R*
        (Rdefinitions.Rinv (#|BlockedQuotientFilter.MetaHash.BasicMetaHash.AMQHashValue h.1| %R) ^R^ i)) *R*
       ((1 -R- Rdefinitions.Rinv (#|BlockedQuotientFilter.MetaHash.BasicMetaHash.AMQHashValue h.1| %R))
        ^R^ l - i)) *R*
      (1 -R-
       ((1 -R- Rdefinitions.Rinv QuotientFilterCore.QuotientFilterDefinitions.QuotientHash.Hash_size.+1)
        ^R^ i))).
  Proof.
    by apply BlockedQuotientFilterProperties.AMQ_false_positives_rate. (* trivial... *)
  Qed.

  Print Assumptions  CountingBlockedBloomFilter_false_positives.
End  BlockedQuotientFilter.
