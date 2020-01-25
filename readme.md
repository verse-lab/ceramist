# Ceramist -  Verified Hash-based Approximate Membership Structures
## Installation
Use opam to install dependencies

```
opam install ./opam
```

Then build the project:
```
make clean && make
```
Takes around an hour to build.

## Theorems and Lemmas
The following table maps the statements from the associated paper to statements in the source code:

- *Theorem 3 (No False Negatives)* 
  - file: Structures/BloomFilter/BloomFilter_Probability.v
  - line: 1164
  - name: AMQ_no_false_negatives
- *Lemma 2 (Probability of Flipping a Single Bit)*
  - file: Structures/BloomFilter/BloomFilter_Probability.v:
  - line: 587
  - name: bloomfilter_addn_insert_multiple
- *Theorem 4 (Probability of a False Positive)*
  - file: Structures/BloomFilter/BloomFilter_Probability.v:
  - line: 1185
  - name: AMQ_false_positives_rate
- *Theorem 5 (Uniform Hash Output)*
  - file: Structures/Core/HashVec.v
  - line: 290
  - name: hash_vecP
- *Theorem 6 (Hash Consistency)*
  - file: Structures/Core/HashVec.v
  - line: 511
  - name: hash_vec_find_simpl
- *AMQHash Interface - Property 1,2*
  - file: Structures/Core/AMQHash.v
  - line: 30
  - name: AMQHASH
  - note: instantiated for single hash functions at line 140
    (BasicHash), and for hash vectors at line 338 (BasicHashVec) of
    same file.
- *AMQ Interface - Property 3,4*
  - file: Structures/Core/AMQ.v
  - line: 30
  - name: AMQ
- *Theorem 7 (Generalized No False Negatives)*
  - file: Structures/Core/AMQ.v
  - line: 264
  - name: AMQ_no_false_negatives
- *AMQMap Interface - Property 5,6*
  - file: Structures/Core/AMQReduction.v
  - line: 30
  - name: AMQMAP
  - note: instantiated for Counting Bloom filters in
    Structures/CountingBloomFilter/CountingBloomFilterDefinitions.v at
    line 832 (BloomFilterReduction).
- *Theorem 8 (AMQ False Positive Reduction)*
  - file: Structures/Core/AMQReduction.v
  - line: 193
  - name: AMQ_false_positives_rate
- *Pattern 1 (Bind normalization)*
  - file: Utils/tactics.v
  - line: 46
  - name: comp_normalize
- *Pattern 2 (Probability of a Sequential Composition)*
  - file: Utils/tactics.v
  - line: 164
  - name: comp_simplify
- *Lemma 3 (Plausible Sequencing)*
  - file: Utils/rsum_ext.v
  - line: 723
  - name: eq_rsum_ne0
- *Pattern 3 (Plausible Outcome Decomposition)*
  - file: Utils/tactics.v
  - line: 190,251
  - name: comp_possible_decompose, comp_possible_exists
  - note: first version for when plausiblility is an assumption, and
    the second version is for when the plausiblility is a goal
- *Theorem 9 (Quotient filter False Positive Rate)
  - file: Structures/QuotientFilter/QuotientFilter_Probability.v
  - line:  516
  - name: AMQ_false_positives_rate
- *Theorem 10 (Blocked AMQ False Positive Rate)*
  - file: Structures/BlockedAMQ/BlockedAMQ.v
  - line: 706
  - name: AMQ_false_positives_rate
  - note: see Structures/Demo.v for an instantiation of the Blocked AMQ on each of the prior AMQs
- *Theorem 11 (Counting Bloom filter removal)*
  - file: Structures/CountingBloomFilter/CountingBloomFilter_Probability.v
  - line: 165
  - name: countingbloomfilter_removal_preserve
- *Theorem 12 (Certainty of Counter Increments)*
  - file: Structures/CountingBloomFilter/CountingBloomFilter_Probability.v
  - line: 91
  - name: countingbloomfilter_counter_prob

## Project Structure
The structure of the overall development is as follows:
```
.
├── Computation
│   ├── Comp.v
│   └── Notationv1.v
├── Structures
│   ├── BlockedAMQ
│   │   └── BlockedAMQ.v
│   ├── BloomFilter
│   │   ├── BloomFilter_Definitions.v
│   │   └── BloomFilter_Probability.v
│   ├── Core
│   │   ├── AMQHash.v
│   │   ├── AMQReduction.v
│   │   ├── AMQ.v
│   │   ├── FixedList.v
│   │   ├── FixedMap.v
│   │   ├── Hash.v
│   │   └── HashVec.v
│   ├── CountingBloomFilter
│   │   ├── CountingBloomFilter_Definitions.v
│   │   └── CountingBloomFilter_Probability.v
│   └── QuotientFilter
│       ├── QuotientFilter_Definitions.v
│       └── QuotientFilter_Probability.v
└── Utils
    ├── InvMisc.v
    ├── rsum_ext.v
    ├── seq_ext.v
    ├── seq_subset.v
    ├── stirling.v
    └── tactics.v

8 directories, 22 files
```

The library is split into separate logical components by directory:
- *Computation* - defines a probability monad and associated notation for it on top of the 'coq-infotheo' probability library.
- *Utils* - collection of utility lemmas and tactics used throughout the development
- *Structures/Core* - contains definitions and properties about the core probabilistic primitives exported by the library, and defines the abstract AMQ interface satisfied by all instantiations.
- *Structures/BloomFilter* - example use of the exported library to prove various probabilistic properties on bloom filters.
- *Structures/CountingBloomFilter* - another exemplar use of the library to prove probabilistic properties on counting bloom filters. 
- *Structures/QuotientBloomFilter* - exemplar use of library to prove probabilistic properties of quotient filters
- *Structures/BlockedAMQ* - exemplar use of library to prove probabilistic properties of a higher order AMQ - the blockedAMQ 

Check out `Structures/Demo.v` for an example instantiation of the BlockedAMQ to derive Blocked Bloom filters, Counting Blocked bloom filters and Blocked Quotient filters.

## Tactics
To simplify reasoning about probabilistic computations, we provide a few helper tactics under `ProbHash.Utils`:

- `comp_normalize` - is a tactic which normalizes  probabilistic computations in the goal to a standard
   form consisting of a nested summation with a summand which is the product of each individual statement:
   For example, if our goal contains a term of the form:
   ```
   d[ res <-$ hash n v hsh;
   x <- fst res;
   ret x ] value
   ```
   applying `comp_normalize` normalizes it to:
   ```
   \sum_(i in HashState n) 
   \sum_(i0 in 'I_Hash_size.+1) 
   ((d[ hash n v hsh]) (i, i0) *R* 
   ((value == i0) %R))
   ``` 
   This tactic works by simply recursively descending the computation and expanding the
   definition of the distribution.

- `comp_simplify` - is a tactic which effectively applies beta
   reduction to the normalized form, substituting any `ret x` (which
   have been normalized to a factor of the form `(x == ...)` by the previous tactic)
   statements into the rest of the computation - applying it to the previous example would result in:
   ```
   \sum_(i in HashState n) 
   (d[ hash n v hsh]) (i, value)
   ```
- `comp_simplify_n n` - is a variant of the previous one which applies
   the reduction a fixed number `n` of times as sometimes the previous
   tactic may loop.
- `comp_possible_decompose` - is a tactic which converts a fact (must
   be first element of goal) about a possible computation 
   `( d[ c1; c2; ....; cn] v != 0)` 
   into a fact about the possibility of the individual statements of
   the computation
   `forall v1,v2, ..., vn, d[ c1 ] v1 != 0 -> d[ c2] v2 -> .... d[ cn] vn != 0`
- `comp_possible_exists` is a tactic which converts a goal about a computation being possible
   `( d[ c1; c2; ....; cn] v != 0)` 
   into a corresponding proof of existance, where one must provide
   possible outcomes for each statement outcome
   `exists v1,v2, ..., vn, d[ c1 ] v1 != 0 /\ d[ c2] v2 /\ .... /\ d[ cn] vn != 0`
- `comp_impossible_decompose` - is a tactic which automatically
   decomposes an impossibility statement 
   `\sum_{v1} ... \sum_{vn} P[c1 = v1] * ... * P[ cn = vn ] = 0` 
   into properties about its component parts 
   `forall v1,..,vn, P[c1 = v1] * ... * P[cn = vn] = 0`

- `exchange_big_inwards f` - is a tactic which moves the outermost
   summation in a series of nested summations to the innermost
   position, then applies the supplied tactic `f` in this context.

- `exchange_big_outwards n` - is a tactic which moves the `n`th
   summation in a series of nested summations to the outermost
   position.

## License
Given its dependencies:

- Coq (distributed under the LGPLv2.1 license)
- MathComp (distributed under the CeCILL-B license)
- Infotheo (distributed under the GPLv3 license)

ProbHash is distributed under the GPLv3 license.
