# Ceramist Artefact

This is the artefact accompanying the CAV 2020 paper entitled
"Ceramist: Certifying Certainty and Uncertainty in Approximate
Membership Query Structures".

The artefact contains a scripts that will download and compile the
Ceramist proof scripts in a docker container.

## Prerequisites

In order to build the image, you must have the
[Docker](https://www.docker.com/) platform (>= Docker version 19.03.7)
installed and the docker daemon running.

Note: If running on Windows or Mac OS ensure that you have at least 8GB
of RAM allocated to the docker process (see
[here](https://docs.docker.com/docker-for-mac/#advanced) for Mac OS and
[here](https://docs.docker.com/docker-for-windows/#advanced) for Windows).

The source of this artefact script can be obtained from GitHub:
```
git clone -b artefact https://github.com/certichain/ceramist.git
```

## Building the artefact
Note: The artefact is expected to take around 1 hour to compile from
sources.

Once you have the Docker daemon running, navigate to the root of this repository and run:
```
docker build --memory=8g -t ceramist:1.0.1 .
```

Note: If the build fails with a `killed` message, this means that your
docker process ran out of memory - please ensure that you have allowed
it at least 8GB of ram (see [here](https://docs.docker.com/docker-for-mac/#advanced) for
Mac OS and [here](https://docs.docker.com/docker-for-windows/#advanced) for
Windows).


This will download all the project's dependencies and will compile the
proof scripts - this will take a while (around 1 hour).

When the build completes, you should see the following output:
```
COQC Structures/CountingBloomFilter/CountingBloomFilter_Probability.v
COQC Structures/QuotientFilter/QuotientFilter_Definitions.v
COQC Structures/QuotientFilter/QuotientFilter_Probability.v
COQC Structures/BlockedAMQ/BlockedAMQ.v
make[1]: Leaving directory '/ceramist'
```

At this point all the proofs in the artefact have been compiled and the docker image is ready.

To browse the files within the image, first start a docker container from the image:
```
docker run --name ceramist --rm -it ceramist:1.0.1
```
You should now be dropped into a shell with the working directory set to a folder containing the ceramist source code.
From here you can explore the source code/build the coqdoc documentation (using `eval $(opam env) && make doc`, and the output will be placed into a `html` folder at the ceramist root).

If you wish to browse the files on your local machine, start up the
docker container, using the command above, and *while it is still
running (i.e don't close it)*, in a separate shell, execute:

```
docker cp  ceramist:/ceramist ./ceramist
```

This will copy the compiled ceramist source code (and HTML
documentation, if you have made it, to your local machine).

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

## Theorems and Lemmas
The following table maps the statements from the paper to statements
in the source code:

- *Theorem 3 (No False Negatives)* 
  - file: Structures/BloomFilter/BloomFilter_Probability.v
  - line: 1166
  - name: AMQ_no_false_negatives
- *Lemma 2 (Probability of Flipping a Single Bit)*
  - file: Structures/BloomFilter/BloomFilter_Probability.v:
  - line: 588
  - name: bloomfilter_addn_insert_multiple
- *Theorem 4 (Probability of a False Positive)*
  - file: Structures/BloomFilter/BloomFilter_Probability.v:
  - line: 1187
  - name: AMQ_false_positives_rate
- *Theorem 5 (Uniform Hash Output)*
  - file: Structures/Core/HashVec.v
  - line: 296
  - name: hash_vecP
- *Theorem 6 (Hash Consistency)*
  - file: Structures/Core/HashVec.v
  - line: 517
  - name: hash_vec_find_simpl
- *AMQHash Interface - Property 1,2*
  - file: Structures/Core/AMQHash.v
  - line: 39
  - name: AMQHASH
  - note: instantiated for single hash functions at line 156
    (BasicHash), and for hash vectors at line 354 (BasicHashVec) of
    same file.
- *AMQ Interface - Property 3,4*
  - file: Structures/Core/AMQ.v
  - line: 46
  - name: AMQ
- *Theorem 7 (Generalized No False Negatives)*
  - file: Structures/Core/AMQ.v
  - line: 281
  - name: AMQ_no_false_negatives
- *AMQMap Interface - Property 5,6*
  - file: Structures/Core/AMQReduction.v
  - line: 42
  - name: AMQMAP
  - note: instantiated for Counting Bloom filters in
    Structures/CountingBloomFilter/CountingBloomFilterDefinitions.v at
    line 832 (BloomFilterReduction).
- *Theorem 8 (AMQ False Positive Reduction)*
  - file: Structures/Core/AMQReduction.v
  - line: 205
  - name: AMQ_false_positives_rate
- *Pattern 1 (Bind normalization)*
  - file: Utils/tactics.v
  - line: 53
  - name: comp_normalize
- *Pattern 2 (Probability of a Sequential Composition)*
  - file: Utils/tactics.v
  - line: 171
  - name: comp_simplify
- *Lemma 3 (Plausible Sequencing)*
  - file: Utils/rsum_ext.v
  - line: 732
  - name: eq_rsum_ne0
- *Pattern 3 (Plausible Outcome Decomposition)*
  - file: Utils/tactics.v
  - line: 197,258
  - name: comp_possible_decompose, comp_possible_exists
  - note: first version for when plausiblility is an assumption, and
    the second version is for when the plausiblility is a goal
- *Theorem 9 (Quotient filter False Positive Rate)**
  - file: Structures/QuotientFilter/QuotientFilter_Probability.v
  - line:  527
  - name: AMQ_false_positives_rate
- *Theorem 10 (Blocked AMQ False Positive Rate)*
  - file: Structures/BlockedAMQ/BlockedAMQ.v
  - line: 738
  - name: AMQ_false_positives_rate
  - note: see Structures/Demo.v for an instantiation of the Blocked
    AMQ on each of the prior AMQs
- *Theorem 11 (Counting Bloom filter removal)*
  - file:
    Structures/CountingBloomFilter/CountingBloomFilter_Probability.v
  - line: 178
  - name: countingbloomfilter_removal_preserve
- *Theorem 12 (Certainty of Counter Increments)*
  - file:
    Structures/CountingBloomFilter/CountingBloomFilter_Probability.v
  - line: 104
  - name: countingbloomfilter_counter_prob


## Building Locally
If you wish to step through the proof interactively, we recommend you
build the artefact locally.

To do this, ensure that you have the latest version of
[opam](https://opam.ocaml.org/) installed, and that it has been
correctly initialised (running `opam init` and `eval $(opam env)`).

1. Add the coq-released repository.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
```

2. Install the dependencies for ceramist (you may also be prompted to use `--unlock-base`):
```
opam install -y --deps-only coq-ceramist.1.0.1
```

3. Clone the ceramist artefact:
```
git clone -b artefact https://github.com/certichain/ceramist.git
cd ./ceramist
```

4. Build ceramist:
```
make
```

5. (Optional) Build ocamldoc - the documentation will be placed into a  folder named `html` at the project root:
```
make doc
```

6. Open the coq source files (`.v` extension) in either coq-ide or
   proof general.
