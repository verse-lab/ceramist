# Bloom filters in Coq - Reasoning about Hash-based Probabilistic Algorithms

# Installation
Use opam to install dependencies

```
opam install ./opam
```

Then build the project:
```
make clean && make
```


# Project Structure
```

.
├── Probability
│   ├── bigop_tactics.v
│   ├── Comp.v
│   └── Notationv1.v
├── Properties
│   ├── Collision.v
│   ├── InvMisc.v
│   └── Parameters.v
├── Structures
│   ├── BitVector.v
│   ├── BloomFilter.v
│   ├── FixedList.v
│   ├── FixedMap.v
│   └── Hash.v

4 directories, 45 files

```
