[![Build Status](https://travis-ci.com/dusk-network/poseidon252-hash.svg?branch=master)](https://travis-ci.com/dusk-network/poseidon252-hash)
[![Repository](https://img.shields.io/badge/github-poseidon252-blueviolet)](https://github.com/dusk-network/poseidon252-hash)
[![Documentation](https://img.shields.io/badge/docs-poseidon252-blue)](https://dusk-network.github.io/poseidon252-hash/index.html)

# Poseidon252 Hash

Reference implementation for the Poseidon Hashing algorithm.

#### Reference

[Starkad and Poseidon: New Hash Functions for Zero Knowledge Proof Systems](https://eprint.iacr.org/2019/458.pdf)

This repository has been created so there's a unique library that holds the tools & functions
required to perform Poseidon Hashes.

This hashes heavily rely on the Hades permutation, which is one of the key parts that Poseidon needs in order
to work.
This library uses the reference implementation of [Hades252](https://github.com/dusk-network/hades252) which has been
designed & build by the [Dusk-Network team](https://dusk.network/).

**The library provides the two hashing techniques of Poseidon:**

## Sponge Hash

The `Sponge` techniqe in Poseidon allows to hash an unlimited ammount of data
into a single `Scalar`.
The sponge hash techniqe requires a padding to be applied before the data can
be hashed.

This is done to avoid hash collitions as stated in the paper of the Poseidon Hash
algorithm. See: (https://eprint.iacr.org/2019/458.pdf)[https://eprint.iacr.org/2019/458.pdf].
The inputs of the `sponge_hash` are always `Scalar` or need to be capable of being represented
as it.

The module provides two sponge hash implementations:

- Sponge hash using `Scalar` as backend. Which hashes the inputed `Scalar`s and returns a single
`Scalar`.

- Sponge hash gadget using `dusk_plonk::Variable` as a backend. This techniqe is used/required
when you want to proof pre-images of unconstrained data inside of Zero-Knowledge PLONK circuits.

## Merkle Hash

The Merkle Level Hashing is a technique that Poseidon is optimized-by-design
to perform.
This technique allows us to perform hashes of an entire Merkle Tree using
`Hades252` as backend.

The technique requires the computation of a `bitflags` element which is always
positioned as the first item of the level when we hash it, and it basically generated
in respect of the presence or absence of a leaf in the tree level.
This allows to prevent hashing collitions.

At the moment, this library is designed and optimized to work only with trees of `ARITY`
up to 4. **That means that trees with a bigger ARITY SHOULD NEVER be used with this lib.**
The module contains the implementation of 4 variants of the same algorithm to support the
majority of the configurations that the user may need:

- Scalar backend for hashing Merkle Tree levels outside of ZK-Circuits whith two variants:
One of them computes the bitflags item while the other assumes that it has already been
computed and placed in the first Level position.

- `dusk_plonk::Variable` backend for hashing Merkle Tree levels inside of ZK-Circuits,
 specifically, PLONK circuits. This implementation comes also whith two variants;
One of them computes the bitflags item while the other assumes that it has already been
computed and placed in the first Level position.

## Licensing

This code is licensed under Mozilla Public License Version 2.0 (MPL-2.0). Please see [LICENSE](https://github.com/dusk-network/plonk/blob/master/LICENSE) for further info.

## About

Implementation designed by the [dusk](https://dusk.network) team.
