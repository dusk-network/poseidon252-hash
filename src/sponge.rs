// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use dusk_bls12_381::BlsScalar;
use dusk_plonk::prelude::*;
use hades252::strategies::{GadgetStrategy, ScalarStrategy, Strategy};

/// The `hash` function takes an arbitrary number of BlsScalars and returns the
/// hash, using the `Hades` BlsScalarStragegy
pub fn hash(messages: &[BlsScalar]) -> BlsScalar {
    let mut strategy = ScalarStrategy::new();

    // The value used to pad the words is zero.
    let padder = BlsScalar::zero();
    // One will identify the end of messages.
    let eom = BlsScalar::one();

    let mut words = pad(messages, hades252::WIDTH, padder, eom);
    // If the words len is less than the Hades252 permutation `hades252::WIDTH` we directly
    // call the permutation saving useless additions by zero.
    if words.len() == hades252::WIDTH {
        strategy.perm(&mut words);
        return words[1];
    }
    // If the words len is bigger than the Hades252 permutation `hades252::WIDTH` then we
    // need to collapse the padded limbs. See bottom of pag. 16 of
    // https://eprint.iacr.org/2019/458.pdf
    let words = words.chunks(hades252::WIDTH).fold(
        vec![BlsScalar::zero(); hades252::WIDTH],
        |mut inputs, values| {
            let mut values = values.iter();
            inputs
                .iter_mut()
                .for_each(|input| *input += values.next().unwrap());
            strategy.perm(&mut inputs);
            inputs
        },
    );

    words[1]
}

/// The `hash` function takes an arbitrary number of plonk `Variable`s and returns the
/// hash, using the `Hades` GadgetStragegy
pub fn hash_gadget(composer: &mut StandardComposer, messages: &[Variable]) -> Variable {
    // Create and constrait one and zero as witnesses.
    let zero = composer.add_input(BlsScalar::zero());
    composer.constrain_to_constant(zero, BlsScalar::zero(), BlsScalar::zero());
    let one = composer.add_input(BlsScalar::one());
    composer.constrain_to_constant(one, BlsScalar::one(), BlsScalar::zero());
    // The value used to pad the words is zero.
    let padder = zero;
    // One will identify the end of messages.
    let eom = one;
    let mut words = pad(messages, hades252::WIDTH, padder, eom);
    // If the words len is less than the Hades252 permutation `hades252::WIDTH` we directly
    // call the permutation saving useless additions by zero.
    if words.len() == hades252::WIDTH {
        let mut strategy = GadgetStrategy::new(composer);
        strategy.perm(&mut words);
        return words[1];
    }
    // If the words len is bigger than the Hades252 permutation `hades252::WIDTH` then we
    // need to collapse the padded limbs. See bottom of pag. 16 of
    // https://eprint.iacr.org/2019/458.pdf
    let words =
        words
            .chunks(hades252::WIDTH)
            .fold(vec![padder; hades252::WIDTH], |mut inputs, values| {
                let mut values = values.iter();
                inputs.iter_mut().for_each(|input| {
                    *input = composer.add(
                        (BlsScalar::one(), *input),
                        (BlsScalar::one(), *values.next().unwrap()),
                        BlsScalar::zero(),
                        BlsScalar::zero(),
                    )
                });
                let mut strategy = GadgetStrategy::new(composer);
                strategy.perm(&mut inputs);
                inputs
            });

    words[1]
}

fn pad<T>(messages: &[T], width: usize, pad_value: T, eom_value: T) -> Vec<T>
where
    T: Clone,
{
    let length = messages.len() + 1;
    let arity = width - 1;
    let offset = ((length % arity) != 0) as usize;
    let size = (length / arity + offset) * width;

    let zero = pad_value;
    let one = eom_value;
    let mut words = vec![zero; size];
    let mut messages = messages.iter();

    for chunk in words.chunks_mut(width) {
        for elem in chunk.iter_mut().skip(1) {
            if let Some(message) = messages.next() {
                *elem = message.clone();
            } else {
                *elem = one;
                return words;
            }
        }
    }

    words
}

#[cfg(test)]
mod tests {
    use crate::sponge::{hash, hash_gadget, pad};
    use anyhow::Result;
    use dusk_bls12_381::BlsScalar;
    use dusk_plonk::prelude::*;

    const CAPACITY: usize = 1 << 12;

    #[test]
    fn test_scalar_padding_width_3() {
        let padder = BlsScalar::zero();
        let eom = BlsScalar::one();
        let two = BlsScalar::from(2u64);
        let three = BlsScalar::from(3u64);
        let four = BlsScalar::from(4u64);

        assert_eq!(&pad(&[two], 3, padder, eom), &[padder, two, eom]);
        assert_eq!(
            &pad(&[two, three], 3, padder, eom),
            &[padder, two, three, padder, eom, padder]
        );
        assert_eq!(
            &pad(&[two, three, four], 3, padder, eom),
            &[padder, two, three, padder, four, eom]
        );
    }

    #[test]
    fn test_scalar_padding_width_4() {
        let padder = BlsScalar::zero();
        let eom = BlsScalar::one();
        let two = BlsScalar::from(2u64);
        let three = BlsScalar::from(3u64);
        let four = BlsScalar::from(4u64);

        assert_eq!(&pad(&[two], 4, padder, eom), &[padder, two, eom, padder]);
        assert_eq!(
            &pad(&[two, three], 4, padder, eom),
            &[padder, two, three, eom]
        );
        assert_eq!(
            &pad(&[two, three, four], 4, padder, eom),
            &[padder, two, three, four, padder, eom, padder, padder]
        );
    }

    #[test]
    #[cfg(feature = "std")]
    fn test_variable_padding() {
        let mut composer = StandardComposer::new();
        let padder = composer.add_input(BlsScalar::zero());
        let eom = composer.add_input(BlsScalar::one());
        let two = composer.add_input(BlsScalar::from(2u64));
        let three = composer.add_input(BlsScalar::from(3u64));
        let four = composer.add_input(BlsScalar::from(4u64));

        assert_eq!(&pad(&[two], 3, padder, eom), &[padder, two, eom]);
        assert_eq!(
            &pad(&[two, three], 3, padder, eom),
            &[padder, two, three, padder, eom, padder]
        );
        assert_eq!(
            &pad(&[two, three, four], 3, padder, eom),
            &[padder, two, three, padder, four, eom]
        );
    }

    fn poseidon_sponge_params(width: usize) -> (Vec<BlsScalar>, BlsScalar) {
        let mut input = vec![BlsScalar::zero(); width];
        input
            .iter_mut()
            .for_each(|s| *s = BlsScalar::random(&mut rand::thread_rng()));
        let output = hash(&input);
        (input, output)
    }

    // Checks that the result of the hades permutation is the same as the one obtained by
    // the sponge gadget
    fn sponge_gadget_tester(
        width: usize,
        i: Vec<BlsScalar>,
        out: BlsScalar,
        composer: &mut StandardComposer,
    ) {
        let zero = composer.add_input(BlsScalar::zero());
        composer.constrain_to_constant(zero, BlsScalar::zero(), BlsScalar::zero());

        let mut i_var = vec![zero; width];
        i.iter().zip(i_var.iter_mut()).for_each(|(i, v)| {
            *v = composer.add_input(*i);
        });

        let o_var = composer.add_input(out);

        // Apply Poseidon Sponge hash to the inputs
        let computed_o_var = hash_gadget(composer, &i_var);

        // Check that the Gadget sponge hash result = BlsScalar sponge hash result
        composer.add_gate(
            o_var,
            computed_o_var,
            zero,
            BlsScalar::one(),
            -BlsScalar::one(),
            BlsScalar::zero(),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );
    }

    #[test]
    fn sponge_gadget_width_3() -> Result<()> {
        // Setup OG params.
        let public_parameters = PublicParameters::setup(CAPACITY, &mut rand::thread_rng())?;
        let (ck, vk) = public_parameters.trim(CAPACITY)?;

        // Test with width = 3

        // Proving
        let (i, o) = poseidon_sponge_params(3usize);
        let mut prover = Prover::new(b"sponge_tester");
        sponge_gadget_tester(3usize, i.clone(), o, prover.mut_cs());
        prover.preprocess(&ck)?;
        let proof = prover.prove(&ck)?;

        // Verify
        let mut verifier = Verifier::new(b"sponge_tester");
        sponge_gadget_tester(3usize, i, o, verifier.mut_cs());
        verifier.preprocess(&ck)?;
        verifier.verify(&proof, &vk, &vec![BlsScalar::zero()])
    }

    #[test]
    fn sponge_gadget_hades_width() -> Result<()> {
        // Setup OG params.
        let public_parameters = PublicParameters::setup(CAPACITY, &mut rand::thread_rng())?;
        let (ck, vk) = public_parameters.trim(CAPACITY)?;

        // Test with width = 5

        // Proving
        let (i, o) = poseidon_sponge_params(hades252::WIDTH);
        let mut prover = Prover::new(b"sponge_tester");
        sponge_gadget_tester(hades252::WIDTH, i.clone(), o, prover.mut_cs());
        prover.preprocess(&ck)?;
        let proof = prover.prove(&ck)?;

        // Verify
        let mut verifier = Verifier::new(b"sponge_tester");
        sponge_gadget_tester(hades252::WIDTH, i, o, verifier.mut_cs());
        verifier.preprocess(&ck)?;
        verifier.verify(&proof, &vk, &vec![BlsScalar::zero()])
    }

    #[test]
    fn sponge_gadget_width_15() -> Result<()> {
        // Setup OG params.
        let public_parameters = PublicParameters::setup(1 << 17, &mut rand::thread_rng())?;
        let (ck, vk) = public_parameters.trim(1 << 17)?;

        // Test with width = 15

        // Proving
        let (i, o) = poseidon_sponge_params(15usize);
        let mut prover = Prover::new(b"sponge_tester");
        sponge_gadget_tester(15usize, i.clone(), o, prover.mut_cs());
        prover.preprocess(&ck)?;
        let proof = prover.prove(&ck)?;

        // Verify
        let mut verifier = Verifier::new(b"sponge_tester");
        sponge_gadget_tester(15usize, i, o, verifier.mut_cs());
        verifier.preprocess(&ck)?;
        verifier.verify(&proof, &vk, &vec![BlsScalar::zero()])
    }
}
