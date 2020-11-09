use core::cmp;
use dusk_bls12_381::BlsScalar;
use hades252::strategies::{ScalarStrategy, Strategy};

#[cfg(feature = "std")]
use dusk_plonk::prelude::*;
#[cfg(feature = "std")]
use hades252::strategies::GadgetStrategy;

const WIDTH: usize = hades252::WIDTH - 1;

/// Maximum length of an input for [`hash`]
pub const fn width() -> usize {
    WIDTH
}

/// Truncate a set of messages to [`width()`] and set the first element as the bitflags
/// representing the provided input
pub fn prepare_input(input: &[BlsScalar], perm: &mut [BlsScalar; hades252::WIDTH]) {
    let n = cmp::min(input.len(), width());

    let mut mask = 0;
    (0..n).fold(1, |flag, _| {
        mask |= flag;
        flag << 1
    });
    perm[0] = BlsScalar::from(mask);

    perm[1..n + 1].copy_from_slice(&input[0..n]);
}

/// Perform the Hades252 permutation
pub fn permutate(input: &mut [BlsScalar; hades252::WIDTH]) -> BlsScalar {
    ScalarStrategy::new().perm(input);

    input[1]
}

/// Perform the poseidon hash of a provided set of scalars.
///
/// The input will be truncated with [`prepare_input`]
///
/// The permutation is provided by [`permutate`]
pub fn hash(input: &[BlsScalar]) -> BlsScalar {
    let mut perm = [BlsScalar::zero(); hades252::WIDTH];
    prepare_input(input, &mut perm);
    permutate(&mut perm)
}

/// Truncate a set of messages to [`width()`] and set the first element as the bitflags
/// representing the provided input
///
/// Mirror implementation of [`prepare_input`] for a given plonk circuit
#[cfg(feature = "std")]
pub fn prepare_input_gadget(
    composer: &mut StandardComposer,
    input: &[BlsScalar],
    perm: &mut [Variable; hades252::WIDTH],
) {
    let n = cmp::min(input.len(), width());

    let mut mask = 0;
    (0..n).fold(1, |flag, _| {
        mask |= flag;
        flag << 1
    });

    let flag = BlsScalar::from(mask);
    let flag = composer.add_input(flag);
    perm[0] = flag;

    perm.iter_mut()
        .skip(1)
        .zip(input.iter())
        .for_each(|(p, i)| *p = composer.add_input(*i));
}

/// Perform the Hades252 permutation inside of a circuit
///
/// Mirror implementation of [`permutate`]
#[cfg(feature = "std")]
pub fn permutate_gadget(
    composer: &mut StandardComposer,
    input: &mut [Variable; hades252::WIDTH],
) -> Variable {
    GadgetStrategy::new(composer).perm(input);

    input[1]
}

/// Perform the poseidon hash of a provided set of circuit variables.
///
/// Mirror the implementation of [`hash`] for a circuit
#[cfg(feature = "std")]
pub fn hash_gadget(composer: &mut StandardComposer, input: &[BlsScalar]) -> Variable {
    let zero = composer.add_witness_to_circuit_description(BlsScalar::zero());

    let mut perm = [zero; hades252::WIDTH];
    prepare_input_gadget(composer, input, &mut perm);

    permutate_gadget(composer, &mut perm)
}

#[cfg(test)]
mod tests {
    use crate::merkle::{hash, prepare_input, width};
    use dusk_bls12_381::BlsScalar;

    #[cfg(feature = "std")]
    use crate::merkle::hash_gadget;
    #[cfg(feature = "std")]
    use anyhow::Result;
    #[cfg(feature = "std")]
    use dusk_plonk::prelude::*;

    #[test]
    fn bitflags() {
        let mut perm = [BlsScalar::zero(); hades252::WIDTH];

        // Test all possible bitflags for a constant width 5
        //
        // If the width changes, then some other test cases need to be added
        assert_eq!(width(), 4);

        prepare_input(&[], &mut perm);
        assert_eq!(BlsScalar::from(0b0000), perm[0]);

        prepare_input(&[BlsScalar::zero(); 1], &mut perm);
        assert_eq!(BlsScalar::from(0b0001), perm[0]);

        prepare_input(&[BlsScalar::zero(); 2], &mut perm);
        assert_eq!(BlsScalar::from(0b0011), perm[0]);

        prepare_input(&[BlsScalar::zero(); 3], &mut perm);
        assert_eq!(BlsScalar::from(0b0111), perm[0]);

        prepare_input(&[BlsScalar::zero(); 4], &mut perm);
        assert_eq!(BlsScalar::from(0b1111), perm[0]);

        prepare_input(&[BlsScalar::zero(); 5], &mut perm);
        assert_eq!(BlsScalar::from(0b1111), perm[0]);

        prepare_input(&[BlsScalar::zero(); 6], &mut perm);
        assert_eq!(BlsScalar::from(0b1111), perm[0]);

        prepare_input(&[BlsScalar::zero(); 7], &mut perm);
        assert_eq!(BlsScalar::from(0b1111), perm[0]);

        prepare_input(&[BlsScalar::zero(); 8], &mut perm);
        assert_eq!(BlsScalar::from(0b1111), perm[0]);
    }

    #[test]
    fn merkle_deterministic() {
        let a = hash(&[BlsScalar::from(32), BlsScalar::from(31)]);
        let b = hash(&[BlsScalar::from(32), BlsScalar::from(31)]);
        let c = hash(&[BlsScalar::from(32), BlsScalar::from(33)]);

        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    #[cfg(feature = "std")]
    fn merkle_preimage() -> Result<()> {
        const CAPACITY: usize = 1 << 10;

        let pub_params = PublicParameters::setup(CAPACITY, &mut rand::thread_rng())?;
        let (ck, ok) = pub_params.trim(CAPACITY)?;

        let label = b"merkle_hash_gadget";
        fn execute(
            label: &'static [u8],
            ck: &CommitKey,
            ok: &OpeningKey,
            input: &[BlsScalar],
        ) -> Result<()> {
            let gadget_tester = |composer: &mut StandardComposer, input: &[BlsScalar]| {
                let hash = hash(input);
                let hash_p = hash_gadget(composer, input);

                composer.constrain_to_constant(hash_p, BlsScalar::zero(), -hash);
            };

            let mut prover = Prover::new(label);
            gadget_tester(prover.mut_cs(), &input);
            prover.preprocess(ck)?;
            let proof = prover.prove(ck)?;

            let mut verifier = Verifier::new(label);
            gadget_tester(verifier.mut_cs(), &input);
            verifier.preprocess(ck)?;
            let pi = verifier.mut_cs().public_inputs.clone();
            verifier.verify(&proof, ok, &pi).unwrap();

            Ok(())
        }

        execute(label, &ck, &ok, &[])?;
        execute(label, &ck, &ok, &[BlsScalar::from(25)])?;
        execute(
            label,
            &ck,
            &ok,
            &[BlsScalar::from(54), BlsScalar::from(43728)],
        )?;
        execute(
            label,
            &ck,
            &ok,
            &[
                BlsScalar::from(54),
                BlsScalar::from(43728),
                BlsScalar::from(123),
            ],
        )?;
        execute(
            label,
            &ck,
            &ok,
            &[
                BlsScalar::from(54),
                BlsScalar::from(43728),
                BlsScalar::from(5846),
                BlsScalar::from(9834),
            ],
        )?;
        execute(
            label,
            &ck,
            &ok,
            &[
                BlsScalar::from(54),
                BlsScalar::from(43728),
                BlsScalar::from(5846),
                BlsScalar::from(9834),
                BlsScalar::from(23984),
            ],
        )?;

        Ok(())
    }
}
