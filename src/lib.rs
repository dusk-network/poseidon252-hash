// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(external_doc)]
#![doc(include = "../README.md")]
#![warn(missing_docs)]

/// Merkle tree optimized hash implementation
pub mod merkle;

/// Sponge hash implementation
#[cfg(feature = "std")]
pub mod sponge;
