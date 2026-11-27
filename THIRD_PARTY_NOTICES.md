The three modules under ThirteenPlanes/Tits named C1Coordinates, TitsLinear and TitsSquare adapt the corresponding AlbertLean/Generic sources from the albert-frame-triple-invariants package at dd06ef5d423a0e4a5d814d2c221e999b98887ee1, under Apache-2.0. Their module imports were adapted for Lean 4.36. The included copies omit local diagnostic commands from the two computational modules. The Apache license is included in LICENSE.

The external proof dependencies are recorded in [lakefile.toml](lakefile.toml). The sequential-measurements dependency retains its Apache-2.0 license and notices. [Registered dependency, v1](https://data.palomar-registry.org/entries/PALOMAR-2026-11-27-000005-v1.json). The package also contains the four Tau Ceti proof modules identified below.

Tits/TraceCubic.lean includes the two trace-pairing lemmas and the trace-cube lemma adapted from TitsDetectorIdentities.lean and TitsTraceCube.lean at the same revision.

`ThirteenPlanes/NativeTits.lean` specializes the compact first-Tits coordinates `TitsS.titsOfNative` from `Proofs/TitsForm.lean` in the earlier tight 39-point formalization. The specialization uses the pinned native Albert carrier and takes the third slot by conjugate transpose. [Included specialization](src/ThirteenPlanes/NativeTits.lean), [pinned source](https://github.com/macgregor-sudo/tight-39-code/blob/46f01c135aacea9003435e7f1dc99b4a69568e83/Proofs/TitsForm.lean#L61), [registered source formalization](https://palomar-registry.org/entry?id=PALOMAR-2026-10-29-000034&version=1).

The independent statement and its proof-side definitions use the Cayley–Dickson product, conjugation and octonionic Hermitian upper-entry coordinates from the Apache-2.0 [Albert Sequential Measurements statement](https://github.com/macgregor-sudo/albert-sequential-measurements/blob/10e5ca8ce341a1cb3a812569d3081005a40007c8/src/Challenge.lean). The carriers and trace-cubic predicates here use the notation of the current manuscript.

## Tau Ceti proof sources

The four modules below reproduce the complete upstream implementations from Tau Ceti
at commit `d91980bdc255e6e50506be147ad9bcb88eb9fcc0`. Their original headers and file bytes are retained at the
start of each file. The package appends one attribution comment per file, including a Newton quotation as an editorial acknowledgment.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
The package thanks the Tau Ceti contributors. The files use Apache-2.0 under the
[upstream grant](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/LICENSE), reproduced verbatim in [LICENSE](LICENSE).

- [TauCeti/Data/Fin/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Data/Fin/Basic.lean) · [included source](src/TauCeti/Data/Fin/Basic.lean)
- [TauCeti/Algebra/Octonion/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Algebra/Octonion/Basic.lean) · [included source](src/TauCeti/Algebra/Octonion/Basic.lean)
- [TauCeti/Algebra/AlbertAlgebra/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Algebra/AlbertAlgebra/Basic.lean) · [included source](src/TauCeti/Algebra/AlbertAlgebra/Basic.lean)
- [TauCeti/Algebra/AlbertAlgebra/Determinant.lean](https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/Algebra/AlbertAlgebra/Determinant.lean) · [included source](src/TauCeti/Algebra/AlbertAlgebra/Determinant.lean)
