# Physical cut trace and logarithm

`Rank7RealCutSpectrum.lean` converts the selected principal compression to a Mathlib complex Hermitian matrix. Its diagonalization produces a project `SpectralWitness`, with the matrix product, adjoint, and diagonal checked in the original list representation. `physicalCutLower` proves the bound for a specified trace decomposition. `physicalCutRounding` supplies a suitable decomposition and price for every cut of an actual orthonormal seven-column frame.

The Lean 4.36.0 project in this directory pins Mathlib at its corresponding release. The parent project has a bundled-library build. The spectral theorem used here is in [Mathlib's matrix spectrum module](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Matrix/Spectrum.lean).

To check this package, run the following from this directory with the complete Lean 4.36.0 toolchain.

```sh
lake update
lake exe cache get Mathlib/Analysis/Matrix/Spectrum.lean Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
lake build
```

The exported dependency reports use only `propext`, `Classical.choice`, and `Quot.sound`. Lake reports an import-format warning because this file connects the parent's legacy Lean modules to Mathlib's module-system files. `entropyOrder` checks the order reversal after taking the negative logarithm of positive purity values.

[Rank7RealUpperCutPrice.lean](Rank7RealUpperCutPrice.lean) identifies the shared and highest trace offsets with the actual exterior weights of the physical frame. `actualTracePrices` proves both fractional lower prices, including the integral endpoint of the shared trace. `supportedCompression` bounds the combined prices by the actual compression loss with the outside-coordinate charge written explicitly.

[Rank7RealTiedCutPrice.lean](Rank7RealTiedCutPrice.lean) proves the original affine supports for the complete upper tied chart. The theorem `physicalTiedCompression` supplies both actual trace prices and bounds the compression loss with the single 1234 entering-wedge allowance.

[Rank7RealUpperPhysicalComparison.lean](Rank7RealUpperPhysicalComparison.lean) combines the signed corner, Pauli and compression inequalities into the paired-defect comparison for an actual orthonormal frame on the normalized upper chart. Its large-Gram entry point proves the two quantitative Gram bounds internally when `24*kappa >= 1` and `15*kappaOne >= 2`. The frontier theorem preserves the older and weighted scalar classifications and every open box.

[Rank7RealLowerCutPrice.lean](Rank7RealLowerCutPrice.lean) checks the lower shared compression payment at the full nominal width after rescaling by the tied probabilities. It retains the exact 1234 entering-wedge allowance.

[Rank7RealLowerPhysicalComparison.lean](Rank7RealLowerPhysicalComparison.lean) proves the original-spectrum physical paired-defect inequality from an accepted shared margin. It matches the exact raw Pauli prices and raw compression loss. `checkedSlabLarge` derives the four radicals and the geometry inequalities at the same large-Gram thresholds as the upper comparison. Its input is a successful Boolean lower replay and its output retains the old and weighted scalar classifications.

[Rank7RealLowerSmallHead.lean](Rank7RealLowerSmallHead.lean) proves the physical small-head exit directly from the ordered spectral chart. [Rank7RealLowerAllWeighted.lean](Rank7RealLowerAllWeighted.lean) handles all four weighted shifts on the nonpositive-head subregion with the two displayed Gram conditions.

[Rank7RealPhysicalHighest.lean](Rank7RealPhysicalHighest.lean) uses the unconditional highest-pair theorem in covered upper corners, the lower shared replay, and the proved lower weighted subregion. Its Gram premise is the single shared threshold `24*kappa >= 1`.
