/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.JordanFrames.AlbertNormal
public import OctonionGeometry
public import FrameSlotNormalizers

@[expose] public section

set_option backward.privateInPublic true

/-! Ordered unbiased compact Albert frame pairs in a fixed Fourier slice. -/

namespace ThirteenPlanes.JordanFrames

open AlbertSequential AlbertSequential.NativeAnalysis

private def octMap (α : OctonionAutomorphism) : Glennie.Octonion ≃ₗ[ℝ] Glennie.Octonion := α.equiv

private theorem unitImaginary_to_fixed (u : AlbertSequential.Octonion)
    (hu : Glennie.octRe u = 0) (hn : Glennie.octNormSq u = 1) :
    ∃ α : OctonionAutomorphism, octMap α u = octI := by
  obtain ⟨α, r, hr, hα⟩ := exists_octAuto_imag_to_I u hu
  have hnorm : octNormSq u = 1 := by
    rw [octNormSq_eq_coords]
    change Quaternion.normSq u.1 + Quaternion.normSq u.2 = 1 at hn
    simpa only [Quaternion.normSq_def', pow_two, add_assoc] using hn
  have hI : octNormSq octI = 1 := by rw [octNormSq_eq_coords]; simp [octI]
  have h := α.map_normSq u
  rw [hα, octNormSq_smul, hI, mul_one, hnorm] at h
  have hr1 : r = 1 := by nlinarith
  refine ⟨α, ?_⟩
  change α.equiv u = (octI : AlbertSequential.Octonion)
  rw [hα, hr1, one_smul]

private abbrev entrywiseAuto (α : OctonionAutomorphism) :=
  nativeAutoToCompactAuto (octAutoToAlbertAuto α)

private theorem entrywise_apply (α : OctonionAutomorphism) (x : Glennie.Albert) :
    (entrywiseAuto α).equiv x =
      ⟨x.d0, x.d1, x.d2, octMap α x.o01, octMap α x.o02, octMap α x.o12⟩ := by
  apply Glennie.Albert.ext <;> rfl

private theorem entrywise_frame (α : OctonionAutomorphism) (i : Fin 3) :
    (entrywiseAuto α).equiv (Glennie.standardFrame i) = Glennie.standardFrame i := by
  rw [entrywise_apply]
  fin_cases i <;> simp [Glennie.standardFrame, map_zero]

private theorem entrywise_fourier_zero (α : OctonionAutomorphism) :
    (entrywiseAuto α).equiv nativeFourierZero = nativeFourierZero := by
  have h : octMap α (Glennie.octScalar 1) = Glennie.octScalar 1 := α.map_scalar 1
  rw [entrywise_apply]
  simp only [nativeFourierZero, map_smul, h]

private theorem entrywise_fourier_phase (α : OctonionAutomorphism) (u : Glennie.Octonion) :
    (entrywiseAuto α).equiv (nativeFourierPhase u) = nativeFourierPhase (octMap α u) := by
  have h : octMap α (Glennie.octScalar 1) = Glennie.octScalar 1 := α.map_scalar 1
  have hc (v : Glennie.Octonion) : octMap α (Glennie.octConj v) = Glennie.octConj (octMap α v) :=
    α.map_conj v
  rw [entrywise_apply]
  simp only [nativeFourierPhase, hc, map_add, map_smul, h]

private theorem entrywise_fourier (α : OctonionAutomorphism) (u : Glennie.Octonion) (i : Fin 3) :
    (entrywiseAuto α).equiv (nativeFourierFrame u i) = nativeFourierFrame (octMap α u) i := by
  fin_cases i
  · exact entrywise_fourier_zero α
  · change (entrywiseAuto α).equiv (nativeFourierPhase (-u)) = nativeFourierPhase (-(octMap α u))
    rw [entrywise_fourier_phase, map_neg]
  · exact entrywise_fourier_phase α u

/-- A single automorphism carries an ordered unbiased pair to fixed ordered reference frames. -/
theorem native_unbiased_pair_fixed_fourier (p q : Fin 3 → Glennie.Albert)
    (hp : Glennie.Frame p) (hq : Glennie.Frame q)
    (unbiased : ∀ i j, Glennie.inner (p i) (q j) = 1 / 3) :
    ∃ g : Glennie.CompactAutomorphism, (∀ i, g.equiv (p i) = Glennie.standardFrame i) ∧
      (∀ i, g.equiv (q i) = nativeFourierFrame octI i) := by
  obtain ⟨g, u, hu, hn, hP, hQ⟩ := native_normalize_unbiased_pair p q hp hq unbiased
  obtain ⟨α, hα⟩ := unitImaginary_to_fixed u hu hn
  refine ⟨(entrywiseAuto α).comp g, fun i => ?_, fun i => ?_⟩
  · rw [Glennie.CompactAutomorphism.comp_apply, hP, entrywise_frame]
  · rw [Glennie.CompactAutomorphism.comp_apply, hQ, entrywise_fourier, hα]

/-- Two ordered pairs of mutually unbiased compact Albert frames are conjugate with matching labels. -/
theorem native_unbiased_pair_transitive (p q p' q' : Fin 3 → Glennie.Albert)
    (hp : Glennie.Frame p) (hq : Glennie.Frame q) (hp' : Glennie.Frame p') (hq' : Glennie.Frame q')
    (h : ∀ i j, Glennie.inner (p i) (q j) = 1 / 3)
    (h' : ∀ i j, Glennie.inner (p' i) (q' j) = 1 / 3) :
    ∃ g : Glennie.CompactAutomorphism, (∀ i, g.equiv (p i) = p' i) ∧ (∀ i, g.equiv (q i) = q' i) := by
  obtain ⟨g, hgP, hgQ⟩ := native_unbiased_pair_fixed_fourier p q hp hq h
  obtain ⟨f, hfP, hfQ⟩ := native_unbiased_pair_fixed_fourier p' q' hp' hq' h'
  refine ⟨f.symm.comp g, fun i => ?_, fun i => ?_⟩
  · rw [Glennie.CompactAutomorphism.comp_apply, Glennie.CompactAutomorphism.symm_apply, hgP, ← hfP,
      LinearEquiv.symm_apply_apply]
  · rw [Glennie.CompactAutomorphism.comp_apply, Glennie.CompactAutomorphism.symm_apply, hgQ, ← hfQ,
      LinearEquiv.symm_apply_apply]

end ThirteenPlanes.JordanFrames
