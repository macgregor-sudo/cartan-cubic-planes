module

public import ThirteenPlanes.AlbertGrading.Recognition.NormalCoords
public import FrameSlotNormalizers
public import AcceptedRootAtomAdapter

@[expose] public section

/-!
# `OrbitHypotheses.PairNormalization` from the unbiased-pair and slot normal forms (i)

The unbiased-pair normal form gives the diagonal frame and a Fourier frame over `ℂ_u`.
Applying an octonion automorphism that sends `u` to `i` entrywise fixes the diagonal frame
and moves the Fourier frame to `ℂ_i`. The isomorphism `𝔸 ≃ J_T` takes them to the eigenframes
of `ι₀(Z)` and `ι₀(X)`.

`AlbertSequential.exists_octAuto_imag_to_I` supplies the octonion automorphism.
`octAutoToAlbertAuto` and `nativeAutoToCompactAuto` transport it to `Glennie.Albert`.



-/

open scoped Matrix BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

theorem psi_symm_product (x y : CompactTits) :
    nativeCompactTitsEquiv.symm (CompactTits.product x y) = Glennie.jordan (nativeCompactTitsEquiv.symm x) (nativeCompactTitsEquiv.symm y) := by
  apply nativeCompactTitsEquiv.injective
  rw [nativeCompactTitsEquiv_product]
  simp

theorem psi_symm_trace (x : CompactTits) : Glennie.trace (nativeCompactTitsEquiv.symm x) = CompactTits.trace x := by
  rw [← nativeCompactTitsEquiv_trace, LinearIsometryEquiv.apply_symm_apply]

theorem psi_symm_one : nativeCompactTitsEquiv.symm CompactTits.one = 1 := by
  rw [← nativeCompactTitsEquiv_one, LinearIsometryEquiv.symm_apply_apply]

theorem frame_of_tits {P : ZMod 3 → CompactTits} (hP : IsTitsFrame P) :
    Glennie.Frame (fun a : Fin 3 => nativeCompactTitsEquiv.symm (P a)) where
  trace_one i := by rw [psi_symm_trace]; exact hP.2.1 i
  idempotent i := by
    rw [← psi_symm_product]
    have h := hP.1 i i
    split_ifs at h with h'
    · rw [h]
    · exact absurd rfl h'
  orthogonal i j hij := by
    rw [← psi_symm_product]
    have h := hP.1 i j
    split_ifs at h with h'
    · exact absurd h' hij
    · rw [h, map_zero]
  sum_unit := by
    have h := congrArg nativeCompactTitsEquiv.symm hP.2.2
    rw [map_sum, sum_zmod3, psi_symm_one] at h
    exact h

theorem IsTraceAut.frame {f : CompactTits ≃ₗ[ℝ] CompactTits} (hf : IsTraceAut f)
    {P : ZMod 3 → CompactTits} (hP : IsTitsFrame P) : IsTitsFrame (fun a => f (P a)) :=
  ⟨fun a b => by rw [← hf.1, hP.1 a b]; split <;> simp,
    fun a => by rw [hf.2, hP.2.1], by rw [← map_sum, hP.2.2, hf.map_one]⟩

/-- `Aut(𝕆)` moves a unit imaginary `u` to `i`, and its entrywise action fixes the diagonal frame
and carries the Fourier frame over `ℂ_u` to the one over `ℂ_i`. -/
/- Transitivity on unit imaginary octonions is described by John Baez, The Octonions, §4.1
(arXiv:math/0105155). The proof uses `AlbertSequential.exists_octAuto_imag_to_I` and
extends the octonion automorphism to the native Albert algebra. -/
theorem octonion_step (u : Glennie.Octonion) (hu0 : u.1.re = 0) (hu1 : Glennie.octNormSq u = 1) :
    ∃ ψ : Glennie.CompactAutomorphism, (∀ b, ψ.equiv (Glennie.standardFrame b) =
      Glennie.standardFrame b) ∧ ∀ k, ψ.equiv (fourierFrameU u k) = fourierFrameU octI' k := by
  obtain ⟨α, r, hr, hαu⟩ := AlbertSequential.exists_octAuto_imag_to_I u hu0
  have hn := AlbertSequential.OctonionAutomorphism.map_normSq α u
  rw [hαu, AlbertSequential.octNormSq_smul] at hn
  have hI : AlbertSequential.octNormSq AlbertSequential.octI = 1 := by
    rw [AlbertSequential.octNormSq_eq_coords]; simp [AlbertSequential.octI]
  have hu : AlbertSequential.octNormSq u = 1 := by
    refine (AlbertSequential.octNormSq_eq_coords u).trans ?_
    have h := hu1
    rw [Glennie.octNormSq, Quaternion.normSq_def', Quaternion.normSq_def'] at h
    linarith
  rw [hI, hu, mul_one] at hn
  have hr1 : r = 1 := by nlinarith
  subst hr1
  rw [one_smul] at hαu
  let ψ := AlbertSequential.nativeAutoToCompactAuto (AlbertSequential.octAutoToAlbertAuto α)
  have hψ : ∀ y : Glennie.Albert, ψ.equiv y =
      ⟨y.d0, y.d1, y.d2, α.equiv y.o01, α.equiv y.o02, α.equiv y.o12⟩ := fun y => rfl
  have hα0 : α.equiv (0 : Glennie.Octonion) = (0 : Glennie.Octonion) := map_zero α.equiv
  have hω : ∀ m, α.equiv (omegaU u m) = omegaU octI' m := by
    intro m
    have e1 : α.equiv (omegaU u m) = α.equiv (AlbertSequential.octonionScalar (chargePhase m).re +
        (chargePhase m).im • (show AlbertSequential.Octonion from u)) := rfl
    rw [e1, map_add, map_smul, AlbertSequential.OctonionAutomorphism.map_scalar]
    rw [show α.equiv (show AlbertSequential.Octonion from u) = AlbertSequential.octI from hαu]
    rfl
  have hω' : ∀ (c : ℝ) m, α.equiv (c • omegaU u m) = c • omegaU octI' m := by
    intro c m
    have e : α.equiv (c • omegaU u m) = c • α.equiv (omegaU u m) := map_smul α.equiv c (omegaU u m)
    rw [e, hω]
    rfl
  refine ⟨ψ, fun b => ?_, fun k => ?_⟩
  · rw [hψ]
    rcases zmod3_cases b with rfl | rfl | rfl <;> simp [Glennie.standardFrame, hα0]
  · rw [hψ]
    simp only [fourierFrameU, hω']

theorem pairNormalization_of_normalForm (hN : FrameProperties.NormalFormOctonion) :
    OrbitHypotheses.PairNormalization := by
  intro P Q hP hQ hPQ
  obtain ⟨φ, u, hu0, hu1, hF, hG⟩ := hN (fun a => nativeCompactTitsEquiv.symm (P a)) (fun a => nativeCompactTitsEquiv.symm (Q a))
    (frame_of_tits hP) (frame_of_tits hQ) (fun a b => by
      rw [Glennie.inner, ← psi_symm_product, psi_symm_trace]; exact hPQ a b)
  obtain ⟨ψ, hψs, hψf⟩ := octonion_step u hu0 hu1
  let Φ := ψ.comp φ
  let f : CompactTits ≃ₗ[ℝ] CompactTits :=
    nativeCompactTitsEquiv.symm.toLinearEquiv.trans (Φ.equiv.trans nativeCompactTitsEquiv.toLinearEquiv)
  have hfapp : ∀ x, f x = nativeCompactTitsEquiv (ψ.equiv (φ.equiv (nativeCompactTitsEquiv.symm x))) := fun x => rfl
  have hf : IsTraceAut f := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [hfapp, hfapp, hfapp, psi_symm_product, φ.map_jordan, ψ.map_jordan,
        nativeCompactTitsEquiv_product]
    · rw [hfapp, nativeCompactTitsEquiv_trace, ψ.map_trace, φ.map_trace, psi_symm_trace]
  refine ⟨f, hf.1, hf.2, ?_, ?_⟩
  · refine range_of_span (hf.frame hP) (chargeFrom_ne_zero (by decide) 0) fun a => ?_
    obtain ⟨b, hb⟩ : φ.equiv (nativeCompactTitsEquiv.symm (P a)) ∈ Set.range Glennie.standardFrame :=
      hF ▸ ⟨a, rfl⟩
    rw [hfapp, ← hb, hψs]
    exact standard_mem b
  · refine range_of_span (hf.frame hQ) (chargeFrom_ne_zero (by decide) 0) fun a => ?_
    obtain ⟨k, hk⟩ : φ.equiv (nativeCompactTitsEquiv.symm (Q a)) ∈ Set.range (fourierFrameU u) := hG ▸ ⟨a, rfl⟩
    rw [hfapp, ← hk, hψf]
    exact fourier_mem k

end

end ThirteenPlanes.AlbertGrading
