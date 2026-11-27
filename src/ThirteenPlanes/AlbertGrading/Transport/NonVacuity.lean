module

public import ThirteenPlanes.AlbertGrading.Transport.RecutBridge
public import ThirteenPlanes.AlbertGrading.GradingWitness.Witness
public import ThirteenPlanes.AlbertGrading.Generation.NonVacuity

@[expose] public section

/-! Examples realizing the hypotheses of the subalgebra, generation, and rotated-system results. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading.Transport

open AlbertSequential

/-- Two-plane subalgebra classification: a unit imaginary octonion exists and the whole Albert algebra contains
`H₃(ℂ_u)`. -/
theorem subalgebras_nonvacuous : ∃ u : Octonion, octonionReal u = 0 ∧ octNormSq u = 1 ∧
    ∀ x : Albert, (∀ k : Fin 3, x.2 k ∈ complexLine u) →
      x ∈ (⊤ : NativeJordanSubalgebra).carrier :=
  ⟨octI, rfl, by
    norm_num [octNormSq, octDot, octonionMul, octonionConj, octonionReal, octI],
    fun _ _ => trivial⟩

/-- Generation by triples of closed planes: an actual thirteen-plane system exists and three of its frames have pairwise
orthogonal planes. -/
theorem generation_nonvacuous : ∃ c : TightNativeCode,
    (nativeFramePlane (c.point 0)).IsOrtho (nativeFramePlane (c.point 1)) ∧
    (nativeFramePlane (c.point 0)).IsOrtho (nativeFramePlane (c.point 2)) ∧
    (nativeFramePlane (c.point 1)).IsOrtho (nativeFramePlane (c.point 2)) :=
  ⟨Graded.nativeCode, Graded.nativeCode.planes_orthogonal (show (0 : Fin 13) ≠ 1 by decide),
    Graded.nativeCode.planes_orthogonal (show (0 : Fin 13) ≠ 2 by decide),
    Graded.nativeCode.planes_orthogonal (show (1 : Fin 13) ≠ 2 by decide)⟩

/-- Rotation of four planes on a graded line: an actual ternary grading, a full
choice of normalized elements `u_g ∈ A_g` with their frames, and for every line an automorphism of
its qutrit (the identity) exist, so every hypothesis of `Recut.Targets.OtherSystems` is met. -/
theorem otherSystems_nonvacuous : ∃ ρ : Grading.TernaryAction, Recut.IsTernaryGrading ρ ∧
    ∃ (u : Charge → Recut.JC) (P : Charge → Fin 3 → Glennie.Albert),
      (∀ g, g ≠ 0 → u g ∈ Recut.charSpace ρ g ∧ Recut.IsNormalized (u g) ∧
        Recut.IsFrameOf (u g) (P g)) ∧
      ∀ l : SignedPlaneIndex, Recut.IsSubalgebraAutomorphism (Recut.lineAlgebraOf ρ l)
        (LinearEquiv.refl ℝ (Recut.lineAlgebraOf ρ l)) := by
  obtain ⟨ρ, hρ⟩ := ternaryGradingExists
  obtain ⟨-, -, -, -, hii, -⟩ := gradedSystem_fromFramePairs ρ hρ
  have H : ∀ g : Charge, ∃ (v : Recut.JC) (p : Fin 3 → Glennie.Albert), g ≠ 0 →
      v ∈ Recut.charSpace ρ g ∧ Recut.IsNormalized v ∧ Recut.IsFrameOf v p := by
    intro g
    by_cases hg : g = 0
    · exact ⟨0, fun _ => 0, fun h => (h hg).elim⟩
    obtain ⟨w, hw, hn⟩ := (hii g hg).1
    obtain ⟨p, hfr, -⟩ := (hii g hg).2.2 w hw hn
    refine ⟨jcEquiv.symm w, p, fun _ => ⟨?_, ?_, ?_⟩⟩
    · rw [mem_charSpace_iff, LinearEquiv.apply_symm_apply]; exact hw
    · rw [isNormalized_iff, LinearEquiv.apply_symm_apply]; exact hn
    · rw [isFrameOf_iff, LinearEquiv.apply_symm_apply]; exact hfr
  choose u P hP using H
  refine ⟨ρ, (isTernaryGrading_iff ρ).mpr hρ, u, P, hP, fun l x y h => ?_⟩
  simp only [LinearEquiv.refl_apply]

end ThirteenPlanes.AlbertGrading.Transport
