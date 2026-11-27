module

public import ThirteenPlanes.AlbertGrading.Recut.Recut
public import ThirteenPlanes.AlbertGrading.Grading.GradedSystem
public import ThirteenPlanes.AlbertGrading.Transport.Qutrit

@[expose] public section

/-! Transport between the two formulations of ternary gradings.

The identity on the real and imaginary parts gives a complex-linear equivalence
`Recut.JC ≃ Grading.JC` preserving the product, action and character spaces. The corresponding
real planes, point planes and line algebras are equal submodules. The facts needed for rotating
a projective line follow from `gradedSystem` and the qutrit generation theorem. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading.Transport

open ThirteenPlanes.RoundCubics

/-- The identity on real and imaginary parts, `Recut.JC ≃ Grading.JC`. -/
def jcEquiv : Recut.JC ≃ₗ[ℂ] Grading.JC where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  map_add' _ _ := by apply Grading.JC.ext <;> rfl
  map_smul' _ _ := by apply Grading.JC.ext <;> rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem jcEquiv_re (z : Recut.JC) : (jcEquiv z).re = z.re := rfl
@[simp] theorem jcEquiv_im (z : Recut.JC) : (jcEquiv z).im = z.im := rfl

theorem jcEquiv_of (x : Glennie.Albert) : jcEquiv (Recut.JC.of x) = Grading.JC.of x := rfl
theorem jcEquiv_one : jcEquiv Recut.JC.one = Grading.JC.one := rfl
theorem jcEquiv_conj (z : Recut.JC) : jcEquiv (Recut.JC.conj z) = Grading.JC.conj (jcEquiv z) :=
  rfl
theorem jcEquiv_mul (z w : Recut.JC) :
    jcEquiv (Recut.JC.mul z w) = Grading.JC.mul (jcEquiv z) (jcEquiv w) := by
  apply Grading.JC.ext
  · rw [jcEquiv_re, Grading.JC.mul_re, jcEquiv_re, jcEquiv_re, jcEquiv_im, jcEquiv_im]
    unfold Recut.JC.mul
    rfl
  · rw [jcEquiv_im, Grading.JC.mul_im, jcEquiv_re, jcEquiv_re, jcEquiv_im, jcEquiv_im]
    unfold Recut.JC.mul
    rfl
theorem jcEquiv_act (ρ : Grading.TernaryAction) (s : Charge) (z : Recut.JC) :
    jcEquiv (Recut.act ρ s z) = Grading.act ρ s (jcEquiv z) := rfl

theorem mem_charSpace_iff (ρ : Grading.TernaryAction) (g : Charge) (z : Recut.JC) :
    z ∈ Recut.charSpace ρ g ↔ jcEquiv z ∈ Grading.charSpace ρ g := by
  change (∀ s, Recut.act ρ s z = Recut.gradeCharacter s g • z) ↔
    (∀ s, Grading.act ρ s (jcEquiv z) = Grading.gradeCharacter s g • jcEquiv z)
  refine forall_congr' fun s => ?_
  rw [← jcEquiv_act, ← map_smul]
  exact jcEquiv.injective.eq_iff.symm

theorem charSpace_map (ρ : Grading.TernaryAction) (g : Charge) :
    (Recut.charSpace ρ g).map (jcEquiv : Recut.JC →ₗ[ℂ] Grading.JC) =
      Grading.charSpace ρ g := by
  ext y
  rw [Submodule.mem_map_equiv, mem_charSpace_iff, LinearEquiv.apply_symm_apply]

theorem isTernaryGrading_iff (ρ : Grading.TernaryAction) :
    Recut.IsTernaryGrading ρ ↔ Grading.IsTernaryGrading ρ := by
  constructor
  · intro h
    refine ⟨h.injective, h.automorphism, fun g => ?_⟩
    rw [← charSpace_map, LinearEquiv.finrank_map_eq]
    exact h.lineDim g
  · intro h
    refine ⟨h.injective, h.automorphism, fun g => ?_⟩
    rw [← LinearEquiv.finrank_map_eq jcEquiv, charSpace_map]
    exact h.lineDim g

theorem isNormalized_iff (u : Recut.JC) :
    Recut.IsNormalized u ↔ Grading.IsNormalized (jcEquiv u) := by
  unfold Recut.IsNormalized Grading.IsNormalized
  simp only [← jcEquiv_mul, ← jcEquiv_conj, ← jcEquiv_one, jcEquiv.injective.eq_iff]

theorem jcEquiv_framePoint (u : Recut.JC) (a : Fin 3) :
    jcEquiv (Recut.framePoint u a) = Grading.framePoint (jcEquiv u) a := by
  unfold Recut.framePoint Grading.framePoint
  rw [map_smul, map_add, map_add, map_smul, map_smul, jcEquiv_one, jcEquiv_conj]
  rfl

theorem isFrameOf_iff (u : Recut.JC) (p : Fin 3 → Glennie.Albert) :
    Recut.IsFrameOf u p ↔ Grading.IsFrameOf (jcEquiv u) p := by
  unfold Recut.IsFrameOf Grading.IsFrameOf
  refine and_congr Iff.rfl (forall_congr' fun a => ?_)
  rw [← jcEquiv_of, ← jcEquiv_framePoint, jcEquiv.injective.eq_iff]

theorem gradedPlaneJ_eq (ρ : Grading.TernaryAction) (g : Charge) :
    Recut.gradedPlaneJ ρ g = Grading.gradedPlaneJ ρ g := by
  ext x
  simp only [Recut.gradedPlaneJ, Grading.gradedPlaneJ, Submodule.mem_comap,
    Submodule.restrictScalars_mem]
  rw [← charSpace_map ρ g, ← charSpace_map ρ (-g), ← Submodule.map_sup,
    Submodule.mem_map_equiv]
  rfl

theorem gradedPlane_eq (ρ : Grading.TernaryAction) (g : Charge) :
    Recut.gradedPlane ρ g = Grading.gradedPlane ρ g := by
  simp only [Recut.gradedPlane, Grading.gradedPlane, gradedPlaneJ_eq]

theorem pointPlane_eq (ρ : Grading.TernaryAction) (p : SignedPlaneIndex) :
    Recut.pointPlane ρ p = Grading.pointPlane ρ p := gradedPlane_eq ρ _

theorem lineAlgebraOf_eq (ρ : Grading.TernaryAction) (l : SignedPlaneIndex) :
    Recut.lineAlgebraOf ρ l = Grading.lineAlgebraOf ρ l := by
  simp only [Recut.lineAlgebraOf, Grading.lineAlgebraOf, gradedPlaneJ_eq]

/-- The five graded-system facts used for rotating a projective line. -/
theorem gradedFacts_of (hQ : FrameProperties.QutritGeneration) : Recut.GradingData.GradedFacts := by
  intro ρ hρR
  have hρ : Grading.IsTernaryGrading ρ := (isTernaryGrading_iff ρ).mp hρR
  obtain ⟨-, -, -, -, hii, hiii, -, hiv, hivs, hv, -⟩ := gradedSystem hQ ρ hρ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg u hu hn
    obtain ⟨p, hfr, -, hpl, hker⟩ :=
      (hii g hg).2.2 (jcEquiv u) ((mem_charSpace_iff ρ g u).mp hu) ((isNormalized_iff u).mp hn)
    refine ⟨p, (isFrameOf_iff u p).mpr hfr, ?_, ?_⟩
    · rw [gradedPlane_eq]; exact hpl
    · rw [gradedPlaneJ_eq]; exact hker
  · intro u P hP
    refine hiii (fun g => jcEquiv (u g)) P fun g hg => ?_
    obtain ⟨h1, h2, h3⟩ := hP g hg
    exact ⟨(mem_charSpace_iff ρ g _).mp h1, (isNormalized_iff _).mp h2,
      (isFrameOf_iff _ _).mp h3⟩
  · intro p q r r' h1 h2 h3 h4 h5 h6 h7 h8
    simp only [pointPlane_eq]
    exact hiv p q r r' h1 h2 h3 h4 h5 h6 h7 h8
  · intro p q r h1 h2 h3
    simp only [pointPlane_eq]
    exact hivs p q r h1 h2 h3
  · intro l
    simp only [lineAlgebraOf_eq]
    exact (hv l).1

/-- `Recut.Section5.GradedFacts`, discharged inside the block. -/
theorem gradedFacts : Recut.GradingData.GradedFacts := gradedFacts_of qutritGeneration

/-- Ternary grading theorem, with its Section 3 hypothesis discharged by the generation by triples of closed planes (i). -/
theorem gradedSystem_fromFramePairs : Statements.GradedSystem := gradedSystem qutritGeneration

/-- Rotation of four planes on a graded line, with no hypothesis. -/
theorem rotatedSystems_fromFramePairs : Recut.Statements.OtherSystems := Recut.otherSystems gradedFacts

/-- Both predicates describe the same ternary gradings. The reference grading therefore
also provides an instance of the hypothesis of `Recut.Targets.OtherSystems`. -/
theorem recut_isTernaryGrading_iff (ρ : Grading.TernaryAction) :
    Recut.IsTernaryGrading ρ ↔ Grading.IsTernaryGrading ρ := isTernaryGrading_iff ρ

end ThirteenPlanes.AlbertGrading.Transport
