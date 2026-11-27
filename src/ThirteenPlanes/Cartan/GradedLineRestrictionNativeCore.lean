module

public import ThirteenPlanes.Cartan.GradedLineRestrictionCore
public import ThirteenPlanes.Cartan.AlbertGradingBasis
public import ThirteenPlanes.AlbertGrading.Grading.GradedIncidence
public import ThirteenPlanes.SignedSupport

@[expose] public section

set_option backward.privateInPublic true

/-! The real line in the actual compact Albert carrier and its ambient derivation subspace. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading AlbertGrading.Grading.JC Module

noncomputable section

namespace NormalizedTernaryBasis

private def mapCLinear : Module.End ℝ Glennie.Albert →ₗ[ℝ] Module.End ℂ JC where
  toFun := mapC
  map_add' f g := by
    apply LinearMap.ext
    intro z
    apply JC.ext <;> rfl
  map_smul' r f := by
    apply LinearMap.ext
    intro z
    apply JC.ext
    · change (mapC (r • f) z).re = (r • mapC f z).re
      rw [real_smul_re, mapC_re, mapC_re, LinearMap.smul_apply]
    · change (mapC (r • f) z).im = (r • mapC f z).im
      rw [real_smul_im, mapC_im, mapC_im, LinearMap.smul_apply]

/-- The real operators whose complex extensions belong to the derivation grades of the line. -/
def realLineDerivations (M : NormalizedTernaryBasis JC) (L : Submodule (ZMod 3) Charge) :
    Submodule ℝ (Module.End ℝ Glennie.Albert) :=
  ((M.lineDerivations L).restrictScalars ℝ).comap mapCLinear

@[simp] theorem mem_realLineDerivations (M : NormalizedTernaryBasis JC) (L : Submodule (ZMod 3) Charge)
    {D : Module.End ℝ Glennie.Albert} : D ∈ M.realLineDerivations L ↔ mapC D ∈ M.lineDerivations L :=
  Iff.rfl

theorem realLineDerivations_bracket (M : NormalizedTernaryBasis JC) (L : Submodule (ZMod 3) Charge)
    {D E : Module.End ℝ Glennie.Albert} (hD : D ∈ M.realLineDerivations L)
    (hE : E ∈ M.realLineDerivations L) : operatorBracket D E ∈ M.realLineDerivations L := by
  apply (M.mem_realLineDerivations L).mpr
  have h : mapC (operatorBracket D E) = operatorBracket (mapC D) (mapC E) := by
    apply LinearMap.ext
    intro x
    apply JC.ext <;> rfl
  rw [h]
  exact M.lineDerivations_bracket L (M.mem_realLineDerivations L |>.mp hD)
    (M.mem_realLineDerivations L |>.mp hE)

end NormalizedTernaryBasis

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ) (l : SignedPlaneIndex)

local notation "M" => albertGradingBasis hρ
local notation "L" => signedProjectiveLine l
local notation "Q" => lineAlgebraOf ρ l
local notation "Qc" => NormalizedTernaryBasis.gradedLineSubspace (albertGradingBasis hρ) (signedProjectiveLine l)

private theorem charSpace_le_lineSpace {g : Charge} (hg : g ∈ L) : charSpace ρ g ≤ Qc := by
  intro z hz
  obtain ⟨c, rfl⟩ := exists_smul_of_mem hρ (albertGradingBasis_mem_charSpace hρ g) ((M).basis.ne_zero g) hz
  exact (Qc).smul_mem c ((M).basis_mem_gradedLineSubspace L ⟨g, hg⟩)

theorem of_mem_gradedLineSubspace_of_mem_lineAlgebra {x : Glennie.Albert} (hx : x ∈ Q) :
    of x ∈ Qc := by
  refine Submodule.span_induction (p := fun x _ => of x ∈ Qc) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with h | h
    · have hy : y = 1 := h
      subst y
      have h0 := (M).basis_mem_gradedLineSubspace L 0
      change one ∈ Qc
      simpa only [Submodule.coe_zero, albertGradingBasis_unit] using h0
    · simp only [Set.mem_iUnion] at h
      obtain ⟨p, hp, hp'⟩ := h
      have hp0 : p.val.val ∈ L := hp
      have hle : charSpace ρ p.val.val ⊔ charSpace ρ (-p.val.val) ≤ Qc :=
        sup_le (charSpace_le_lineSpace hρ l hp0) (charSpace_le_lineSpace hρ l ((L).neg_mem hp0))
      exact hle hp'
  · simp [of_zero]
  · intro y z _ _ hy hz
    rw [of_add]
    exact (Qc).add_mem hy hz
  · intro r y _ hy
    rw [of_smul]
    exact ((Qc).restrictScalars ℝ).smul_mem r hy

include hρ in
private theorem re_mem_lineAlgebra_of_mem_charSpace (g : L) {z : JC}
    (hz : z ∈ charSpace ρ g.val) : z.re ∈ Q := by
  by_cases hg : g.val = 0
  · have hc : z ∈ Submodule.span ℂ {one} := by simpa only [hg, charSpace_zero_eq hρ] using hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hc
    have h1 : (1 : Glennie.Albert) ∈ Q := Submodule.subset_span (Or.inl (by rfl))
    simpa [JC.one] using (Q).smul_mem c.re h1
  have hr := re_mem_gradedPlaneJ (Submodule.mem_sup_left hz : z ∈ charSpace ρ g.val ⊔ charSpace ρ (-g.val))
  have rep_has_mem (p : SignedPlaneIndex) (he : p.val.val = g.val ∨ p.val.val = -g.val) : z.re ∈ Q := by
    have hp : signedPointOnLine p l := by
      rcases he with h | h
      · rw [signedPointOnLine, h]
        exact g.property
      · rw [signedPointOnLine, h]
        exact (L).neg_mem g.property
    have hplane : z.re ∈ gradedPlaneJ ρ p.val.val := by
      rcases he with h | h
      · rwa [h]
      · rwa [h, gradedPlaneJ_neg]
    exact Submodule.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hplane⟩⟩))
  by_cases hrep : isChargeRepresentative g.val
  · exact rep_has_mem ⟨⟨g.val, hg⟩, hrep⟩ (Or.inl rfl)
  · exact rep_has_mem ⟨⟨-g.val, neg_ne_zero.mpr hg⟩,
      (oppositeCharge_isRepresentative_iff ⟨g.val, hg⟩).mpr hrep⟩ (Or.inr rfl)

/-- The real component of any vector with line support lies in the literal real line algebra. -/
theorem re_mem_lineAlgebra_of_mem_gradedLineSubspace {z : JC} (hz : z ∈ Qc) : z.re ∈ Q := by
  let S : Submodule ℂ JC :=
    { carrier := {z | z.re ∈ Q ∧ z.im ∈ Q}
      zero_mem' := by simp
      add_mem' := fun hx hy => ⟨(Q).add_mem hx.1 hy.1, (Q).add_mem hx.2 hy.2⟩
      smul_mem' := fun c z hz => ⟨(Q).sub_mem ((Q).smul_mem c.re hz.1) ((Q).smul_mem c.im hz.2),
        (Q).add_mem ((Q).smul_mem c.re hz.2) ((Q).smul_mem c.im hz.1)⟩ }
  have hle : Qc ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    have hχ := albertGradingBasis_mem_charSpace hρ g.val
    refine ⟨re_mem_lineAlgebra_of_mem_charSpace hρ l g hχ, ?_⟩
    have hi := re_mem_lineAlgebra_of_mem_charSpace hρ l g ((charSpace ρ g.val).smul_mem (-Complex.I) hχ)
    simpa using hi
  exact (hle hz).1

theorem im_mem_lineAlgebra_of_mem_gradedLineSubspace {z : JC} (hz : z ∈ Qc) : z.im ∈ Q := by
  have h := re_mem_lineAlgebra_of_mem_gradedLineSubspace hρ l ((Qc).smul_mem (-Complex.I) hz)
  simpa using h

/-- For vectors on the compact real form, membership agrees with the manuscript's line algebra. -/
theorem of_mem_gradedLineSubspace_iff (x : Glennie.Albert) : of x ∈ Qc ↔ x ∈ Q :=
  ⟨fun h => re_mem_lineAlgebra_of_mem_gradedLineSubspace hρ l h,
    of_mem_gradedLineSubspace_of_mem_lineAlgebra hρ l⟩

end

end ThirteenPlanes.Cartan
