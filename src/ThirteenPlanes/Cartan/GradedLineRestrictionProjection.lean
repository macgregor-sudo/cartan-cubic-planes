module

public import ThirteenPlanes.Cartan.GradedLineRestrictionCore

@[expose] public section

set_option backward.privateInPublic true

/-! Homogeneous components on the line are projections of the actual line product. -/

open scoped BigOperators
open Module

namespace ThirteenPlanes.Cartan.NormalizedTernaryBasis

noncomputable section

variable {A : Type*} [AddCommGroup A] [Module ℂ A] (M : NormalizedTernaryBasis A)
variable (L : Submodule (ZMod 3) Charge)

local instance : Fintype L := Fintype.ofFinite L

local notation "Q" => M.gradedLineSubspace L
local notation "b" => M.gradedLineBasis L
local notation "μ" => M.gradedLineProduct L

/-- Extend a linear operator on the line by zero on the remaining character lines. -/
def gradedLineExtend (D : Module.End ℂ Q) : Module.End ℂ A := by
  classical
  exact M.basis.constr ℂ fun g => if hg : g ∈ L then (D (b ⟨g, hg⟩) : A) else 0

theorem gradedLineExtend_on_line (D : Module.End ℂ Q) (x : Q) :
    M.gradedLineExtend L D x.val = (D x : A) := by
  suffices (M.gradedLineExtend L D).comp (Q).subtype = (Q).subtype.comp D by
    exact LinearMap.congr_fun this x
  apply (b).ext
  intro g
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, M.gradedLineBasis_coe]
  rw [gradedLineExtend, Basis.constr_basis, dite_eq_left g.property]

theorem gradedLineBasis_coord (g : L) (x : Q) :
    M.basis.coord g.val x.val = (b).coord g x := by
  suffices (M.basis.coord g.val).comp (Q).subtype = (b).coord g by
    exact LinearMap.congr_fun this x
  apply (b).ext
  intro h
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, M.gradedLineBasis_coe,
    Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, Subtype.ext_iff]

/-- The degree-γ part of an actual endomorphism of the line. -/
def gradedLineDegreeProjection (γ : L) (D : Module.End ℂ Q) : Module.End ℂ Q :=
  (M.degreeProjection γ.val (M.gradedLineExtend L D)).comp (Q).subtype |>.codRestrict Q
    (fun x => M.grade_preserves_line L (M.degreeProjection_hasDegree _ _) x.property)

@[simp] theorem gradedLineDegreeProjection_coe (γ : L) (D : Module.End ℂ Q) (x : Q) :
    (M.gradedLineDegreeProjection L γ D x : A) =
      M.degreeProjection γ.val (M.gradedLineExtend L D) x.val := rfl

theorem gradedLineDegreeProjection_on_basis (γ g : L) (D : Module.End ℂ Q) :
    M.gradedLineDegreeProjection L γ D (b g) = ((b).coord (g + γ) (D (b g))) • b (g + γ) := by
  apply Subtype.ext
  rw [gradedLineDegreeProjection_coe, gradedLineBasis_coe, M.degreeProjection_basis, vectorProjection_apply]
  rw [← M.gradedLineBasis_coe L g, M.gradedLineExtend_on_line]
  change M.basis.coord (g + γ).val (D (b g) : A) • M.basis (g + γ).val =
    (b).coord (g + γ) (D (b g)) • (b (g + γ) : A)
  rw [M.gradedLineBasis_coe, M.gradedLineBasis_coord]

/-- A homogeneous degree on the line is the shift of the restricted basis labels. -/
def HasLineDegree (D : Module.End ℂ Q) (γ : L) : Prop :=
  ∀ g : L, ∃ c : ℂ, D (b g) = c • b (g + γ)

theorem gradedLineDegreeProjection_hasDegree (γ : L) (D : Module.End ℂ Q) :
    M.HasLineDegree L (M.gradedLineDegreeProjection L γ D) γ :=
  fun g => ⟨(b).coord (g + γ) (D (b g)), M.gradedLineDegreeProjection_on_basis L γ g D⟩

private theorem lineDerivation_on_basis (D : Module.End ℂ Q) (hD : ∀ g h : L,
    D (μ (b g) (b h)) = μ (D (b g)) (b h) + μ (b g) (D (b h))) :
    D ∈ M.gradedLineDerivations L := by
  apply (M.mem_gradedLineDerivations L).mpr
  intro x y
  have hspan (z : Q) : z ∈ Submodule.span ℂ (Set.range b) := by rw [Basis.span_eq]; trivial
  refine Submodule.span_induction₂ (p := fun x y _ _ =>
    D (μ x y) = μ (D x) y + μ x (D y)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hspan x) (hspan y)
  · rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
    exact hD g h
  · simp
  · simp
  · intro a c y _ _ _ ha hc
    simp only [map_add, LinearMap.add_apply, ha, hc]
    abel
  · intro x a c _ _ _ ha hc
    simp only [map_add, ha, hc]
    abel
  · intro r x y _ _ h
    simp only [map_smul, LinearMap.smul_apply, h, smul_add]
  · intro r x y _ _ h
    simp only [map_smul, h, smul_add]

private theorem gradedLineExtend_derivation_on_basis {D : Module.End ℂ Q}
    (hD : D ∈ M.gradedLineDerivations L) (g h : L) :
    M.gradedLineExtend L D (M.product (M.basis g.val) (M.basis h.val)) =
      M.product (M.gradedLineExtend L D (M.basis g.val)) (M.basis h.val) +
        M.product (M.basis g.val) (M.gradedLineExtend L D (M.basis h.val)) := by
  have eq := congrArg Subtype.val ((M.mem_gradedLineDerivations L).mp hD (b g) (b h))
  rw [← M.gradedLineBasis_coe L g, ← M.gradedLineBasis_coe L h,
    ← M.gradedLineProduct_coe, M.gradedLineExtend_on_line, M.gradedLineExtend_on_line,
    M.gradedLineExtend_on_line]
  exact eq

theorem gradedLineDegreeProjection_derivation (γ : L) {D : Module.End ℂ Q}
    (hD : D ∈ M.gradedLineDerivations L) :
    M.gradedLineDegreeProjection L γ D ∈ M.gradedLineDerivations L := by
  apply M.lineDerivation_on_basis L
  intro g h
  apply Subtype.ext
  simp only [Submodule.coe_add, M.gradedLineDegreeProjection_coe,
    M.gradedLineProduct_coe, M.gradedLineBasis_coe]
  exact M.degreeProjection_derivation_on_basis γ.val g.val h.val
    (M.gradedLineExtend_derivation_on_basis L hD g h)

theorem gradedLineDegreeProjection_sum (D : Module.End ℂ Q) :
    (∑ γ : L, M.gradedLineDegreeProjection L γ D) = D := by
  classical
  apply (b).ext
  intro g
  rw [LinearMap.sum_apply]
  simp only [M.gradedLineDegreeProjection_on_basis]
  have hsum := Equiv.sum_comp (Equiv.addLeft g) (fun h : L => (b).coord h (D (b g)) • b h)
  change (∑ γ : L, (b).coord (g + γ) (D (b g)) • b (g + γ)) =
    (∑ h : L, (b).coord h (D (b g)) • b h) at hsum
  rw [hsum]
  exact (b).sum_repr (D (b g))

theorem gradedLineDegreeProjection_of_degree {D : Module.End ℂ Q} {γ δ : L}
    (hD : M.HasLineDegree L D δ) :
    M.gradedLineDegreeProjection L γ D = if γ = δ then D else 0 := by
  classical
  apply (b).ext
  intro g
  rw [M.gradedLineDegreeProjection_on_basis]
  obtain ⟨c, hc⟩ := hD g
  by_cases he : γ = δ
  · subst δ
    rw [ite_eq_left rfl, hc, map_smul]
    simp
  · rw [ite_eq_right he, hc, map_smul]
    have hn : g + γ ≠ g + δ := fun e => he (add_left_cancel e)
    simp [Basis.coord_apply, Basis.repr_self, hn]

end

end ThirteenPlanes.Cartan.NormalizedTernaryBasis
