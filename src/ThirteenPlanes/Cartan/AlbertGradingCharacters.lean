module

public import ThirteenPlanes.Cartan.AlbertGradingBasis
public import ThirteenPlanes.Cartan.DerivationGradingFixed
public import ThirteenPlanes.Cartan.AlbertOperators

@[expose] public section

set_option backward.privateInPublic true

/-! The normalized basis grades are the actual conjugation characters and native planes. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading AlbertGrading.Grading.JC Module
open scoped RealInnerProductSpace

noncomputable section

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ)

/-- Every original eigenline is spanned by the chosen normalized vector. -/
theorem albertGradingBasis_charSpace_eq (g : Charge) :
    charSpace ρ g = Submodule.span ℂ {(albertGradingBasis hρ).basis g} := by
  have hv := albertGradingBasis_mem_charSpace hρ g
  apply le_antisymm
  · intro z hz
    obtain ⟨c, rfl⟩ := exists_smul_of_mem hρ hv ((albertGradingBasis hρ).basis.ne_zero g) hz
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hv

private theorem grading_act_add (ρ : TernaryAction) (s t : Charge) (z : JC) :
    act ρ (s + t) z = act ρ s (act ρ t z) := by
  apply JC.ext
  · change (ρ (Multiplicative.ofAdd s * Multiplicative.ofAdd t)) z.re = _
    rw [map_mul]
    rfl
  · change (ρ (Multiplicative.ofAdd s * Multiplicative.ofAdd t)) z.im = _
    rw [map_mul]
    rfl

private theorem grading_act_zero (ρ : TernaryAction) (z : JC) : act ρ 0 z = z := by
  apply JC.ext
  · change (ρ 1) z.re = z.re
    rw [map_one]
    rfl
  · change (ρ 1) z.im = z.im
    rw [map_one]
    rfl

/-- The complexified grading automorphism, with the actual inverse action. -/
def albertGradingActEquiv (ρ : TernaryAction) (s : Charge) : JC ≃ₗ[ℂ] JC :=
  { act ρ s with
    invFun := act ρ (-s)
    left_inv := fun z => by
      change act ρ (-s) (act ρ s z) = z
      rw [← grading_act_add, neg_add_cancel, grading_act_zero]
    right_inv := fun z => by
      change act ρ s (act ρ (-s) z) = z
      rw [← grading_act_add, add_neg_cancel, grading_act_zero] }

@[simp] theorem albertGradingActEquiv_apply (ρ : TernaryAction) (s : Charge) (z : JC) :
    albertGradingActEquiv ρ s z = act ρ s z := rfl

@[simp] theorem albertGradingActEquiv_symm_apply (ρ : TernaryAction) (s : Charge) (z : JC) :
    (albertGradingActEquiv ρ s).symm z = act ρ (-s) z := rfl

/-- The native real compact Jordan isometry underlying one element of the grading action. -/
def albertGradingNativeAction (s : Charge) : albertJordan.Automorphism := by
  let f := ρ (Multiplicative.ofAdd s)
  have hf := hρ.automorphism (Multiplicative.ofAdd s)
  refine ⟨⟨f, fun x => ?_⟩, one_aut f hf, hf⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    Glennie.hilbert_inner_eq_native, Glennie.hilbert_inner_eq_native]
  exact inner_aut f hf x x

private theorem grading_act_on_basis (s g : Charge) :
    act ρ s ((albertGradingBasis hρ).basis g) =
      gradeCharacter s g • (albertGradingBasis hρ).basis g :=
  albertGradingBasis_mem_charSpace hρ g s

/-- Shifting the actual character spaces by γ is equivalent to having conjugation character γ. -/
theorem albertGrading_hasDegree_iff_character (D : Module.End ℂ JC) (γ : Charge) :
    (albertGradingBasis hρ).HasDegree D γ ↔
      ∀ s, (albertGradingActEquiv ρ s).conj D = gradeCharacter s γ • D := by
  let M := albertGradingBasis hρ
  constructor
  · intro hd s
    let e := albertGradingActEquiv ρ s
    have step : (act ρ s).comp D = (gradeCharacter s γ) • (D.comp (act ρ s)) := by
      apply M.basis.ext
      intro g
      obtain ⟨c, hc⟩ := hd g
      change act ρ s (D (M.basis g)) = gradeCharacter s γ • D (act ρ s (M.basis g))
      rw [hc, map_smul, grading_act_on_basis, grading_act_on_basis, map_smul, hc,
        smul_smul, smul_smul, smul_smul, gradeCharacter_add]
      congr 1
      ring
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun step (e.symm z)
    change e (D (e.symm z)) = gradeCharacter s γ • D (e (e.symm z)) at hz
    rw [e.apply_symm_apply] at hz
    exact hz
  · intro h g
    have hm : D (M.basis g) ∈ charSpace ρ (g + γ) := by
      intro s
      let e := albertGradingActEquiv ρ s
      have hgs := LinearMap.congr_fun (h s) (e (M.basis g))
      change e (D (e.symm (e (M.basis g)))) = gradeCharacter s γ • D (e (M.basis g)) at hgs
      rw [e.symm_apply_apply] at hgs
      change act ρ s (D (M.basis g)) = gradeCharacter s γ • D (act ρ s (M.basis g)) at hgs
      rw [grading_act_on_basis, map_smul, smul_smul,
        _root_.mul_comm (gradeCharacter s γ) (gradeCharacter s g), ← gradeCharacter_add] at hgs
      exact hgs
    exact exists_smul_of_mem hρ (albertGradingBasis_mem_charSpace hρ (g + γ))
      (M.basis.ne_zero (g + γ)) hm

/-- The code's homogeneous derivation space is the actual character eigenspace inside derivations. -/
theorem albertGrading_derivationGrade_iff_character (D : Module.End ℂ JC) (γ : Charge) :
    D ∈ (albertGradingBasis hρ).derivationGrade γ ↔
      (albertGradingBasis hρ).IsDerivation D ∧
        ∀ s, (albertGradingActEquiv ρ s).conj D = gradeCharacter s γ • D := by
  rw [NormalizedTernaryBasis.mem_derivationGrade, albertGrading_hasDegree_iff_character]

private def gradingTrace : JC →ₗ[ℂ] ℂ where
  toFun := tr
  map_add' x y := by apply Complex.ext <;> simp [tr]
  map_smul' c z := by
    apply Complex.ext <;> simp [tr, Complex.mul_re, Complex.mul_im, Glennie.trace_sub, Glennie.trace_smul]

/-- The unital axis is the actual sum of the three indicated character lines. -/
theorem albertGrading_gradeAxis_eq (g : Charge) : (albertGradingBasis hρ).gradeAxis g =
    charSpace ρ 0 ⊔ (charSpace ρ g ⊔ charSpace ρ (-g)) := by
  rw [NormalizedTernaryBasis.gradeAxis, Submodule.span_insert, Submodule.span_insert,
    albertGradingBasis_charSpace_eq hρ 0, albertGradingBasis_charSpace_eq hρ g,
    albertGradingBasis_charSpace_eq hρ (-g)]

/-- Deleting the unit component of the native real axis leaves its original graded plane. -/
theorem albertGrading_of_mem_gradeAxis_iff (g : Charge) (hg : g ≠ 0) (x : NativeTraceless) :
    of (x : Glennie.Albert) ∈ (albertGradingBasis hρ).gradeAxis g ↔ x ∈ gradedPlane ρ g := by
  rw [albertGrading_gradeAxis_eq]
  change of (x : Glennie.Albert) ∈ charSpace ρ 0 ⊔ (charSpace ρ g ⊔ charSpace ρ (-g)) ↔
    of (x : Glennie.Albert) ∈ charSpace ρ g ⊔ charSpace ρ (-g)
  constructor
  · rintro hx
    obtain ⟨u, hu, v, hv, eq⟩ := Submodule.mem_sup.mp hx
    have htv : gradingTrace v = 0 := by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      change tr a + tr b = 0
      rw [tr_eq_zero_of_mem hρ hg ha, tr_eq_zero_of_mem hρ (neg_ne_zero.mpr hg) hb, add_zero]
    rw [charSpace_zero_eq hρ] at hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hc := congrArg gradingTrace eq
    rw [map_add, map_smul, htv, add_zero] at hc
    change c * tr one = tr (of (x : Glennie.Albert)) at hc
    have ht : tr (of (x : Glennie.Albert)) = 0 := by
      apply Complex.ext
      · exact nativeTraceless_trace x
      · change Glennie.trace 0 = 0
        simp
    rw [tr_one, ht] at hc
    have hc0 : c = 0 := (mul_eq_zero.mp hc).resolve_right (by norm_num)
    rw [hc0, zero_smul, zero_add] at eq
    exact eq ▸ hv
  · intro hx
    exact Submodule.mem_sup.mpr ⟨0, (charSpace ρ 0).zero_mem, _, hx, zero_add _⟩

/-- The real traceless fixed axis is exactly the projective grading plane from §5. -/
theorem albertGrading_of_mem_pointAxis_iff (p : SignedPlaneIndex) (x : NativeTraceless) :
    of (x : Glennie.Albert) ∈ (albertGradingBasis hρ).gradeAxis p.val.val ↔ x ∈ pointPlane ρ p :=
  albertGrading_of_mem_gradeAxis_iff hρ p.val.val p.val.property x

end

end ThirteenPlanes.Cartan
