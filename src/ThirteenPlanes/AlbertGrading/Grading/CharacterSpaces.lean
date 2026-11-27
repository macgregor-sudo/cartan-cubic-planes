module

public import ThirteenPlanes.AlbertGrading.Grading.Statements
public import ThirteenPlanes.AlbertGrading.Grading.TraceInvariance
public import ThirteenPlanes.AlbertGrading.Grading.Quartic

@[expose] public section

/-! # ternary grading theorem (i): the character spaces of an arbitrary ternary grading group -/

namespace ThirteenPlanes.AlbertGrading.Grading

open JC

noncomputable section

variable {ρ : TernaryAction}

theorem chargeDot_add_right (s g h : Charge) :
    chargeDot s (g + h) = chargeDot s g + chargeDot s h := by
  simp [chargeDot, mul_add, Finset.sum_add_distrib]

theorem chargeDot_neg_right (s g : Charge) : chargeDot s (-g) = -chargeDot s g := by
  simp [chargeDot, Finset.sum_neg_distrib]

theorem chargeDot_zero_right (s : Charge) : chargeDot s 0 = 0 := by simp [chargeDot]

theorem chargeDot_single_left (j : Fin 3) (q : Charge) : chargeDot (Pi.single j 1) q = q j := by
  unfold chargeDot
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · simp

theorem gradeCharacter_add (s g h : Charge) :
    gradeCharacter s (g + h) = gradeCharacter s g * gradeCharacter s h := by
  simp [gradeCharacter, chargeDot_add_right, chargePhase_add]

theorem gradeCharacter_neg (s g : Charge) : gradeCharacter s (-g) = star (gradeCharacter s g) := by
  simp [gradeCharacter, chargeDot_neg_right, chargePhase_neg]

theorem gradeCharacter_zero (s : Charge) : gradeCharacter s 0 = 1 := by
  simp [gradeCharacter, chargeDot_zero_right]

/-- A nonzero grade is detected by some group element. -/
theorem exists_gradeCharacter_ne_one {g : Charge} (hg : g ≠ 0) : ∃ s, gradeCharacter s g ≠ 1 := by
  obtain ⟨j, hj⟩ : ∃ j, g j ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (funext h)
  refine ⟨Pi.single j 1, fun h => hj ?_⟩
  apply FiniteGroup.chargePhase_injective
  rw [chargePhase_zero, ← h, gradeCharacter, chargeDot_single_left]

section Act

variable (hρ : IsTernaryGrading ρ)
include hρ

theorem act_mul (s : Charge) (z w : JC) : act ρ s (mul z w) = mul (act ρ s z) (act ρ s w) :=
  mapC_mul _ (hρ.automorphism _) z w

theorem act_ip (s : Charge) (z w : JC) : ip (act ρ s z) (act ρ s w) = ip z w :=
  mapC_ip _ (inner_aut _ (hρ.automorphism _)) z w

theorem act_one (s : Charge) : act ρ s one = one := by
  unfold act one
  rw [mapC_of]
  congr 1
  exact one_aut _ (hρ.automorphism _)

end Act

theorem act_conj (s : Charge) (z : JC) : act ρ s (conj z) = conj (act ρ s z) := mapC_conj _ z

/-! ## The four assertions of the ternary grading theorem (i) -/

theorem one_mem_charSpace_zero (hρ : IsTernaryGrading ρ) : one ∈ charSpace ρ 0 := by
  intro s
  rw [act_one hρ, gradeCharacter_zero, one_smul]

theorem conj_mem_charSpace {g : Charge} {z : JC} (hz : z ∈ charSpace ρ g) :
    conj z ∈ charSpace ρ (-g) := by
  intro s
  rw [act_conj, hz s, conj_smul, gradeCharacter_neg]

theorem mul_mem_charSpace (hρ : IsTernaryGrading ρ) {g h : Charge} {z w : JC}
    (hz : z ∈ charSpace ρ g) (hw : w ∈ charSpace ρ h) : mul z w ∈ charSpace ρ (g + h) := by
  intro s
  rw [act_mul hρ, hz s, hw s, mul_smul_left, mul_smul_right, smul_smul, gradeCharacter_add,
    mul_comm (gradeCharacter s g)]

theorem ip_eq_zero_of_charSpace (hρ : IsTernaryGrading ρ) {g h : Charge} {z w : JC}
    (hz : z ∈ charSpace ρ g) (hw : w ∈ charSpace ρ h) (hgh : g + h ≠ 0) : ip z w = 0 := by
  obtain ⟨s, hs⟩ := exists_gradeCharacter_ne_one hgh
  have hip := act_ip hρ s z w
  rw [hz s, hw s, ip_smul_left, ip_smul_right, ← mul_assoc, ← gradeCharacter_add] at hip
  have h2 : (gradeCharacter s (g + h) - 1) * ip z w = 0 := by rw [sub_mul, hip, _root_.one_mul, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hs
  · exact h3

theorem mem_charSpace_conj_iff {g : Charge} {z : JC} :
    conj z ∈ charSpace ρ g ↔ z ∈ charSpace ρ (-g) := by
  constructor
  · intro h
    have := conj_mem_charSpace h
    rwa [conj_conj] at this
  · intro h
    have := conj_mem_charSpace h
    rwa [neg_neg] at this

/-! ## One-dimensional spaces -/

/-- In a one-dimensional character space every element is a multiple of a nonzero element. -/
theorem exists_smul_of_mem (hρ : IsTernaryGrading ρ) {g : Charge} {v z : JC}
    (hv : v ∈ charSpace ρ g) (hv0 : v ≠ 0) (hz : z ∈ charSpace ρ g) : ∃ c : ℂ, z = c • v := by
  have h1 := hρ.lineDim g
  have hv' : (⟨v, hv⟩ : charSpace ρ g) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' _ hv').mp h1 ⟨z, hz⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem exists_ne_zero_mem (hρ : IsTernaryGrading ρ) (g : Charge) :
    ∃ v ∈ charSpace ρ g, v ≠ 0 := by
  have h1 := hρ.lineDim g
  have : Nontrivial (charSpace ρ g) := Module.nontrivial_of_finrank_eq_succ h1
  obtain ⟨v, hv⟩ := exists_ne (0 : charSpace ρ g)
  exact ⟨v.val, v.property, fun h => hv (Subtype.ext h)⟩

theorem charSpace_zero_eq (hρ : IsTernaryGrading ρ) : charSpace ρ 0 = Submodule.span ℂ {one} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨c, rfl⟩ := exists_smul_of_mem hρ (one_mem_charSpace_zero hρ) one_ne_zero hz
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact one_mem_charSpace_zero hρ

/-- Elements of nonzero grade are traceless. -/
theorem tr_eq_zero_of_mem (hρ : IsTernaryGrading ρ) {g : Charge} (hg : g ≠ 0) {z : JC}
    (hz : z ∈ charSpace ρ g) : tr z = 0 := by
  rw [← ip_one_right]
  exact ip_eq_zero_of_charSpace hρ hz (one_mem_charSpace_zero hρ) (by simpa using hg)

theorem charSpace_disjoint {g h : Charge} (hgh : g ≠ h) {z : JC}
    (hz : z ∈ charSpace ρ g) (hz' : z ∈ charSpace ρ h) : z = 0 := by
  obtain ⟨s, hs⟩ := exists_gradeCharacter_ne_one (sub_ne_zero.mpr hgh)
  have e1 := hz s
  have e2 := hz' s
  rw [e1] at e2
  have hne : gradeCharacter s g ≠ gradeCharacter s h := by
    intro he
    apply hs
    have hh : gradeCharacter s (g - h) * gradeCharacter s h = gradeCharacter s h := by
      rw [← gradeCharacter_add, sub_add_cancel, he]
    have h0 : gradeCharacter s h ≠ 0 := by
      unfold gradeCharacter chargePhase; exact pow_ne_zero _ chargeRoot_ne_zero
    exact (mul_eq_right₀ h0).mp hh
  have : (gradeCharacter s g - gradeCharacter s h) • z = 0 := by rw [sub_smul, e2, sub_self]
  exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

/-- Ternary grading theorem (i). -/
theorem graded_part_one (hρ : IsTernaryGrading ρ) :
    (charSpace ρ 0 = Submodule.span ℂ {one}) ∧
    (∀ g z, z ∈ charSpace ρ g → conj z ∈ charSpace ρ (-g)) ∧
    (∀ g h z w, z ∈ charSpace ρ g → w ∈ charSpace ρ h → mul z w ∈ charSpace ρ (g + h)) ∧
    (∀ g h z w, z ∈ charSpace ρ g → w ∈ charSpace ρ h → g + h ≠ 0 → ip z w = 0) :=
  ⟨charSpace_zero_eq hρ, fun _ _ hz => conj_mem_charSpace hz,
    fun _ _ _ _ hz hw => mul_mem_charSpace hρ hz hw,
    fun _ _ _ _ hz hw hgh => ip_eq_zero_of_charSpace hρ hz hw hgh⟩

end

end ThirteenPlanes.AlbertGrading.Grading
