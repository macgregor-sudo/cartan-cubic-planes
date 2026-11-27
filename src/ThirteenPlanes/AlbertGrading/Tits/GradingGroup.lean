module

public import ThirteenPlanes.AlbertGrading.Tits.GradingAction

@[expose] public section

set_option backward.privateInPublic true

/-!
# first-Tits grading and Weyl basis (iii), second half: the generated group and its characters

The three printed generators generate the image of the injective homomorphism
`charHom : 𝔽₃³ → Aut(J_T)`. Every character of `𝔽₃³` is `s ↦ ω^{q·s}`, and its eigenspace on
`J_T ⊗ ℂ` is exactly the line `ℂ u_q`.
-/

open scoped Matrix BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

/-- The character action as a homomorphism into the linear automorphism group of `J_T`. -/
def charHom : Multiplicative Charge →* (CompactTits ≃ₗ[ℝ] CompactTits) where
  toFun s := charAut s.toAdd
  map_one' := LinearEquiv.ext fun x => CompactTits.ext (by
    change CompactTits.coordinates (charAut (Multiplicative.toAdd 1) x) = CompactTits.coordinates x
    rw [toAdd_one, charAut_coordinates, charLin_zero])
  map_mul' s t := LinearEquiv.ext fun x => CompactTits.ext (by
    change CompactTits.coordinates (charAut (Multiplicative.toAdd (s * t)) x) =
      CompactTits.coordinates (charAut s.toAdd (charAut t.toAdd x))
    rw [toAdd_mul, charAut_coordinates, charAut_coordinates, charAut_coordinates, charLin_add])

@[simp] theorem charHom_apply (s : Multiplicative Charge) : charHom s = charAut s.toAdd := rfl

theorem titsBasis_ne_zero (q : Charge) : titsBasis q ≠ 0 := by
  intro h
  have := titsBasis_traceForm q (-q)
  rw [h] at this
  simp [titsTraceForm, trace3] at this

theorem charHom_injective : Function.Injective charHom := by
  intro s t hst
  apply Multiplicative.toAdd.injective
  funext i
  have h1 : charLin s.toAdd = charLin t.toAdd := by
    refine LinearMap.ext fun z => ?_
    rw [← complexify_charAut, ← complexify_charAut]
    change complexify (charHom s).toLinearMap z = complexify (charHom t).toLinearMap z
    rw [hst]
  have h2 := LinearMap.congr_fun h1 (titsBasis (Pi.single i 1))
  rw [charLin_basis, charLin_basis, chargeDot_single, chargeDot_single] at h2
  exact FiniteGroup.chargePhase_injective
    (smul_left_injective ℂ (titsBasis_ne_zero _) h2)

private theorem charge_decomp (s : Charge) :
    s = (s 0).val • Pi.single 0 1 + (s 1).val • Pi.single 1 1 + (s 2).val • Pi.single 2 1 := by
  funext i
  fin_cases i <;> simp only [Pi.add_apply, Pi.smul_apply] <;>
    simp [Pi.single_apply, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id']

private def e0 : Multiplicative Charge := Multiplicative.ofAdd (Pi.single 0 1)
private def e1 : Multiplicative Charge := Multiplicative.ofAdd (Pi.single 1 1)
private def e2 : Multiplicative Charge := Multiplicative.ofAdd (Pi.single 2 1)

private theorem mult_decomp (s : Multiplicative Charge) :
    s = e0 ^ (s.toAdd 0).val * e1 ^ (s.toAdd 1).val * e2 ^ (s.toAdd 2).val := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_pow, e0, e1, e2, toAdd_ofAdd]
  exact charge_decomp _

theorem closure_eq_range :
    Subgroup.closure ({charHom e0, charHom e1, charHom e2} : Set (CompactTits ≃ₗ[ℝ] CompactTits)) =
      charHom.range := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
  · rintro _ ⟨s, rfl⟩
    rw [mult_decomp s, map_mul, map_mul, map_pow, map_pow, map_pow]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
      refine Subgroup.pow_mem _ (Subgroup.subset_closure ?_) _ <;> simp

/-! ## Characters of `𝔽₃³` -/

theorem cube_root_eq (z : ℂ) (h : z ^ 3 = 1) : ∃ a : ZMod 3, z = chargePhase a := by
  have hq := chargeRoot_quadratic
  have hc := chargeRoot_cube
  have hprod : (z - 1) * (z - chargeRoot) * (z - chargeRoot ^ 2) = 0 := by
    linear_combination h - z ^ 2 * hq + z * (hq + hc) - hc
  rcases mul_eq_zero.mp hprod with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · exact ⟨0, by rw [chargePhase_zero]; linear_combination h1⟩
    · exact ⟨1, by rw [show chargePhase 1 = chargeRoot ^ 1 from rfl, pow_one]; linear_combination h2⟩
  · exact ⟨2, by
      rw [show chargePhase 2 = chargeRoot ^ 2 from rfl]; linear_combination h3⟩

private theorem chargePhase_pow' (j : ZMod 3) (n : ℕ) :
    chargePhase j ^ n = chargePhase (n * j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← chargePhase_add]; congr 1; push_cast; ring

theorem chargePhase_ne_zero (a : ZMod 3) : chargePhase a ≠ 0 :=
  pow_ne_zero _ chargeRoot_ne_zero

/-- The character `s ↦ ω^{q·s}`. -/
def phaseChar (q : Charge) : Multiplicative Charge →* ℂˣ where
  toFun s := Units.mk0 (chargePhase (chargeDot q s.toAdd)) (chargePhase_ne_zero _)
  map_one' := Units.ext (by simp [chargeDot])
  map_mul' s t := Units.ext (by simp [chargeDot_add_right', chargePhase_add])

@[simp] theorem phaseChar_apply (q : Charge) (s : Multiplicative Charge) :
    ((phaseChar q s : ℂˣ) : ℂ) = chargePhase (chargeDot q s.toAdd) := rfl

theorem char_classify (ψ : Multiplicative Charge →* ℂˣ) :
    ∃ q : Charge, ∀ s, ((ψ s : ℂˣ) : ℂ) = chargePhase (chargeDot q s.toAdd) := by
  have hcube (i : Fin 3) :
      ((ψ (Multiplicative.ofAdd (Pi.single i 1 : Charge)) : ℂˣ) : ℂ) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    have : Multiplicative.ofAdd (Pi.single i 1 : Charge) ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext j
      by_cases hj : j = i
      · subst hj; simp; decide
      · simp [Pi.single_apply, hj]
    rw [this, map_one, Units.val_one]
  choose a ha using fun i => cube_root_eq _ (hcube i)
  refine ⟨a, fun s => ?_⟩
  conv_lhs => rw [mult_decomp s]
  simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, e0, e1, e2, ha,
    chargePhase_pow', ← chargePhase_add]
  congr 1
  simp only [chargeDot, Fin.sum_univ_three, ZMod.natCast_zmod_val]
  ring

/-! ## Eigenspaces -/

private abbrev G := gradedTitsComplexEquiv

theorem eigen_iff (q : Charge) (z : FirstTits ℂ) :
    (∀ s : Charge, charLin s z = chargePhase (chargeDot q s) • z) ↔
      z ∈ Submodule.span ℂ {titsBasis q} := by
  constructor
  · intro h
    obtain ⟨w, rfl⟩ := G.surjective z
    have hw : ∀ x, x ≠ q → w x = 0 := by
      intro x hx
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ q j := by
        by_contra hc; push Not at hc; exact hx (funext hc)
      have h1 := h (Pi.single j 1)
      rw [charLin_graded, ← map_smul] at h1
      have h2 := congrFun (G.injective h1) x
      simp only [charAct_apply, Pi.smul_apply, smul_eq_mul, chargeDot_comm' (Pi.single j 1),
        chargeDot_single] at h2
      have hne : chargePhase (x j) ≠ chargePhase (q j) :=
        fun e => hj (FiniteGroup.chargePhase_injective e)
      have : (chargePhase (x j) - chargePhase (q j)) * w x = 0 := by linear_combination h2
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
    have hw' : w = w q • chargeBasisVector q := by
      funext x
      by_cases hx : x = q
      · subst hx; simp [chargeBasisVector]
      · simp [chargeBasisVector, hx, hw x hx]
    rw [hw', map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [titsBasis_eq_homogeneous, ← gradedTitsCoordinates_single]
    rfl
  · intro h s
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
    rw [map_smul, charLin_basis, chargeDot_comm', smul_comm]

theorem span_titsBasis_injective {g q : Charge}
    (h : (Submodule.span ℂ {titsBasis g} : Set (FirstTits ℂ)) = Submodule.span ℂ {titsBasis q}) :
    g = q := by
  have hg : titsBasis g ∈ (Submodule.span ℂ {titsBasis q} : Set (FirstTits ℂ)) := by
    rw [← h]; exact Submodule.subset_span rfl
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hg
  rw [titsBasis_eq_homogeneous, titsBasis_eq_homogeneous, ← gradedTitsCoordinates_single,
    ← gradedTitsCoordinates_single, ← map_smul] at hc
  have := congrFun (G.injective hc) g
  by_contra hne
  simp [chargeBasisVector, hne] at this

/-! ## The image subgroup is a ternary grading group with character lines `ℂ u_q` -/

section Range

private abbrev E := charHom.range
private abbrev eqv : Multiplicative Charge ≃* E := MonoidHom.ofInjective charHom_injective

theorem complexify_range (s : Multiplicative Charge) (z : FirstTits ℂ) :
    complexify ((eqv s : E) : CompactTits ≃ₗ[ℝ] CompactTits).toLinearMap z = charLin s.toAdd z :=
  complexify_charAut s.toAdd z

theorem characterSpace_range (χ : E →* ℂˣ) (q : Charge)
    (hq : ∀ s, ((χ (eqv s) : ℂˣ) : ℂ) = chargePhase (chargeDot q s.toAdd)) :
    characterSpace E χ = (Submodule.span ℂ {titsBasis q} : Set (FirstTits ℂ)) := by
  ext z
  change (∀ e : E, _) ↔ _
  rw [SetLike.mem_coe, ← eigen_iff]
  constructor
  · intro h s
    have := h (eqv (Multiplicative.ofAdd s))
    rwa [complexify_range, hq] at this
  · intro h e
    obtain ⟨s, rfl⟩ := eqv.surjective e
    rw [complexify_range, hq]
    exact h s.toAdd

theorem range_grading :
    IsTernaryGradingGroup E ∧
    (∀ χ : E →* ℂˣ, ∃! g : Charge,
      characterSpace E χ = (Submodule.span ℂ {titsBasis g} : Set (FirstTits ℂ))) ∧
    (∀ g : Charge, ∃ χ : E →* ℂˣ,
      characterSpace E χ = (Submodule.span ℂ {titsBasis g} : Set (FirstTits ℂ))) := by
  have hex (χ : E →* ℂˣ) : ∃ q : Charge,
      characterSpace E χ = (Submodule.span ℂ {titsBasis q} : Set (FirstTits ℂ)) := by
    obtain ⟨q, hq⟩ := char_classify (χ.comp eqv.toMonoidHom)
    exact ⟨q, characterSpace_range χ q hq⟩
  refine ⟨⟨?_, ⟨eqv.symm⟩, fun χ => ?_⟩, fun χ => ?_, fun g => ?_⟩
  · rintro f ⟨s, rfl⟩
    exact charAut_isAutomorphism _
  · obtain ⟨q, hq⟩ := hex χ
    exact ⟨_, titsBasis_ne_zero q, hq⟩
  · obtain ⟨q, hq⟩ := hex χ
    exact ⟨q, hq, fun g hg => span_titsBasis_injective (hg.symm.trans hq)⟩
  · refine ⟨(phaseChar g).comp eqv.symm.toMonoidHom, characterSpace_range _ g fun s => ?_⟩
    simp

end Range

/-- First-Tits grading and Weyl basis (iii) for the printed generators. -/
theorem partThree (fZ fX fφ : CompactTits ≃ₗ[ℝ] CompactTits)
    (hZ : ∀ x, CompactTits.coordinates (fZ x) = adMap clockMatrix (CompactTits.coordinates x))
    (hX : ∀ x, CompactTits.coordinates (fX x) = adMap shiftMatrix⁻¹ (CompactTits.coordinates x))
    (hφ : ∀ x, CompactTits.coordinates (fφ x) = phiMap (CompactTits.coordinates x)) :
    IsTernaryGradingGroup (Subgroup.closure {fZ, fX, fφ}) ∧
    (∀ χ : Subgroup.closure ({fZ, fX, fφ} : Set (CompactTits ≃ₗ[ℝ] CompactTits)) →* ℂˣ,
      ∃! g : Charge, characterSpace _ χ = (Submodule.span ℂ {titsBasis g} : Set (FirstTits ℂ))) ∧
    (∀ g : Charge, ∃ χ : Subgroup.closure ({fZ, fX, fφ} : Set (CompactTits ≃ₗ[ℝ] CompactTits)) →* ℂˣ,
      characterSpace _ χ = (Submodule.span ℂ {titsBasis g} : Set (FirstTits ℂ))) := by
  have eZ : fZ = charHom e0 := LinearEquiv.ext fun x => CompactTits.ext (by
    rw [hZ, charHom_apply, charAut_coordinates]; exact LinearMap.congr_fun adMap_clock_eq _)
  have eX : fX = charHom e1 := LinearEquiv.ext fun x => CompactTits.ext (by
    rw [hX, charHom_apply, charAut_coordinates]; exact LinearMap.congr_fun adMap_shiftInv_eq _)
  have eφ : fφ = charHom e2 := LinearEquiv.ext fun x => CompactTits.ext (by
    rw [hφ, charHom_apply, charAut_coordinates]; exact LinearMap.congr_fun phiMap_eq _)
  subst eZ eX eφ
  rw [closure_eq_range]
  exact range_grading

end

end ThirteenPlanes.AlbertGrading
