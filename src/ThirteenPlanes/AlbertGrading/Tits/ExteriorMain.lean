module

public import ThirteenPlanes.AlbertGrading.Tits.Exterior

@[expose] public section

set_option backward.privateInPublic true

/-! Construction of the exterior frame in the compact first Tits model. -/

open scoped Matrix RealInnerProductSpace BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

private theorem cp1 : chargePhase 1 = chargeRoot := pow_one _
private theorem cp2 : chargePhase 2 = chargeRoot ^ 2 := rfl
private theorem cpn1 : chargePhase (-1) = chargeRoot ^ 2 := rfl
private theorem cpn2 : chargePhase (-2) = chargeRoot := pow_one _

theorem exteriorPoint_contrast :
    titsContrast exteriorPoint = ((0 : Mat3 ℂ), (0 : Mat3 ℂ), (1 : Mat3 ℂ)) := by
  have hq := chargeRoot_quadratic
  have hc := chargeRoot_cube
  simp only [titsContrast, sum_zmod3, exteriorPoint_coordinates, neg_zero, chargePhase_zero,
    cp1, cp2, cpn1, cpn2, Prod.smul_mk, Prod.mk_add_mk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext i j <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Matrix.zero_apply] <;> split_ifs <;> simp only [mul_one, mul_zero, add_zero]
  · linear_combination (1 / 3 : ℂ) * hq
  · linear_combination (1 / 3 : ℂ) * hq + (1 / 3 : ℂ) * chargeRoot * hc
  · linear_combination (2 / 3 : ℂ) * hc

theorem exteriorPoint_trace (a : ZMod 3) : CompactTits.trace (exteriorPoint a) = 1 := by
  rw [CompactTits.trace_apply, exteriorPoint_coordinates]
  simp [trace3, Matrix.one_apply]
  norm_num

private theorem exterior_of_order (p : ZMod 3 → CompactTits) (hp : IsTitsFrame p)
    (horth : (titsFramePlane p).IsOrtho visibleTraceless) (π : Equiv.Perm (ZMod 3)) (V : Mat3 ℂ)
    (hV : V ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (hπ : ∀ a, (3 : ℂ) • (CompactTits.coordinates (p (π a))).2.1 = chargePhase a • V) :
    ∃ π : Equiv.Perm (ZMod 3), ∃ V ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ,
      (∀ a, CompactTits.coordinates (p (π a)) =
        (1 / 3 : ℂ) • ((1 : Mat3 ℂ), chargePhase a • V, chargePhase (-a) • Vᴴ)) ∧
      Vᴴ ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ ∧
      (∃ f : CompactTits ≃ₗ[ℝ] CompactTits, IsTitsAutomorphism f ∧
        (∀ x, CompactTits.coordinates (f x) = psiMap Vᴴ (CompactTits.coordinates x)) ∧
        (∀ a, f (p (π a)) = exteriorPoint a) ∧
        (∀ x, (CompactTits.coordinates x).2.1 = 0 → f x = x)) ∧
      IsTitsFrame exteriorPoint ∧
      titsContrast exteriorPoint = ((0 : Mat3 ℂ), (0 : Mat3 ℂ), (1 : Mat3 ℂ)) := by
  have hVV : V * Vᴴ = 1 :=
    unitary_mul_conjTranspose (Matrix.mem_specialUnitaryGroup_iff.mp hV).1
  have hcoords (a : ZMod 3) : CompactTits.coordinates (p (π a)) =
      (1 / 3 : ℂ) • ((1 : Mat3 ℂ), chargePhase a • V, chargePhase (-a) • Vᴴ) := by
    have hB : (CompactTits.coordinates (p (π a))).2.1 = (1 / 3 : ℂ) • (chargePhase a • V) := by
      rw [← hπ a, smul_smul]; norm_num
    have h3 := CompactTits.third_eq_adjoint (p (π a))
    rw [Prod.smul_mk, Prod.smul_mk]
    refine Prod.ext (visible_third p hp horth (π a)) (Prod.ext hB ?_)
    change (CompactTits.coordinates (p (π a))).2.2 = _
    rw [h3, hB, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, chargePhase_neg]
    congr 1
    simp
  have hVH := specialUnitary_conjTranspose_mem hV
  obtain ⟨-, -, -, -, f, hfaut, hfc⟩ := psiPart hVH
  have hfix : ∀ x, (CompactTits.coordinates x).2.1 = 0 → f x = x := by
    intro x hx
    apply CompactTits.ext
    rw [hfc]
    have h3 := CompactTits.third_eq_adjoint x
    rw [hx, Matrix.conjTranspose_zero] at h3
    simp only [psiMap, hx, h3, Matrix.zero_mul, Matrix.mul_zero]
    exact Prod.ext rfl (Prod.ext hx.symm h3.symm)
  have hmap (a : ZMod 3) : f (p (π a)) = exteriorPoint a := by
    apply CompactTits.ext
    rw [hfc, hcoords, exteriorPoint_coordinates]
    simp only [psiMap, Prod.smul_mk, Matrix.smul_mul, Matrix.mul_smul, hVV,
      Matrix.conjTranspose_conjTranspose, smul_smul]
  have hone : f CompactTits.one = CompactTits.one :=
    hfix _ (by simp [CompactTits.one])
  refine ⟨π, V, hV, hcoords, hVH, ⟨f, hfaut, hfc, hmap, hfix⟩, ⟨?_, exteriorPoint_trace, ?_⟩,
    exteriorPoint_contrast⟩
  · intro a b
    rw [← hmap a, ← hmap b, ← hfaut, hp.1]
    by_cases hab : a = b
    · subst hab; simp
    · have : π a ≠ π b := fun e => hab (π.injective e)
      simp [hab, this]
  · calc ∑ a, exteriorPoint a = ∑ a, f (p (π a)) := by simp only [hmap]
      _ = f (∑ a, p a) := by rw [map_sum]; exact Equiv.sum_comp π (fun a => f (p a))
      _ = CompactTits.one := by rw [hp.2.2, hone]

/-- Exterior frame normal form. -/
theorem exteriorFrame : Statements.ExteriorFrame := by
  intro p hp horth
  let V : ZMod 3 → Mat3 ℂ := fun a => (3 : ℂ) • (CompactTits.coordinates (p a)).2.1
  have hV (a : ZMod 3) : V a ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ :=
    hidden_specialUnitary p hp horth a
  have hsum : V 0 + V 1 + V 2 = 0 := by
    have := congrArg (fun z => (CompactTits.coordinates z).2.1) hp.2.2
    simp only [map_sum, sum_zmod3, map_add, Prod.snd_add, Prod.fst_add, CompactTits.coordinates_one,
      firstTitsOne] at this
    simp only [V, ← smul_add, this, smul_zero]
  rcases CentralTriples.specialUnitary_triple_sum_zero (V 0) (V 1) (V 2) chargeRoot
      chargeRoot_quadratic (hV 0) (hV 1) (hV 2) hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine exterior_of_order p hp horth (Equiv.refl _) (V 0) (hV 0) fun a => ?_
    rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) a with rfl | rfl | rfl
    · simp [V]
    · simpa [V, cp1] using h1
    · simpa [V, cp2] using h2
  · refine exterior_of_order p hp horth (Equiv.swap 1 2) (V 0) (hV 0) fun a => ?_
    rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) a with rfl | rfl | rfl
    · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; simp [V]
    · rw [Equiv.swap_apply_left]; simpa [V, cp1] using h2
    · rw [Equiv.swap_apply_right]; simpa [V, cp2] using h1

end

end ThirteenPlanes.AlbertGrading
