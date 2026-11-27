module

public import ThirteenPlanes.PeirceDecomposition

@[expose] public section

set_option backward.privateInPublic true

/-! The Clifford action of the minus Peirce space on the half Peirce space. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

open Module.End

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {h : SymmetricCubic V} {a : V}
variable (round : IsRound h 1) (ha : IsUnitIdempotent h a)

/-- Multiplication by a minus field, restricted to the half space. -/
def halfAction : minusSpace h a →ₗ[ℝ] Module.End ℝ (halfSpace h a) :=
  LinearMap.mk₂ ℝ
    (fun u y => ⟨h.L (u : V) (y : V), minus_mul_half round ha u.property y.property⟩)
    (by intro u v y; apply Subtype.ext; exact LinearMap.congr_fun (h.L.map_add (u : V) v) y)
    (by intro r u y; apply Subtype.ext; exact LinearMap.congr_fun (h.L.map_smul r (u : V)) y)
    (by intro u x y; apply Subtype.ext; exact (h.L (u : V)).map_add (x : V) y)
    (by intro r u y; apply Subtype.ext; exact (h.L (u : V)).map_smul r (y : V))

@[simp] theorem halfAction_apply_coe (u : minusSpace h a) (y : halfSpace h a) :
    (halfAction round ha u y : V) = h.L (u : V) (y : V) := rfl

private theorem halfAction_square (u : minusSpace h a) :
    (halfAction round ha u) ^ 2 =
      ((3 / 4 : ℝ) * ‖u‖ ^ 2) • (1 : Module.End ℝ (halfSpace h a)) := by
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  change h.L (u : V) (h.L (u : V) (y : V)) = ((3 / 4 : ℝ) * ‖(u : V)‖ ^ 2) • (y : V)
  have ho := (spectralSplit round ha).minus_half_perp.inner_eq u.property y.property
  have hu : h.L (u : V) (u : V) = (-‖(u : V)‖ ^ 2) • a := by
    rw [minus_mul_minus round ha u.property u.property, real_inner_self_eq_norm_sq]
  have hy := mem_eigenspace_iff.mp y.property
  have hp := square_operator round (u : V) (y : V)
  rw [hu, h.L.map_smul, LinearMap.smul_apply, hy, ho, mul_zero, zero_smul, add_zero] at hp
  have hs := congrArg ((1 / 2 : ℝ) • ·) (eq_sub_of_add_eq' hp)
  convert hs using 1 <;> module

/-- Lemma 2b-clifford. -/
theorem clifford_relation (u v : minusSpace h a) :
    halfAction round ha u * halfAction round ha v + halfAction round ha v * halfAction round ha u =
      ((3 / 2 : ℝ) * ⟪u, v⟫) • (1 : Module.End ℝ (halfSpace h a)) := by
  let A := halfAction round ha
  let I : Module.End ℝ (halfSpace h a) := 1
  have hu := halfAction_square round ha u
  have hv := halfAction_square round ha v
  have hs := halfAction_square round ha (u + v)
  change (A (u + v)) ^ 2 = ((3 / 4 : ℝ) * ‖u + v‖ ^ 2) • I at hs
  rw [A.map_add, pow_two, add_mul, mul_add, mul_add,
    ← pow_two (A u), ← pow_two (A v), hu, hv, norm_add_sq_real] at hs
  have he := congrArg (fun T : Module.End ℝ (halfSpace h a) =>
    T - ((3 / 4 : ℝ) * ‖u‖ ^ 2) • I - ((3 / 4 : ℝ) * ‖v‖ ^ 2) • I) hs
  change A u * A v + A v * A u = ((3 / 2 : ℝ) * ⟪u, v⟫) • I
  convert he using 1 <;> module

/-- The action scaled so that a unit minus field acts as an involution. -/
def scaledHalfAction : minusSpace h a →ₗ[ℝ] Module.End ℝ (halfSpace h a) :=
  (2 / Real.sqrt 3 : ℝ) • halfAction round ha

@[simp] theorem scaledHalfAction_apply_coe (u : minusSpace h a) (y : halfSpace h a) :
    (scaledHalfAction round ha u y : V) = (2 / Real.sqrt 3 : ℝ) • h.L (u : V) (y : V) := rfl

theorem scaledHalfAction_isSymmetric (u : minusSpace h a) :
    (scaledHalfAction round ha u).IsSymmetric := by
  intro x y
  change ⟪(2 / Real.sqrt 3 : ℝ) • h.L (u : V) (x : V), (y : V)⟫ =
    ⟪(x : V), (2 / Real.sqrt 3 : ℝ) • h.L (u : V) (y : V)⟫
  rw [real_inner_smul_left, real_inner_smul_right, h.L_isSymmetric]

private theorem scale_mul_scale : (2 / Real.sqrt 3 : ℝ) * (2 / Real.sqrt 3) = 4 / 3 := by
  have h : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [← pow_two, div_pow, h]
  norm_num

theorem scaledHalfAction_clifford (u v : minusSpace h a) :
    scaledHalfAction round ha u * scaledHalfAction round ha v +
      scaledHalfAction round ha v * scaledHalfAction round ha u =
      (2 * ⟪u, v⟫) • (1 : Module.End ℝ (halfSpace h a)) := by
  unfold scaledHalfAction
  simp only [LinearMap.smul_apply, smul_mul_assoc, mul_smul_comm, smul_smul, scale_mul_scale]
  rw [← smul_add, clifford_relation round ha u v]
  module

theorem scaledHalfAction_square (u : minusSpace h a) :
    (scaledHalfAction round ha u) ^ 2 = ‖u‖ ^ 2 • (1 : Module.End ℝ (halfSpace h a)) := by
  have hp := scaledHalfAction_clifford round ha u u
  rw [real_inner_self_eq_norm_sq, ← pow_two] at hp
  have he := congrArg ((1 / 2 : ℝ) • ·) hp
  convert he using 1 <;> module

theorem scaledHalfAction_norm (u : minusSpace h a) (y : halfSpace h a) :
    ‖scaledHalfAction round ha u y‖ = ‖u‖ * ‖y‖ := by
  let B := scaledHalfAction round ha u
  have hB : B (B y) = ‖u‖ ^ 2 • y := by
    have h := congrArg (fun T : Module.End ℝ (halfSpace h a) => T y)
      (scaledHalfAction_square round ha u)
    rw [pow_two] at h
    exact h
  have hi := scaledHalfAction_isSymmetric round ha u (B y) y
  change ⟪B (B y), y⟫ = ⟪B y, B y⟫ at hi
  rw [hB, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
  have hsq : ‖B y‖ ^ 2 = (‖u‖ * ‖y‖) ^ 2 := by rw [mul_pow, hi]
  have he := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
  rwa [abs_of_nonneg (norm_nonneg (B y)),
    abs_of_nonneg (mul_nonneg (norm_nonneg u) (norm_nonneg y))] at he

end

end ThirteenPlanes.Peirce
