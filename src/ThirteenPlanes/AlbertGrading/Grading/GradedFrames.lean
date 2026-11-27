module

public import ThirteenPlanes.AlbertGrading.Grading.Normalization

@[expose] public section

set_option backward.privateInPublic true

/-! # ternary grading theorem (ii)–(iii): the frame of a normalized element and its plane

For normalized `u ∈ A_g`, `g ≠ 0`, the elements `p_a = ⅓(e + ω^{-a} u + ω^a ū)` are real, multiply
as the primitive idempotents of the group algebra of `ℤ/3`, and form a frame with contrast `u`;
its plane is `J ∩ (A_g ⊕ A_{-g})`. Frames of different points are unbiased. -/

namespace ThirteenPlanes.AlbertGrading.Grading

open JC

noncomputable section

variable {ρ : TernaryAction}

/-! ## Phases -/

theorem phase_one : chargePhase 1 = chargeRoot := by
  show chargeRoot ^ (1 : ZMod 3).val = _
  rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]

theorem phase_two : chargePhase 2 = chargeRoot ^ 2 := by
  show chargeRoot ^ (2 : ZMod 3).val = _
  rw [show (2 : ZMod 3).val = 2 from rfl]

theorem phase_sum3 (c : ZMod 3) :
    1 + chargePhase c + chargePhase (-c) = if c = 0 then 3 else 0 := by
  have hq := chargeRoot_quadratic
  have key : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  rcases key c with rfl | rfl | rfl
  · rw [if_pos rfl, neg_zero, chargePhase_zero]; norm_num
  · rw [if_neg (by decide), show (-(1 : ZMod 3)) = 2 from by decide, phase_one, phase_two]
    linear_combination hq
  · rw [if_neg (by decide), show (-(2 : ZMod 3)) = 1 from by decide, phase_one, phase_two]
    linear_combination hq

theorem sum_phase_outcome : (∑ a : Fin 3, chargePhase (outcome a)) = 0 := by
  rw [Fin.sum_univ_three]
  rw [show outcome 0 = 0 from rfl, show outcome 1 = 1 from rfl, show outcome 2 = 2 from rfl,
    chargePhase_zero, phase_one, phase_two]
  linear_combination chargeRoot_quadratic

theorem sum_phase_neg_outcome : (∑ a : Fin 3, chargePhase (-(outcome a))) = 0 := by
  rw [Fin.sum_univ_three]
  rw [show outcome 0 = 0 from rfl, show outcome 1 = 1 from rfl, show outcome 2 = 2 from rfl,
    neg_zero, show (-(1 : ZMod 3)) = 2 from by decide, show (-(2 : ZMod 3)) = 1 from by decide,
    chargePhase_zero, phase_one, phase_two]
  linear_combination chargeRoot_quadratic

theorem star_phase (a : ZMod 3) : star (chargePhase a) = chargePhase (-a) := by
  rw [chargePhase_neg]

theorem outcome_injective : Function.Injective outcome := fun _ _ h => h

/-! ## The frame of a normalized element -/

section Frame

variable (hρ : IsTernaryGrading ρ) {g : Charge} (hg : g ≠ 0) {u : JC}
  (hu : u ∈ charSpace ρ g) (hun : IsNormalized u)

theorem framePoint_conj (a : Fin 3) : conj (framePoint u a) = framePoint u a := by
  unfold framePoint
  rw [conj_smul, conj_add, conj_add, conj_one, conj_smul, conj_smul, conj_conj, star_phase,
    star_phase, neg_neg]
  have h3 : star (1 / 3 : ℂ) = 1 / 3 := by simp
  rw [h3, add_assoc, add_assoc, add_comm (chargePhase (outcome a) • conj u)]

/-- The real frame point. -/
def framePointReal (u : JC) (a : Fin 3) : Glennie.Albert := (framePoint u a).re

theorem of_framePointReal (a : Fin 3) : of (framePointReal u a) = framePoint u a :=
  ((conj_eq_self_iff _).mp (framePoint_conj a)).symm

include hun in
theorem mul_framePoint_general (a b : Fin 3) :
    mul (framePoint u a) (framePoint u b) = (1 / 9 : ℂ) •
      ((1 + chargePhase (-(outcome a)) * chargePhase (outcome b) +
          chargePhase (outcome a) * chargePhase (-(outcome b))) • one +
        (chargePhase (-(outcome a)) + chargePhase (-(outcome b)) +
          chargePhase (outcome a) * chargePhase (outcome b)) • u +
        (chargePhase (outcome a) + chargePhase (outcome b) +
          chargePhase (-(outcome a)) * chargePhase (-(outcome b))) • conj u) := by
  have h1 := hun.1
  have h2 := hun.2
  have h3 : mul (conj u) u = one := by rw [JC.mul_comm]; exact h2
  have h4 := conj_mul_conj_of_normalized hun
  unfold framePoint
  simp only [mul_add_left, mul_add_right, mul_smul_left, mul_smul_right, JC.one_mul, JC.mul_one,
    h1, h2, h3, h4]
  module

private theorem coeff_one (α β : ZMod 3) :
    1 + chargePhase (-α) * chargePhase β + chargePhase α * chargePhase (-β) =
      if β - α = 0 then 3 else 0 := by
  rw [← phase_sum3, ← chargePhase_add, ← chargePhase_add]
  congr 2 <;> ring

private theorem coeff_two (α β : ZMod 3) :
    chargePhase (-α) + chargePhase (-β) + chargePhase α * chargePhase β =
      chargePhase (-α) * (if α - β = 0 then 3 else 0) := by
  rw [← phase_sum3, mul_add, mul_add, _root_.mul_one, ← chargePhase_add, ← chargePhase_add,
    ← chargePhase_add]
  have e1 : -α + (α - β) = -β := by ring
  have e2 : ∀ α β : ZMod 3, -α + -(α - β) = α + β := by decide
  rw [e1, e2]

private theorem coeff_three (α β : ZMod 3) :
    chargePhase α + chargePhase β + chargePhase (-α) * chargePhase (-β) =
      chargePhase α * (if β - α = 0 then 3 else 0) := by
  rw [← phase_sum3, mul_add, mul_add, _root_.mul_one, ← chargePhase_add, ← chargePhase_add,
    ← chargePhase_add]
  have e1 : α + (β - α) = β := by ring
  have e2 : ∀ α β : ZMod 3, α + -(β - α) = -α + -β := by decide
  rw [e1, e2]

include hun in
theorem mul_framePoint (a b : Fin 3) :
    mul (framePoint u a) (framePoint u b) = if a = b then framePoint u a else 0 := by
  rw [mul_framePoint_general hun, coeff_one, coeff_two, coeff_three]
  by_cases hab : a = b
  · subst hab
    simp only [sub_self, if_true]
    unfold framePoint
    module
  · have h1 : outcome b - outcome a ≠ 0 := sub_ne_zero.mpr (fun h => hab (outcome_injective h).symm)
    have h2 : outcome a - outcome b ≠ 0 := sub_ne_zero.mpr (fun h => hab (outcome_injective h))
    rw [if_neg h1, if_neg h2, if_neg hab]
    simp

include hρ hg hu in
theorem ip_framePoint_one (a : Fin 3) : ip (framePoint u a) one = 1 := by
  have hu0 : ip u one = 0 := by rw [ip_one_right]; exact tr_eq_zero_of_mem hρ hg hu
  have hub0 : ip (conj u) one = 0 := by
    rw [ip_one_right]; exact tr_eq_zero_of_mem hρ (neg_ne_zero.mpr hg) (conj_mem_charSpace hu)
  unfold framePoint
  rw [ip_smul_left, ip_add_left, ip_add_left, ip_smul_left, ip_smul_left, hu0, hub0, ip_one_one]
  ring

theorem sum_framePoint : framePoint u 0 + framePoint u 1 + framePoint u 2 = one := by
  have hs := sum_phase_outcome
  have hs' := sum_phase_neg_outcome
  rw [Fin.sum_univ_three] at hs hs'
  unfold framePoint
  have e : (1 / 3 : ℂ) • (one + chargePhase (-outcome 0) • u + chargePhase (outcome 0) • conj u) +
      (1 / 3 : ℂ) • (one + chargePhase (-outcome 1) • u + chargePhase (outcome 1) • conj u) +
      (1 / 3 : ℂ) • (one + chargePhase (-outcome 2) • u + chargePhase (outcome 2) • conj u) =
      one + ((1 / 3 : ℂ) * (chargePhase (-outcome 0) + chargePhase (-outcome 1) +
        chargePhase (-outcome 2))) • u + ((1 / 3 : ℂ) * (chargePhase (outcome 0) +
        chargePhase (outcome 1) + chargePhase (outcome 2))) • conj u := by module
  rw [e, hs, hs']
  simp

include hρ hg hu hun in
/-- The frame of a normalized element. -/
theorem isFrameOf_framePointReal : IsFrameOf u (framePointReal u) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, of_framePointReal⟩
  · intro a
    have h := ip_framePoint_one hρ hg hu a
    rw [← of_framePointReal a, show one = of 1 from rfl, ip_of] at h
    rw [← nativeInner_one_right]
    exact_mod_cast congrArg Complex.re h
  · intro a
    apply of_injective
    rw [← of_mul, of_framePointReal, mul_framePoint hun, if_pos rfl]
  · intro a b hab
    apply of_injective
    rw [← of_mul, of_framePointReal, of_framePointReal, mul_framePoint hun, if_neg hab, of_zero]
  · apply of_injective
    rw [of_add, of_add, of_framePointReal, of_framePointReal, of_framePointReal,
      sum_framePoint]
    rfl

theorem contrast_framePointReal : contrast (framePointReal u) = u := by
  unfold contrast
  simp only [of_framePointReal]
  rw [Fin.sum_univ_three]
  unfold framePoint
  rw [show outcome 0 = 0 from rfl, show outcome 1 = 1 from rfl, show outcome 2 = 2 from rfl,
    neg_zero, show (-(1 : ZMod 3)) = 2 from by decide, show (-(2 : ZMod 3)) = 1 from by decide,
    chargePhase_zero, phase_one, phase_two]
  have hq := chargeRoot_quadratic
  have hc := chargeRoot_cube
  have e : (1 : ℂ) • ((1 / 3 : ℂ) • (one + (1 : ℂ) • u + (1 : ℂ) • conj u)) +
      chargeRoot • ((1 / 3 : ℂ) • (one + chargeRoot ^ 2 • u + chargeRoot • conj u)) +
      chargeRoot ^ 2 • ((1 / 3 : ℂ) • (one + chargeRoot • u + chargeRoot ^ 2 • conj u)) =
      ((1 / 3 : ℂ) * (1 + chargeRoot + chargeRoot ^ 2)) • one +
        ((1 / 3 : ℂ) * (1 + chargeRoot ^ 3 + chargeRoot ^ 3)) • u +
        ((1 / 3 : ℂ) * (1 + chargeRoot ^ 2 + chargeRoot ^ 4)) • conj u := by module
  rw [e, hc, show chargeRoot ^ 4 = chargeRoot by rw [pow_succ, hc, _root_.one_mul],
    show (1 : ℂ) + chargeRoot + chargeRoot ^ 2 = 0 by linear_combination hq,
    show (1 : ℂ) + chargeRoot ^ 2 + chargeRoot = 0 by linear_combination hq]
  simp
  norm_num

end Frame

end

end ThirteenPlanes.AlbertGrading.Grading
