module

public import ThirteenPlanes.Quaternionic.Algebra
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Conjugating an arbitrary unit imaginary quaternion

The witness is explicit: normalize `i + u` away from `u = -i`, and use `j`
at that exceptional point. This supplies the genuine quaternionic conjugation
needed by Hadamard normalization; it assumes no normal form or group orbit.
-/

noncomputable section
namespace QuaternionicMUB

def qi : Q := ⟨0, 1, 0, 0⟩
def qj : Q := ⟨0, 0, 1, 0⟩

lemma qi_sq : qi * qi = -1 := by
  ext <;> norm_num [qi, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]

lemma qj_normSq : Quaternion.normSq qj = 1 := by
  norm_num [qj, Quaternion.normSq_def']

/-- Every unit imaginary quaternion can be sent to the fixed native `i` by
conjugation with an actual norm-one quaternion. -/
theorem exists_unit_conjugator_to_i (u : Q) (hre : u.re = 0)
    (hn : Quaternion.normSq u = 1) :
    ∃ g : Q, Quaternion.normSq g = 1 ∧ g * u * star g = qi := by
  by_cases hspecial : u = -qi
  · refine ⟨qj, qj_normSq, ?_⟩
    rw [hspecial]
    ext <;> norm_num [qi, qj, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
  · have hu2 : u * u = -1 := by
      have h := Quaternion.sq_eq_neg_normSq.mpr hre
      simpa only [pow_two, hn, Quaternion.coe_one] using h
    let v := qi + u
    have hv : v ≠ 0 := by
      intro h
      apply hspecial
      calc
        u = -qi + (qi + u) := by abel
        _ = -qi := by change -qi + v = -qi; rw [h, add_zero]
    have hintertwine : v * u = qi * v := by
      dsimp [v]
      rw [add_mul, mul_add, hu2, qi_sq]
      exact add_comm _ _
    let g : Q := ‖v‖⁻¹ • v
    have hnorm : ‖g‖ = 1 := by
      dsimp [g]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hgn : Quaternion.normSq g = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, hnorm, one_mul]
    have hgu : g * u = qi * g := by
      dsimp [g]
      rw [smul_mul_assoc, mul_smul_comm, hintertwine]
    refine ⟨g, hgn, ?_⟩
    rw [hgu, mul_assoc, Quaternion.self_mul_star, hgn, Quaternion.coe_one, mul_one]

end QuaternionicMUB
