module

public import ThirteenPlanes.SphereMoments.Energy
public import ThirteenPlanes.Potential

@[expose] public section

/-!
# Coordinate algebra for the floor identity

Contractions of the symmetrized quartic array `S` of a cubic with the pairing array `Π`, under the
hypotheses that the cubic is trace-free and its double contraction is scalar.
-/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

local notation "δ" a:max b:max => (if a = b then (1 : ℝ) else 0)

omit [FiniteDimensional ℝ V] [DecidableEq ι] in
theorem sum_four_perm₂₃ (f : ι → ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f a c b d :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

omit [FiniteDimensional ℝ V] [DecidableEq ι] in
theorem sum_four_perm₃₄ (f : ι → ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f a b d c :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

omit [FiniteDimensional ℝ V] in
theorem sum_mul_delta_delta (F : ι → ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (δ a b * δ c d) = ∑ a, ∑ c, F a a c c := by
  refine Finset.sum_congr rfl fun a _ => ?_
  have : ∀ b, ∑ c, ∑ d, F a b c d * (δ a b * δ c d) = δ a b * ∑ c, F a b c c := fun b => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    simp [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun b _ => this b]
  simp

omit [FiniteDimensional ℝ V] in
/-- Pairing a symmetric quartic array with `Π` gives three times its double trace. -/
theorem sum_mul_pairingArray {T : ι → ι → ι → ι → ℝ} (hT : IsSymmetric4 T) :
    ∑ a, ∑ b, ∑ c, ∑ d, T a b c d * pairingArray a b c d = 3 * ∑ a, ∑ c, T a a c c := by
  have h1 := sum_mul_delta_delta (ι := ι) T
  have h2 : ∑ a, ∑ b, ∑ c, ∑ d, T a b c d * (δ a c * δ b d) = ∑ a, ∑ c, T a a c c := by
    rw [sum_four_perm₂₃, ← h1]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [hT.swap₂₃]
  have h3 : ∑ a, ∑ b, ∑ c, ∑ d, T a b c d * (δ a d * δ b c) = ∑ a, ∑ c, T a a c c := by
    rw [sum_four_perm₃₄, ← h2]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [hT.swap₃₄]
  have hsplit : ∑ a, ∑ b, ∑ c, ∑ d, T a b c d * pairingArray a b c d =
      ∑ a, ∑ b, ∑ c, ∑ d, T a b c d * (δ a b * δ c d) +
      ∑ a, ∑ b, ∑ c, ∑ d, T a b c d * (δ a c * δ b d) +
      ∑ a, ∑ b, ∑ c, ∑ d, T a b c d * (δ a d * δ b c) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [pairingArray]; ring
  rw [hsplit, h1, h2, h3]; ring

omit [FiniteDimensional ℝ V] in
theorem pairingArray_trace (c d : ι) :
    ∑ t, pairingArray t t c d = (Fintype.card ι + 2) * δ c d := by
  simp only [pairingArray, if_true, one_mul, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  have h1 : ∑ t : ι, δ t c * δ t d = δ c d := by
    by_cases h : c = d <;> simp [h, Finset.sum_ite_eq', eq_comm]
  have h2 : ∑ t : ι, δ t d * δ t c = δ c d := by
    by_cases h : c = d <;> simp [h, ite_mul, Finset.sum_ite_eq', eq_comm]
  rw [h1, h2]; ring

namespace SymmetricCubic

theorem symmetrizedArray_trace (h : SymmetricCubic V) (hv : h.TraceFree) (m : ℝ)
    (hM : h.doubleContraction = m • (LinearMap.id : V →ₗ[ℝ] V)) (c d : ι) :
    ∑ t, h.symmetrizedArray e t t c d = 2 * m * δ c d := by
  have hK1 : ∑ t, h.squareArray e t t c d = 0 := by
    simp only [squareArray]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [← Finset.sum_mul, ← trace_L_basis, hv, zero_mul]
  have hK2 : ∀ c d, ∑ t, h.squareArray e t c t d = m * δ c d := by
    intro c d
    have := inner_doubleContraction_eq_sum e h (e c) (e d)
    rw [hM, LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_left, e.inner_eq_ite] at this
    rw [this]
    simp only [squareArray, coefficient]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun n _ => ?_
    rw [h.apply_swap₁₂ (e t) (e c), h.apply_swap₁₂ (e t) (e d)]
  have hK3 : ∑ t, h.squareArray e t d t c = m * δ c d := by
    rw [hK2]; by_cases hcd : c = d <;> simp [hcd, eq_comm]
  have dc : (if d = c then (1 : ℝ) else 0) = if c = d then 1 else 0 := by
    by_cases hcd : c = d <;> simp [hcd, eq_comm]
  simp only [symmetrizedArray, Finset.sum_add_distrib, hK1, hK2, dc]
  ring

end SymmetricCubic

end

end ThirteenPlanes
