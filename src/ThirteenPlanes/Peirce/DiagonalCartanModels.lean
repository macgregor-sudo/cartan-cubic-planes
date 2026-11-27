module

public import ThirteenPlanes.Peirce.CartanModelConditions
public import ThirteenPlanes.PeirceDecomposition

@[expose] public section

set_option backward.privateInPublic true

/-! The diagonal marks and their literal joint eigenspaces in the four Cartan models. -/

open scoped Quaternion InnerProductSpace RealInnerProductSpace
open scoped ThirteenPlanes.MarkedPlane.NativeOctonionEuclidean

namespace ThirteenPlanes.Peirce

noncomputable section

variable {V K : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The normalized diagonal formula with the given off-diagonal multiplication. -/
def ModelCoordinateNormalForm (h : SymmetricCubic V) (e : CartanCoordinates K ≃ₗ[ℝ] V)
    (φ : K →ₗ[ℝ] K →ₗ[ℝ] K) : Prop :=
  ∀ (α β : ℝ) (u p q : K), let x := e (α, β, u, p, q)
    h.apply x x x = α ^ 3 - 3 * α * (β ^ 2 + ‖u‖ ^ 2) +
      (3 / 2 : ℝ) * α * (‖p‖ ^ 2 + ‖q‖ ^ 2) +
      (3 * Real.sqrt 3 / 2) * β * (‖q‖ ^ 2 - ‖p‖ ^ 2) +
      3 * Real.sqrt 3 * ⟪φ u p, q⟫

/-- Hermitian slot models with the slots described by their joint actions and literal matrix coordinates. -/
structure CartanModelAtDiagonal (h : SymmetricCubic V) (e : CartanCoordinates K ≃ₗ[ℝ] V)
    (φ : K →ₗ[ℝ] K →ₗ[ℝ] K) : Prop where
  unitIdempotent : IsUnitIdempotent h (e (1, 0, 0, 0, 0))
  minusMark : ‖e (0, 1, 0, 0, 0)‖ = 1 ∧ h.L (e (1, 0, 0, 0, 0)) (e (0, 1, 0, 0, 0)) =
      -e (0, 1, 0, 0, 0)
  one : ∀ x, (h.L (e (1, 0, 0, 0, 0)) x = -x ∧ ⟪x, e (0, 1, 0, 0, 0)⟫ = 0) ↔
    ∃ p, x = e (0, 0, p, 0, 0)
  two : ∀ x, (h.L (e (1, 0, 0, 0, 0)) x = (1 / 2 : ℝ) • x ∧
    h.L (e (0, 1, 0, 0, 0)) x = -(Real.sqrt 3 / 2) • x) ↔
    ∃ p, x = e (0, 0, 0, p, 0)
  three : ∀ x, (h.L (e (1, 0, 0, 0, 0)) x = (1 / 2 : ℝ) • x ∧
    h.L (e (0, 1, 0, 0, 0)) x = (Real.sqrt 3 / 2) • x) ↔
    ∃ q, x = e (0, 0, 0, 0, q)
  product : ∀ p q, (2 / Real.sqrt 3 : ℝ) • h.L (e (0, 0, p, 0, 0)) (e (0, 0, 0, q, 0)) =
    e (0, 0, 0, 0, φ p q)
  normalForm : ModelCoordinateNormalForm h e φ

private theorem smul_eq_iff_of_coeff_ne (s t : ℝ) (hne : s ≠ t) (x : K) :
    s • x = t • x ↔ x = 0 := by
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero]
  simp [sub_ne_zero.mpr hne]

private theorem smul_tuple (s α β : ℝ) (p q r : K) :
    s • (α, β, p, q, r) = (s * α, s * β, s • p, s • q, s • r) := rfl

set_option maxHeartbeats 1200000 in
/-- The full coefficient formula determines the diagonal multiplication actions and slot product. -/
theorem CartanCoordinateConditions.modelAtDiagonal {h : SymmetricCubic V}
    {e : CartanCoordinates K ≃ₗ[ℝ] V} {φ : K →ₗ[ℝ] K →ₗ[ℝ] K}
    (hc : CartanCoordinateConditions h e φ) (hn : ModelCoordinateNormalForm h e φ) :
    CartanModelAtDiagonal h e φ := by
  let a := e (1, 0, 0, 0, 0)
  let b := e (0, 1, 0, 0, 0)
  let t := Real.sqrt 3 / 2
  have tpos : 0 < t := div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)
  have tne : -t ≠ t := by linarith
  have hA (α β : ℝ) (u p q : K) :
      h.L a (e (α, β, u, p, q)) = e (α, -β, -u, (1 / 2 : ℝ) • p, (1 / 2 : ℝ) • q) := by
    apply ext_inner_right ℝ
    intro z
    obtain ⟨z, rfl⟩ := e.surjective z
    change h.apply (e (1, 0, 0, 0, 0)) (e (α, β, u, p, q)) (e z) = _
    rw [cartanCoordinateTriple_of_normalForm h e φ hn, hc.pairing]
    simp [cartanCoordinateTriple, CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first,
      CartanCoordinates.second, CartanCoordinates.third, CartanCoordinates.minusPair, CartanCoordinates.halfPair,
      CartanCoordinates.halfDifference, real_inner_smul_left]
    ring
  have hB (α β : ℝ) (u p q : K) :
      h.L b (e (α, β, u, p, q)) = e (-β, -α, 0, (-t) • p, t • q) := by
    apply ext_inner_right ℝ
    intro z
    obtain ⟨z, rfl⟩ := e.surjective z
    change h.apply (e (0, 1, 0, 0, 0)) (e (α, β, u, p, q)) (e z) = _
    rw [cartanCoordinateTriple_of_normalForm h e φ hn, hc.pairing]
    simp [cartanCoordinateTriple, CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first,
      CartanCoordinates.second, CartanCoordinates.third, CartanCoordinates.minusPair, CartanCoordinates.halfPair,
      CartanCoordinates.halfDifference, real_inner_smul_left, t]
    ring
  have ha : ‖a‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    change ‖e (1, 0, 0, 0, 0)‖ ^ 2 = (1 : ℝ) ^ 2
    rw [← real_inner_self_eq_norm_sq, hc.pairing]
    simp [CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first, CartanCoordinates.second,
      CartanCoordinates.third, CartanCoordinates.minusPair, CartanCoordinates.halfPair]
  have hb : ‖b‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    change ‖e (0, 1, 0, 0, 0)‖ ^ 2 = (1 : ℝ) ^ 2
    rw [← real_inner_self_eq_norm_sq, hc.pairing]
    simp [CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first, CartanCoordinates.second,
      CartanCoordinates.third, CartanCoordinates.minusPair, CartanCoordinates.halfPair]
  have hhalf (α β : ℝ) (u p q : K) :
      h.L a (e (α, β, u, p, q)) = (1 / 2 : ℝ) • e (α, β, u, p, q) ↔
      α = 0 ∧ β = 0 ∧ u = 0 := by
    rw [hA, ← e.map_smul, smul_tuple, e.injective.eq_iff]
    simp only [Prod.mk.injEq, and_true]
    rw [← neg_one_smul ℝ u,
      smul_eq_iff_of_coeff_ne (-1) (1 / 2) (by norm_num)]
    grind
  refine ⟨⟨ha, hc.idempotent⟩, ⟨hb, hc.minus_action 1 0⟩, ?_, ?_, ?_, ?_, hn⟩
  · intro x
    obtain ⟨⟨α, β, u, p, q⟩, rfl⟩ := e.surjective x
    change (h.L a (e (α, β, u, p, q)) = -e (α, β, u, p, q) ∧
      ⟪e (α, β, u, p, q), e (0, 1, 0, 0, 0)⟫ = 0) ↔ _
    have hneg : -e (α, β, u, p, q) = e (-α, -β, -u, -p, -q) := (e.map_neg _).symm
    rw [hA, hneg, e.injective.eq_iff, hc.pairing]
    simp only [CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first,
      CartanCoordinates.second, CartanCoordinates.third, CartanCoordinates.minusPair, CartanCoordinates.halfPair,
      mul_zero, mul_one, inner_zero_right, add_zero, zero_add, Prod.mk.injEq, e.injective.eq_iff, eq_self, true_and]
    rw [← neg_one_smul ℝ p, ← neg_one_smul ℝ q,
      smul_eq_iff_of_coeff_ne (1 / 2) (-1) (by norm_num),
      smul_eq_iff_of_coeff_ne (1 / 2) (-1) (by norm_num)]
    constructor
    · rintro ⟨⟨hα, hp, hq⟩, rfl⟩
      exact ⟨u, by linarith, rfl, rfl, hp, hq⟩
    · rintro ⟨v, rfl, rfl, rfl, rfl, rfl⟩
      simp
  · intro x
    obtain ⟨⟨α, β, u, p, q⟩, rfl⟩ := e.surjective x
    change (h.L a (e (α, β, u, p, q)) = (1 / 2 : ℝ) • e (α, β, u, p, q) ∧
      h.L b (e (α, β, u, p, q)) = (-t) • e (α, β, u, p, q)) ↔ _
    rw [hhalf, hB, ← e.map_smul, smul_tuple, e.injective.eq_iff]
    constructor
    · rintro ⟨⟨rfl, rfl, rfl⟩, h⟩
      have hq := congrArg (fun z : CartanCoordinates K => z.2.2.2.2) h
      exact ⟨p, by rw [(smul_eq_iff_of_coeff_ne t (-t) tne.symm q).mp hq]⟩
    · rintro ⟨v, hv⟩
      have he := e.injective hv
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl, rfl, rfl, rfl⟩
      simp
  · intro x
    obtain ⟨⟨α, β, u, p, q⟩, rfl⟩ := e.surjective x
    change (h.L a (e (α, β, u, p, q)) = (1 / 2 : ℝ) • e (α, β, u, p, q) ∧
      h.L b (e (α, β, u, p, q)) = t • e (α, β, u, p, q)) ↔ _
    rw [hhalf, hB, ← e.map_smul, smul_tuple, e.injective.eq_iff]
    constructor
    · rintro ⟨⟨rfl, rfl, rfl⟩, h⟩
      have hp := congrArg (fun z : CartanCoordinates K => z.2.2.2.1) h
      exact ⟨q, by rw [(smul_eq_iff_of_coeff_ne (-t) t tne p).mp hp]⟩
    · rintro ⟨v, hv⟩
      have he := e.injective hv
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl, rfl, rfl, rfl⟩
      simp
  · intro p q
    apply ext_inner_right ℝ
    intro z
    obtain ⟨z, rfl⟩ := e.surjective z
    rw [real_inner_smul_left]
    change (2 / Real.sqrt 3) * h.apply (e (0, 0, p, 0, 0)) (e (0, 0, 0, q, 0)) (e z) = _
    rw [cartanCoordinateTriple_of_normalForm h e φ hn, hc.pairing]
    simp [cartanCoordinateTriple, CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first,
      CartanCoordinates.second, CartanCoordinates.third, CartanCoordinates.minusPair, CartanCoordinates.halfPair,
      CartanCoordinates.halfDifference]
    field_simp [Real.sqrt_pos.mpr (by norm_num : 0 < (3 : ℝ)) |>.ne']

/-- The exact real symmetric model in the paper's coordinates. -/
theorem realCartan_modelAtDiagonal :
    CartanModelAtDiagonal realCartanCubic realCartanEquiv (conjugateSlotProduct ℝ) := by
  apply realCartan_modelConditions.modelAtDiagonal
  intro α β p q r
  simpa only [conjugateSlotProduct_apply, star_trivial] using realCartanCubic_normalForm α β p q r

/-- The exact complex Hermitian model in the paper's coordinates. -/
theorem complexCartan_modelAtDiagonal :
    CartanModelAtDiagonal complexCartanCubic complexCartanEquiv (conjugateSlotProduct ℂ) :=
  complexCartan_modelConditions.modelAtDiagonal complexCartanCubic_normalForm

/-- The exact quaternionic Hermitian model in the paper's coordinates. -/
theorem quaternionCartan_modelAtDiagonal :
    CartanModelAtDiagonal quaternionCartanCubic quaternionCartanEquiv (conjugateSlotProduct (Quaternion ℝ)) :=
  quaternionCartan_modelConditions.modelAtDiagonal quaternionCartanCubic_normalForm

/-- The exact Albert model, with the order of the two octonion factors fixed. -/
theorem nativeCartan_modelAtDiagonal :
    CartanModelAtDiagonal nativeCartanCubic nativeCartanEquiv nativeConjugateSlotProduct :=
  nativeCartan_modelConditions.modelAtDiagonal nativeCartanCubic_normalForm

end

end ThirteenPlanes.Peirce
