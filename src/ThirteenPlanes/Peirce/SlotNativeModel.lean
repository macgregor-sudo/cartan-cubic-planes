module

public import ThirteenPlanes.Peirce.SlotCubic
public import ThirteenPlanes.Isotope.NativeOctonion
public import ThirteenPlanes.NativeFramesCarrier
public import Glennie.Native.Triality

@[expose] public section

set_option backward.privateInPublic true

/-! The marked trace coordinates and cubic of the actual native Albert model. -/

open scoped InnerProductSpace RealInnerProductSpace ThirteenPlanes.MarkedPlane.NativeOctonionEuclidean

namespace ThirteenPlanes.Peirce

noncomputable section

open Glennie MarkedPlane

local notation "𝕆ₙ" => AlbertSequential.Octonion
private abbrev s₂ : ℝ := (Real.sqrt 2)⁻¹
private abbrev s₆ : ℝ := (Real.sqrt 6)⁻¹

private theorem s₂_sq : s₂ ^ 2 = 1 / 2 := by
  unfold s₂
  rw [inv_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  norm_num

private theorem s₆_sq : s₆ ^ 2 = 1 / 6 := by
  unfold s₆
  rw [inv_pow, Real.sq_sqrt (by norm_num : 0 ≤ (6 : ℝ))]
  norm_num

private theorem sqrt_s₆ : Real.sqrt 6 * s₆ = 1 :=
  mul_inv_cancel₀ (Real.sqrt_pos.mpr (by norm_num)).ne'

private theorem sqrt_s₂ : Real.sqrt 6 * s₂ = Real.sqrt 3 := by
  unfold s₂
  rw [show (6 : ℝ) = 3 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
    mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne', mul_one]

private theorem nativeOctonion_inner_glennie (x y : 𝕆ₙ) : ⟪x, y⟫ = Glennie.octDot x y := by
  rw [nativeOctonion_inner]
  rfl

private theorem nativeOctonion_norm_sq_glennie (x : 𝕆ₙ) : ‖x‖ ^ 2 = Glennie.octNormSq x := by
  rw [← real_inner_self_eq_norm_sq, nativeOctonion_inner_glennie]
  exact Glennie.octDot_self x

/-- Normalized native coordinates in the actual traceless Albert carrier, with off-diagonal
entries in positions 23, 13, and 12 in that order. -/
def nativeCartanField (α β : ℝ) (p q r : 𝕆ₙ) : NativeTraceless :=
  ⟨⟨2 * (s₆ * α), -(s₆ * α) + s₂ * β, -(s₆ * α) - s₂ * β,
     s₂ • r, s₂ • q, s₂ • p⟩, by change 2 * (s₆ * α) + (-(s₆ * α) + s₂ * β) +
       (-(s₆ * α) - s₂ * β) = 0; ring⟩

/-- The coordinate map uses the raw Jordan trace metric. -/
theorem nativeCartanField_inner (α β α' β' : ℝ) (p q r p' q' r' : 𝕆ₙ) :
    ⟪nativeCartanField α β p q r, nativeCartanField α' β' p' q' r'⟫ =
      α * α' + β * β' + ⟪p, p'⟫ + ⟪q, q'⟫ + ⟪r, r'⟫ := by
  change Glennie.inner (nativeCartanField α β p q r) (nativeCartanField α' β' p' q' r') = _
  rw [Glennie.inner_coordinates]
  dsimp only [nativeCartanField]
  simp only [← nativeOctonion_inner_glennie, real_inner_smul_left, real_inner_smul_right]
  calc
    _ = (6 * s₆ ^ 2) * (α * α') + (2 * s₂ ^ 2) *
        (β * β' + ⟪p, p'⟫ + ⟪q, q'⟫ + ⟪r, r'⟫) := by ring
    _ = _ := by rw [s₂_sq, s₆_sq]; ring

theorem nativeCartanField_norm_sq (α β : ℝ) (p q r : 𝕆ₙ) :
    ‖nativeCartanField α β p q r‖ ^ 2 = α ^ 2 + β ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2 + ‖r‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, nativeCartanField_inner]
  simp only [real_inner_self_eq_norm_sq, pow_two]

/-- Normalized coordinates as a real linear map to the actual trace kernel. -/
def nativeCartanLinear : (ℝ × ℝ × 𝕆ₙ × 𝕆ₙ × 𝕆ₙ) →ₗ[ℝ] NativeTraceless where
  toFun t := nativeCartanField t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  map_add' t w := by
    rcases t with ⟨α, β, p, q, r⟩
    rcases w with ⟨α', β', p', q', r'⟩
    apply Subtype.ext
    apply Glennie.Albert.ext
    · change 2 * (s₆ * (α + α')) = 2 * (s₆ * α) + 2 * (s₆ * α'); ring
    · change -(s₆ * (α + α')) + s₂ * (β + β') =
        -(s₆ * α) + s₂ * β + (-(s₆ * α') + s₂ * β'); ring
    · change -(s₆ * (α + α')) - s₂ * (β + β') =
        -(s₆ * α) - s₂ * β + (-(s₆ * α') - s₂ * β'); ring
    · exact smul_add s₂ r r'
    · exact smul_add s₂ q q'
    · exact smul_add s₂ p p'
  map_smul' c t := by
    rcases t with ⟨α, β, p, q, r⟩
    apply Subtype.ext
    apply Glennie.Albert.ext
    · change 2 * (s₆ * (c * α)) = c * (2 * (s₆ * α)); ring
    · change -(s₆ * (c * α)) + s₂ * (c * β) = c * (-(s₆ * α) + s₂ * β); ring
    · change -(s₆ * (c * α)) - s₂ * (c * β) = c * (-(s₆ * α) - s₂ * β); ring
    · exact smul_comm s₂ c r
    · exact smul_comm s₂ c q
    · exact smul_comm s₂ c p

private theorem nativeCartanLinear_bijective : Function.Bijective nativeCartanLinear := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    rintro ⟨α, β, p, q, r⟩ hx
    change nativeCartanField α β p q r = 0 at hx
    have h := nativeCartanField_norm_sq α β p q r
    rw [hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    have hα : α = 0 := by nlinarith only [h, sq_nonneg β, sq_nonneg ‖p‖, sq_nonneg ‖q‖, sq_nonneg ‖r‖]
    have hβ : β = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg ‖p‖, sq_nonneg ‖q‖, sq_nonneg ‖r‖]
    have hp : ‖p‖ = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg β, sq_nonneg ‖q‖, sq_nonneg ‖r‖]
    have hq : ‖q‖ = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg β, sq_nonneg ‖p‖, sq_nonneg ‖r‖]
    have hr : ‖r‖ = 0 := by nlinarith only [h, sq_nonneg α, sq_nonneg β, sq_nonneg ‖p‖, sq_nonneg ‖q‖]
    rw [hα, hβ, norm_eq_zero.mp hp, norm_eq_zero.mp hq, norm_eq_zero.mp hr]
    rfl
  · intro x
    let X : Glennie.Albert := x
    have htrace : X.d0 + X.d1 + X.d2 = 0 := x.property
    have h₂ : s₂ * Real.sqrt 2 = 1 :=
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have h₆ : s₆ * Real.sqrt 6 = 1 := by rw [mul_comm, sqrt_s₆]
    let α := Real.sqrt 6 * (X.d0 / 2)
    let β := Real.sqrt 2 * (X.d1 + X.d0 / 2)
    have hα : s₆ * α = X.d0 / 2 := by
      rw [show α = Real.sqrt 6 * (X.d0 / 2) from rfl, ← mul_assoc, h₆, one_mul]
    have hβ : s₂ * β = X.d1 + X.d0 / 2 := by
      rw [show β = Real.sqrt 2 * (X.d1 + X.d0 / 2) from rfl, ← mul_assoc, h₂, one_mul]
    refine ⟨(α, β, Real.sqrt 2 • X.o12, Real.sqrt 2 • X.o02, Real.sqrt 2 • X.o01), ?_⟩
    apply Subtype.ext
    apply Glennie.Albert.ext
    · change 2 * (s₆ * α) = X.d0; rw [hα]; ring
    · change -(s₆ * α) + s₂ * β = X.d1; rw [hα, hβ]; ring
    · change -(s₆ * α) - s₂ * β = X.d2; rw [hα, hβ]; linarith only [htrace]
    · change s₂ • (Real.sqrt 2 • X.o01) = X.o01; rw [smul_smul, h₂, one_smul]
    · change s₂ • (Real.sqrt 2 • X.o02) = X.o02; rw [smul_smul, h₂, one_smul]
    · change s₂ • (Real.sqrt 2 • X.o12) = X.o12; rw [smul_smul, h₂, one_smul]

/-- The actual traceless Albert matrices have unique normalized marked coordinates. -/
def nativeCartanEquiv : (ℝ × ℝ × 𝕆ₙ × 𝕆ₙ × 𝕆ₙ) ≃ₗ[ℝ] NativeTraceless :=
  LinearEquiv.ofBijective nativeCartanLinear nativeCartanLinear_bijective

@[simp] theorem nativeCartanEquiv_apply (α β : ℝ) (p q r : 𝕆ₙ) :
    nativeCartanEquiv (α, β, p, q, r) = nativeCartanField α β p q r := rfl

/-- The native trace cubic at the round normalization `c=1`. -/
def nativeCartanCubic : SymmetricCubic NativeTraceless := Real.sqrt 6 • nativeEqualCubic

theorem nativeCartanCubic_apply (x y z : NativeTraceless) :
    nativeCartanCubic.apply x y z = Real.sqrt 6 * Glennie.trace (Glennie.jordan
      (Glennie.jordan (x : Glennie.Albert) y) z) := by
  rw [nativeCartanCubic, SymmetricCubic.apply_smul]
  change Real.sqrt 6 * Glennie.inner (Glennie.traceless (Glennie.jordan x y)) z = _
  rw [nativeInner_center_left]
  rfl

/-- The raw cubic trace formula on the actual binary Jordan-matrix product. -/
theorem nativeAlbert_trace_cube (a b d : ℝ) (p q r : Glennie.Octonion) :
    let x : Glennie.Albert := ⟨a, b, d, r, q, p⟩
    Glennie.inner (Glennie.jordan x x) x =
      a ^ 3 + b ^ 3 + d ^ 3 + 3 * (b + d) * Glennie.octNormSq p +
      3 * (a + d) * Glennie.octNormSq q + 3 * (a + b) * Glennie.octNormSq r +
      6 * Glennie.octDot (Glennie.octMul q (Glennie.octConj p)) r := by
  let C := Glennie.octDot (Glennie.octMul q (Glennie.octConj p)) r
  have h₁ : Glennie.octDot (Glennie.octMul r p) q = C := by
    rw [Glennie.octDot_mul_right, Glennie.octDot_comm]
  have h₂ : Glennie.octDot (Glennie.octMul (Glennie.octConj r) q) p = C := by
    rw [Glennie.octDot_mul_left, Glennie.octConj_conj]
    exact (Glennie.octDot_comm _ _).trans h₁
  dsimp only
  rw [Glennie.inner_coordinates]
  simp only [Glennie.jordan_d0, Glennie.jordan_d1, Glennie.jordan_d2, Glennie.jordan_o01,
    Glennie.jordan_o02, Glennie.jordan_o12, Glennie.octDot_add_left, Glennie.octDot_smul_left,
    h₁, h₂, Glennie.octDot_self]
  unfold C
  ring

private theorem s₂_smul_norm_sq (z : 𝕆ₙ) : ‖s₂ • z‖ ^ 2 = s₂ ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem s₂_triple_inner (p q r : 𝕆ₙ) :
    ⟪AlbertSequential.octonionMul (s₂ • q) (AlbertSequential.octonionConj (s₂ • p)), s₂ • r⟫ =
      s₂ ^ 3 * ⟪AlbertSequential.octonionMul q (AlbertSequential.octonionConj p), r⟫ := by
  have h (x y : Glennie.Octonion) : Glennie.octMul (s₂ • x) (Glennie.octConj (s₂ • y)) =
      (s₂ * s₂) • Glennie.octMul x (Glennie.octConj y) := by
    rw [Glennie.octConj_smul, Glennie.octMul_smul_left, Glennie.octMul_smul_right, smul_smul]
  have hs : AlbertSequential.octonionMul (s₂ • q) (AlbertSequential.octonionConj (s₂ • p)) =
      (s₂ * s₂) • AlbertSequential.octonionMul q (AlbertSequential.octonionConj p) := h q p
  rw [hs, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The full normalized Albert polynomial with the actual off-diagonal product `q * conj p`. -/
theorem nativeCartanCubic_normalForm (α β : ℝ) (p q r : 𝕆ₙ) :
    let x := nativeCartanField α β p q r
    nativeCartanCubic.apply x x x =
      α ^ 3 - 3 * α * (β ^ 2 + ‖p‖ ^ 2) +
      (3 / 2 : ℝ) * α * (‖q‖ ^ 2 + ‖r‖ ^ 2) +
      (3 * Real.sqrt 3 / 2) * β * (‖r‖ ^ 2 - ‖q‖ ^ 2) +
      3 * Real.sqrt 3 * ⟪AlbertSequential.octonionMul q (AlbertSequential.octonionConj p), r⟫ := by
  dsimp only
  rw [nativeCartanCubic_apply]
  change Real.sqrt 6 * Glennie.inner (Glennie.jordan _ _) _ = _
  simp only [nativeCartanField]
  have hc := nativeAlbert_trace_cube (2 * (s₆ * α)) (-(s₆ * α) + s₂ * β)
    (-(s₆ * α) - s₂ * β) (s₂ • p) (s₂ • q) (s₂ • r)
  have hj : Glennie.octDot (Glennie.octMul (s₂ • q) (Glennie.octConj (s₂ • p))) (s₂ • r) =
      ⟪AlbertSequential.octonionMul (s₂ • q) (AlbertSequential.octonionConj (s₂ • p)), s₂ • r⟫ :=
    (nativeOctonion_inner_glennie _ _).symm
  rw [hc]
  rw [← nativeOctonion_norm_sq_glennie (s₂ • p), ← nativeOctonion_norm_sq_glennie (s₂ • q),
    ← nativeOctonion_norm_sq_glennie (s₂ • r), hj]
  rw [s₂_smul_norm_sq, s₂_smul_norm_sq, s₂_smul_norm_sq, s₂_triple_inner]
  calc
    _ = (Real.sqrt 6 * s₆) *
        (6 * s₆ ^ 2 * α ^ 3 - 6 * s₂ ^ 2 * α * (β ^ 2 + ‖p‖ ^ 2) +
          3 * s₂ ^ 2 * α * (‖q‖ ^ 2 + ‖r‖ ^ 2)) +
        (Real.sqrt 6 * s₂) * (3 * s₂ ^ 2 * β * (‖r‖ ^ 2 - ‖q‖ ^ 2) +
          6 * s₂ ^ 2 * ⟪AlbertSequential.octonionMul q (AlbertSequential.octonionConj p), r⟫) := by ring
    _ = _ := by rw [sqrt_s₆, sqrt_s₂, s₂_sq, s₆_sq]; ring


end

end ThirteenPlanes.Peirce
