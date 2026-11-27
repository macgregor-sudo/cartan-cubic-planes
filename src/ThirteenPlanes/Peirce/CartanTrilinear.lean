module

public import ThirteenPlanes.Peirce.SlotTransport

@[expose] public section

set_option backward.privateInPublic true

/-! All marked trace coefficients from the full diagonal polynomial of a concrete model. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

variable {V K : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

abbrev CartanCoordinates (K : Type*) := ℝ × ℝ × K × K × K

namespace CartanCoordinates

variable (x y : CartanCoordinates K)

abbrev a := x.1
abbrev b := x.2.1
abbrev first := x.2.2.1
abbrev second := x.2.2.2.1
abbrev third := x.2.2.2.2

abbrev minusPair := x.b * y.b + ⟪x.first, y.first⟫
abbrev halfPair := ⟪x.second, y.second⟫ + ⟪x.third, y.third⟫
abbrev halfDifference := ⟪x.third, y.third⟫ - ⟪x.second, y.second⟫

end CartanCoordinates

/-- The polarized Cartan formula on the five normalized coordinates. -/
def cartanCoordinateTriple (φ : K →ₗ[ℝ] K →ₗ[ℝ] K) (x y z : CartanCoordinates K) : ℝ :=
  x.a * y.a * z.a -
  (x.a * y.minusPair z + y.a * x.minusPair z + z.a * x.minusPair y) +
  (1 / 2 : ℝ) * (x.a * y.halfPair z + y.a * x.halfPair z + z.a * x.halfPair y) +
  (Real.sqrt 3 / 2) *
    (x.b * y.halfDifference z + y.b * x.halfDifference z + z.b * x.halfDifference y +
     ⟪φ x.first y.second, z.third⟫ + ⟪φ x.first z.second, y.third⟫ +
     ⟪φ y.first x.second, z.third⟫ + ⟪φ y.first z.second, x.third⟫ +
     ⟪φ z.first x.second, y.third⟫ + ⟪φ z.first y.second, x.third⟫)

private theorem diagonal_polarize (h : SymmetricCubic V) (x y z : V) :
    6 * h.apply x y z =
      h.apply (x + y + z) (x + y + z) (x + y + z) -
      h.apply (x + y) (x + y) (x + y) - h.apply (x + z) (x + z) (x + z) -
      h.apply (y + z) (y + z) (y + z) + h.apply x x x + h.apply y y y + h.apply z z z := by
  have h₁₃₂ := h.apply_swap₂₃ x z y
  have h₂₁₃ := h.apply_swap₁₂ y x z
  have h₂₃₁ := (h.apply_swap₂₃ y z x).trans h₂₁₃
  have h₃₁₂ := (h.apply_swap₁₂ z x y).trans h₁₃₂
  have h₃₂₁ := (h.apply_swap₁₂ z y x).trans h₂₃₁
  simp only [SymmetricCubic.apply_add₁, SymmetricCubic.apply_add₂, SymmetricCubic.apply_add₃,
    h₁₃₂, h₂₁₃, h₂₃₁, h₃₁₂, h₃₂₁]
  ring

set_option maxHeartbeats 800000 in
/-- The diagonal determines the exact trilinear coefficients on all five actual coordinates. -/
theorem cartanCoordinateTriple_of_normalForm (h : SymmetricCubic V)
    (e : CartanCoordinates K ≃ₗ[ℝ] V) (φ : K →ₗ[ℝ] K →ₗ[ℝ] K)
    (hpoly : ∀ (α β : ℝ) (u p q : K), let x := e (α, β, u, p, q)
      h.apply x x x = α ^ 3 - 3 * α * (β ^ 2 + ‖u‖ ^ 2) +
        (3 / 2 : ℝ) * α * (‖p‖ ^ 2 + ‖q‖ ^ 2) +
        (3 * Real.sqrt 3 / 2) * β * (‖q‖ ^ 2 - ‖p‖ ^ 2) +
        3 * Real.sqrt 3 * ⟪φ u p, q⟫)
    (x y z : CartanCoordinates K) : h.apply (e x) (e y) (e z) = cartanCoordinateTriple φ x y z := by
  have hc (t : CartanCoordinates K) :
      h.apply (e t) (e t) (e t) = t.a ^ 3 - 3 * t.a * (t.b ^ 2 + ‖t.first‖ ^ 2) +
        (3 / 2 : ℝ) * t.a * (‖t.second‖ ^ 2 + ‖t.third‖ ^ 2) +
        (3 * Real.sqrt 3 / 2) * t.b * (‖t.third‖ ^ 2 - ‖t.second‖ ^ 2) +
        3 * Real.sqrt 3 * ⟪φ t.first t.second, t.third⟫ := by
    rcases t with ⟨α, β, u, p, q⟩
    exact hpoly α β u p q
  have hp := diagonal_polarize h (e x) (e y) (e z)
  rw [← e.map_add x y, ← e.map_add (x + y) z, ← e.map_add x z, ← e.map_add y z] at hp
  rw [hc (x + y + z), hc (x + y), hc (x + z), hc (y + z), hc x, hc y, hc z] at hp
  simp only [CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first,
    CartanCoordinates.second, CartanCoordinates.third, Prod.fst_add, Prod.snd_add,
    ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, map_add, LinearMap.add_apply] at hp
  simp only [cartanCoordinateTriple, CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first,
    CartanCoordinates.second, CartanCoordinates.third, CartanCoordinates.minusPair,
    CartanCoordinates.halfPair, CartanCoordinates.halfDifference]
  simp only [real_inner_comm] at hp ⊢
  linear_combination (1 / 6 : ℝ) * hp

/-- The literal N1–N3 assertions on the image of the two scalar axes and the three
coordinate slots. Since `e` is onto, the stated orthogonal pairing gives their decomposition. -/
structure CartanCoordinateConditions (h : SymmetricCubic V) (e : CartanCoordinates K ≃ₗ[ℝ] V)
    (φ : K →ₗ[ℝ] K →ₗ[ℝ] K) : Prop where
  pairing : ∀ x y : CartanCoordinates K,
    ⟪e x, e y⟫ = x.a * y.a + x.minusPair y + x.halfPair y
  idempotent : h.L (e (1, 0, 0, 0, 0)) (e (1, 0, 0, 0, 0)) = e (1, 0, 0, 0, 0)
  minus_action : ∀ (β : ℝ) (u : K), h.L (e (1, 0, 0, 0, 0)) (e (0, β, u, 0, 0)) = -e (0, β, u, 0, 0)
  half_action : ∀ p q : K, h.L (e (1, 0, 0, 0, 0)) (e (0, 0, 0, p, q)) = (1 / 2 : ℝ) • e (0, 0, 0, p, q)
  minus_minus_minus : ∀ (b₁ b₂ b₃ : ℝ) (u₁ u₂ u₃ : K),
    h.apply (e (0, b₁, u₁, 0, 0)) (e (0, b₂, u₂, 0, 0)) (e (0, b₃, u₃, 0, 0)) = 0
  minus_minus_half : ∀ (b₁ b₂ : ℝ) (u₁ u₂ p q : K),
    h.apply (e (0, b₁, u₁, 0, 0)) (e (0, b₂, u₂, 0, 0)) (e (0, 0, 0, p, q)) = 0
  half_half_half : ∀ p₁ p₂ p₃ q₁ q₂ q₃ : K,
    h.apply (e (0, 0, 0, p₁, q₁)) (e (0, 0, 0, p₂, q₂)) (e (0, 0, 0, p₃, q₃)) = 0
  b_second_second : ∀ p p' : K,
    h.apply (e (0, 1, 0, 0, 0)) (e (0, 0, 0, p, 0)) (e (0, 0, 0, p', 0)) =
      -(Real.sqrt 3 / 2) * ⟪p, p'⟫
  b_third_third : ∀ q q' : K,
    h.apply (e (0, 1, 0, 0, 0)) (e (0, 0, 0, 0, q)) (e (0, 0, 0, 0, q')) =
      (Real.sqrt 3 / 2) * ⟪q, q'⟫
  b_second_third : ∀ p q : K, h.apply (e (0, 1, 0, 0, 0)) (e (0, 0, 0, p, 0)) (e (0, 0, 0, 0, q)) = 0
  first_second_second : ∀ u p p' : K,
    h.apply (e (0, 0, u, 0, 0)) (e (0, 0, 0, p, 0)) (e (0, 0, 0, p', 0)) = 0
  first_third_third : ∀ u q q' : K,
    h.apply (e (0, 0, u, 0, 0)) (e (0, 0, 0, 0, q)) (e (0, 0, 0, 0, q')) = 0
  first_second_third : ∀ u p q : K,
    h.apply (e (0, 0, u, 0, 0)) (e (0, 0, 0, p, 0)) (e (0, 0, 0, 0, q)) =
      (Real.sqrt 3 / 2) * ⟪φ u p, q⟫

/-- The normalized coordinate metric and polynomial give all N1–N3 coefficients. -/
theorem cartanCoordinateConditions_of_normalForm (h : SymmetricCubic V)
    (e : CartanCoordinates K ≃ₗ[ℝ] V) (φ : K →ₗ[ℝ] K →ₗ[ℝ] K)
    (he : ∀ (α β : ℝ) (u p q : K), ‖e (α, β, u, p, q)‖ ^ 2 =
      α ^ 2 + β ^ 2 + ‖u‖ ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2)
    (hpoly : ∀ (α β : ℝ) (u p q : K), let x := e (α, β, u, p, q)
      h.apply x x x = α ^ 3 - 3 * α * (β ^ 2 + ‖u‖ ^ 2) +
        (3 / 2 : ℝ) * α * (‖p‖ ^ 2 + ‖q‖ ^ 2) +
        (3 * Real.sqrt 3 / 2) * β * (‖q‖ ^ 2 - ‖p‖ ^ 2) +
        3 * Real.sqrt 3 * ⟪φ u p, q⟫) : CartanCoordinateConditions h e φ := by
  have hn (x : CartanCoordinates K) : ‖e x‖ ^ 2 =
      x.a ^ 2 + x.b ^ 2 + ‖x.first‖ ^ 2 + ‖x.second‖ ^ 2 + ‖x.third‖ ^ 2 := by
    rcases x with ⟨α, β, u, p, q⟩
    exact he α β u p q
  have hi (x y : CartanCoordinates K) :
      ⟪e x, e y⟫ = x.a * y.a + x.minusPair y + x.halfPair y := by
    have H := norm_add_sq_real (e x) (e y)
    rw [← e.map_add x y, hn (x + y), hn x, hn y] at H
    simp only [CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first, CartanCoordinates.second,
      CartanCoordinates.third, Prod.fst_add, Prod.snd_add, norm_add_sq_real] at H
    dsimp only [CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.minusPair, CartanCoordinates.halfPair,
      CartanCoordinates.first, CartanCoordinates.second, CartanCoordinates.third]
    linarith only [H, add_sq x.a y.a, add_sq x.b y.b]
  have hc := cartanCoordinateTriple_of_normalForm h e φ hpoly
  refine ⟨hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_inner_right ℝ
    intro z
    obtain ⟨z, rfl⟩ := e.surjective z
    change h.apply (e (1, 0, 0, 0, 0)) (e (1, 0, 0, 0, 0)) (e z) = _
    rw [hc, hi]
    simp [cartanCoordinateTriple, CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first,
      CartanCoordinates.second, CartanCoordinates.third, CartanCoordinates.minusPair, CartanCoordinates.halfPair,
      CartanCoordinates.halfDifference]
  · intro β u
    apply ext_inner_right ℝ
    intro z
    obtain ⟨z, rfl⟩ := e.surjective z
    change h.apply (e (1, 0, 0, 0, 0)) (e (0, β, u, 0, 0)) (e z) = _
    rw [hc, inner_neg_left, hi]
    simp [cartanCoordinateTriple, CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first,
      CartanCoordinates.second, CartanCoordinates.third, CartanCoordinates.minusPair, CartanCoordinates.halfPair,
      CartanCoordinates.halfDifference]
  · intro p q
    apply ext_inner_right ℝ
    intro z
    obtain ⟨z, rfl⟩ := e.surjective z
    change h.apply (e (1, 0, 0, 0, 0)) (e (0, 0, 0, p, q)) (e z) = _
    rw [hc, real_inner_smul_left, hi]
    simp [cartanCoordinateTriple, CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first,
      CartanCoordinates.second, CartanCoordinates.third, CartanCoordinates.minusPair, CartanCoordinates.halfPair,
      CartanCoordinates.halfDifference]
  all_goals
    intros
    rw [hc]
    simp [cartanCoordinateTriple, CartanCoordinates.a, CartanCoordinates.b, CartanCoordinates.first,
      CartanCoordinates.second, CartanCoordinates.third, CartanCoordinates.minusPair, CartanCoordinates.halfPair,
      CartanCoordinates.halfDifference]


end

end ThirteenPlanes.Peirce
