module

public import ThirteenPlanes.Peirce.SlotTransport

@[expose] public section

/-! Transport from the marked normal form to an actual model in explicit coordinates. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

variable {V W S₁ S₂ S₃ K : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup S₁] [InnerProductSpace ℝ S₁]
  [NormedAddCommGroup S₂] [InnerProductSpace ℝ S₂]
  [NormedAddCommGroup S₃] [InnerProductSpace ℝ S₃]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Explicit model coordinates with the full metric and polynomial give an onto marked
cubic isometry as soon as their slot multiplication is intertwined. -/
theorem slotCubic_isometry_of_model_coordinates [FiniteDimensional ℝ V]
    (F : SlotCoordinates V S₁ S₂ S₃) (h : SymmetricCubic V) (k : SymmetricCubic W)
    (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃) (hF : SlotNormalConditions F h φ)
    (e : (ℝ × ℝ × K × K × K) ≃ₗ[ℝ] W) (ψ : K → K → K)
    (he_norm : ∀ (α β : ℝ) (u p q : K), ‖e (α, β, u, p, q)‖ ^ 2 =
      α ^ 2 + β ^ 2 + ‖u‖ ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2)
    (he_cubic : ∀ (α β : ℝ) (u p q : K), let x := e (α, β, u, p, q)
      k.apply x x x = α ^ 3 - 3 * α * (β ^ 2 + ‖u‖ ^ 2) +
        (3 / 2 : ℝ) * α * (‖p‖ ^ 2 + ‖q‖ ^ 2) +
        (3 * Real.sqrt 3 / 2) * β * (‖q‖ ^ 2 - ‖p‖ ^ 2) +
        3 * Real.sqrt 3 * ⟪ψ u p, q⟫)
    (ρ₁ : S₁ ≃ₗᵢ[ℝ] K) (ρ₂ : S₂ ≃ₗᵢ[ℝ] K) (ρ₃ : S₃ ≃ₗᵢ[ℝ] K)
    (hρ : ∀ u p, ρ₃ (φ u p) = ψ (ρ₁ u) (ρ₂ p)) :
    ∃ I : V ≃ₗᵢ[ℝ] W, I F.a = e (1, 0, 0, 0, 0) ∧ I F.b = e (0, 1, 0, 0, 0) ∧
      h = k.pullback I.toLinearMap := by
  let f := slotCoordinateEquiv F
  let R := (LinearEquiv.refl ℝ ℝ).prodCongr ((LinearEquiv.refl ℝ ℝ).prodCongr
    (ρ₁.toLinearEquiv.prodCongr (ρ₂.toLinearEquiv.prodCongr ρ₃.toLinearEquiv)))
  let E := f.symm.trans (R.trans e)
  have hE (α β : ℝ) (u : S₁) (p : S₂) (q : S₃) :
       E (f (α, β, u, p, q)) = e (α, β, ρ₁ u, ρ₂ p, ρ₃ q) := by
    simp [E, R]
  have hnorm (x : V) : ‖E x‖ = ‖x‖ := by
    obtain ⟨⟨α, β, u, p, q⟩, rfl⟩ := f.surjective x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hE]
    change ‖e (α, β, ρ₁ u, ρ₂ p, ρ₃ q)‖ ^ 2 = ‖slotCoordinateSum F (α, β, u, p, q)‖ ^ 2
    rw [he_norm, slotCoordinateSum_norm_sq, ρ₁.norm_map, ρ₂.norm_map, ρ₃.norm_map]
  let I : V ≃ₗᵢ[ℝ] W := ⟨E, hnorm⟩
  refine ⟨I, ?_, ?_, ?_⟩
  · have ha := hE 1 0 0 0 0
    change I (slotCoordinateSum F (1, 0, 0, 0, 0)) = e (1, 0, ρ₁ 0, ρ₂ 0, ρ₃ 0) at ha
    simpa [slotCoordinateSum] using ha
  · have hb := hE 0 1 0 0 0
    change I (slotCoordinateSum F (0, 1, 0, 0, 0)) = e (0, 1, ρ₁ 0, ρ₂ 0, ρ₃ 0) at hb
    simpa [slotCoordinateSum] using hb
  · apply cubic_eq_of_diagonal_eq
    intro x
    obtain ⟨⟨α, β, u, p, q⟩, rfl⟩ := f.surjective x
    rw [SymmetricCubic.pullback_apply]
    change h.apply (f (α, β, u, p, q)) (f (α, β, u, p, q)) (f (α, β, u, p, q)) =
      k.apply (E (f (α, β, u, p, q))) (E (f (α, β, u, p, q))) (E (f (α, β, u, p, q)))
    rw [hE]
    have hf := slotCubic_normalForm F h φ hF α β u p q
    have hg := he_cubic α β (ρ₁ u) (ρ₂ p) (ρ₃ q)
    have hi := ρ₃.inner_map_map (φ u p) q
    rw [hρ] at hi
    simp only [ρ₁.norm_map, ρ₂.norm_map, ρ₃.norm_map, hi] at hg
    change h.apply (slotCoordinateSum F (α, β, u, p, q)) (slotCoordinateSum F (α, β, u, p, q))
      (slotCoordinateSum F (α, β, u, p, q)) = _
    simpa only [slotCoordinateSum, LinearMap.coe_mk, AddHom.coe_mk, add_assoc] using hf.trans hg.symm

end

end ThirteenPlanes.Peirce
