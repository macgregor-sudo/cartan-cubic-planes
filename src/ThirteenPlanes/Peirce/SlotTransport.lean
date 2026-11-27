module

public import ThirteenPlanes.Peirce.SlotCubic

@[expose] public section

set_option backward.privateInPublic true

/-! Cubic transport along isometries that intertwine the three slot products. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

open SymmetricCubic Submodule

variable {V S₁ S₂ S₃ : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup S₁] [InnerProductSpace ℝ S₁]
  [NormedAddCommGroup S₂] [InnerProductSpace ℝ S₂]
  [NormedAddCommGroup S₃] [InnerProductSpace ℝ S₃]

variable (F : SlotCoordinates V S₁ S₂ S₃)

/-- The sum of the two marked line coordinates and the three slot coordinates. -/
def slotCoordinateSum : (ℝ × ℝ × S₁ × S₂ × S₃) →ₗ[ℝ] V where
  toFun t := t.1 • F.a + (t.2.1 • F.b + (F.first t.2.2.1 + (F.second t.2.2.2.1 + F.third t.2.2.2.2)))
  map_add' t w := by simp only [Prod.fst_add, Prod.snd_add, add_smul, map_add]; abel
  map_smul' r t := by
    rcases t with ⟨α, β, u, p, q⟩
    change (r * α) • F.a + ((r * β) • F.b +
      (F.first (r • u) + (F.second (r • p) + F.third (r • q)))) =
      r • (α • F.a + (β • F.b + (F.first u + (F.second p + F.third q))))
    simp only [map_smul, smul_add, smul_smul]

theorem slotCoordinateSum_norm_sq (α β : ℝ) (u : S₁) (p : S₂) (q : S₃) :
    ‖slotCoordinateSum F (α, β, u, p, q)‖ ^ 2 =
      α ^ 2 + β ^ 2 + ‖u‖ ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  let y := F.second p + F.third q
  let z := F.first u + y
  let w := β • F.b + z
  have h₁ : F.first u ∈ F.first.toLinearMap.range := ⟨u, rfl⟩
  have h₂ : F.second p ∈ F.second.toLinearMap.range := ⟨p, rfl⟩
  have h₃ : F.third q ∈ F.third.toLinearMap.range := ⟨q, rfl⟩
  have ha : F.a ∈ ℝ ∙ F.a := mem_span_singleton_self _
  have hb : F.b ∈ ℝ ∙ F.b := mem_span_singleton_self _
  have hy : y ∈ F.halfSpan := mem_sup.mpr ⟨_, h₂, _, h₃, rfl⟩
  have hz : z ∈ F.first.toLinearMap.range ⊔ F.halfSpan := mem_sup.mpr ⟨_, h₁, _, hy, rfl⟩
  have hw : w ∈ F.minusSpan ⊔ F.halfSpan := by
    have hm : β • F.b + F.first u ∈ F.minusSpan :=
      mem_sup.mpr ⟨_, (ℝ ∙ F.b).smul_mem β hb, _, h₁, rfl⟩
    exact mem_sup.mpr ⟨_, hm, _, hy, add_assoc _ _ _⟩
  have hNy : ‖y‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    change ‖F.second p + F.third q‖ ^ 2 = _
    rw [norm_add_sq_real, F.second_perp.inner_eq h₂ h₃, F.second.norm_map, F.third.norm_map]
    ring
  have hNz : ‖z‖ ^ 2 = ‖u‖ ^ 2 + (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
    change ‖F.first u + y‖ ^ 2 = _
    rw [norm_add_sq_real, F.first_perp.inner_eq h₁ hy, F.first.norm_map, hNy]
    ring
  have hNw : ‖w‖ ^ 2 = β ^ 2 + (‖u‖ ^ 2 + (‖p‖ ^ 2 + ‖q‖ ^ 2)) := by
    change ‖β • F.b + z‖ ^ 2 = _
    rw [norm_add_sq_real, real_inner_smul_left, F.b_perp.inner_eq hb hz, norm_smul,
      Real.norm_eq_abs, F.b_unit, mul_one, sq_abs, hNz]
    ring
  change ‖α • F.a + w‖ ^ 2 = _
  rw [norm_add_sq_real, real_inner_smul_left, F.a_perp.inner_eq ha hw, norm_smul,
    Real.norm_eq_abs, F.a_unit, mul_one, sq_abs, hNw]
  ring

private theorem slotCoordinateSum_bijective : Function.Bijective (slotCoordinateSum F) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    rintro ⟨α, β, u, p, q⟩ hx
    have h := slotCoordinateSum_norm_sq F α β u p q
    rw [hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    have nα : 0 ≤ α ^ 2 := sq_nonneg _
    have nβ : 0 ≤ β ^ 2 := sq_nonneg _
    have nu : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
    have np : 0 ≤ ‖p‖ ^ 2 := sq_nonneg _
    have nq : 0 ≤ ‖q‖ ^ 2 := sq_nonneg _
    have hz : α ^ 2 = 0 ∧ β ^ 2 = 0 ∧ ‖u‖ ^ 2 = 0 ∧ ‖p‖ ^ 2 = 0 ∧ ‖q‖ ^ 2 = 0 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [h, nα, nβ, nu, np, nq]
    obtain ⟨hα, hβ, hu, hp, hq⟩ := hz
    have square_zero {x : ℝ} (hx : x ^ 2 = 0) : x = 0 :=
      mul_self_eq_zero.mp (by simpa only [pow_two] using hx)
    rw [square_zero hα, square_zero hβ, norm_eq_zero.mp (square_zero hu),
      norm_eq_zero.mp (square_zero hp), norm_eq_zero.mp (square_zero hq)]
    rfl
  · intro x
    have hx : x ∈ (ℝ ∙ F.a) ⊔ (F.minusSpan ⊔ F.halfSpan) := by rw [F.exhaustive]; trivial
    obtain ⟨xₐ, hxₐ, y, hy, rfl⟩ := mem_sup.mp hx
    obtain ⟨v, hv, w, hw, rfl⟩ := mem_sup.mp hy
    obtain ⟨xᵦ, hxᵦ, u, hu, rfl⟩ := mem_sup.mp hv
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup.mp hw
    obtain ⟨α, rfl⟩ := mem_span_singleton.mp hxₐ
    obtain ⟨β, rfl⟩ := mem_span_singleton.mp hxᵦ
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hu
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hp
    obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp hq
    refine ⟨(α, β, u, p, q), ?_⟩
    change α • F.a + (β • F.b + (F.first u + (F.second p + F.third q))) = _
    abel

/-- Uniqueness and existence of the five coordinates as a real linear equivalence. -/
def slotCoordinateEquiv : (ℝ × ℝ × S₁ × S₂ × S₃) ≃ₗ[ℝ] V :=
  LinearEquiv.ofBijective (slotCoordinateSum F) (slotCoordinateSum_bijective F)

private theorem diagonal_polarization (h : SymmetricCubic V) (x y z : V) :
    6 * h.apply x y z =
      h.apply (x + y + z) (x + y + z) (x + y + z) -
      h.apply (x + y) (x + y) (x + y) - h.apply (x + z) (x + z) (x + z) -
      h.apply (y + z) (y + z) (y + z) + h.apply x x x + h.apply y y y + h.apply z z z := by
  have h₁₃₂ := h.apply_swap₂₃ x z y
  have h₂₁₃ := h.apply_swap₁₂ y x z
  have h₂₃₁ := (h.apply_swap₂₃ y z x).trans h₂₁₃
  have h₃₁₂ := (h.apply_swap₁₂ z x y).trans h₁₃₂
  have h₃₂₁ := (h.apply_swap₁₂ z y x).trans h₂₃₁
  simp only [apply_add₁, apply_add₂, apply_add₃, h₁₃₂, h₂₁₃, h₂₃₁, h₃₁₂, h₃₂₁]
  ring

/-- The diagonal determines the entire metric symmetric cubic. -/
theorem cubic_eq_of_diagonal_eq {f g : SymmetricCubic V}
    (he : ∀ x : V, f.apply x x x = g.apply x x x) : f = g := by
  apply SymmetricCubic.ext
  intro x y z
  have hf := diagonal_polarization f x y z
  have hg := diagonal_polarization g x y z
  rw [he, he, he, he, he, he, he] at hf
  linarith only [hf, hg]

variable {W T₁ T₂ T₃ : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup T₁] [InnerProductSpace ℝ T₁]
  [NormedAddCommGroup T₂] [InnerProductSpace ℝ T₂]
  [NormedAddCommGroup T₃] [InnerProductSpace ℝ T₃]

/-- Intertwining the slot products transports the whole cubics by an onto isometry
carrying both marked vectors to their counterparts. -/
theorem slotCubic_isometry [FiniteDimensional ℝ V] (G : SlotCoordinates W T₁ T₂ T₃)
    (h : SymmetricCubic V) (k : SymmetricCubic W)
    (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃) (ψ : T₁ →ₗ[ℝ] T₂ →ₗ[ℝ] T₃)
    (hF : SlotNormalConditions F h φ) (hG : SlotNormalConditions G k ψ)
    (ρ₁ : S₁ ≃ₗᵢ[ℝ] T₁) (ρ₂ : S₂ ≃ₗᵢ[ℝ] T₂) (ρ₃ : S₃ ≃ₗᵢ[ℝ] T₃)
    (hρ : ∀ u p, ρ₃ (φ u p) = ψ (ρ₁ u) (ρ₂ p)) :
    ∃ E : V ≃ₗᵢ[ℝ] W, E F.a = G.a ∧ E F.b = G.b ∧
      h = k.pullback E.toLinearMap := by
  let f := slotCoordinateEquiv F
  let g := slotCoordinateEquiv G
  let R := (LinearEquiv.refl ℝ ℝ).prodCongr ((LinearEquiv.refl ℝ ℝ).prodCongr
    (ρ₁.toLinearEquiv.prodCongr (ρ₂.toLinearEquiv.prodCongr ρ₃.toLinearEquiv)))
  let E := f.symm.trans (R.trans g)
  have hE (α β : ℝ) (u : S₁) (p : S₂) (q : S₃) :
       E (f (α, β, u, p, q)) = g (α, β, ρ₁ u, ρ₂ p, ρ₃ q) := by
    simp [E, R]
  have hnorm (x : V) : ‖E x‖ = ‖x‖ := by
    obtain ⟨⟨α, β, u, p, q⟩, rfl⟩ := f.surjective x
    have he : ‖E (f (α, β, u, p, q))‖ ^ 2 = ‖f (α, β, u, p, q)‖ ^ 2 := by
      rw [hE]
      change ‖slotCoordinateSum G (α, β, ρ₁ u, ρ₂ p, ρ₃ q)‖ ^ 2 =
        ‖slotCoordinateSum F (α, β, u, p, q)‖ ^ 2
      rw [slotCoordinateSum_norm_sq, slotCoordinateSum_norm_sq, ρ₁.norm_map, ρ₂.norm_map,
        ρ₃.norm_map]
    have hh := (sq_eq_sq_iff_abs_eq_abs _ _).mp he
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hh
  let I : V ≃ₗᵢ[ℝ] W := ⟨E, hnorm⟩
  refine ⟨I, ?_, ?_, ?_⟩
  · have ha := hE 1 0 0 0 0
    change I (slotCoordinateSum F (1, 0, 0, 0, 0)) = slotCoordinateSum G (1, 0, ρ₁ 0, ρ₂ 0, ρ₃ 0) at ha
    simpa [slotCoordinateSum] using ha
  · have hb := hE 0 1 0 0 0
    change I (slotCoordinateSum F (0, 1, 0, 0, 0)) = slotCoordinateSum G (0, 1, ρ₁ 0, ρ₂ 0, ρ₃ 0) at hb
    simpa [slotCoordinateSum] using hb
  · apply cubic_eq_of_diagonal_eq
    intro x
    obtain ⟨⟨α, β, u, p, q⟩, rfl⟩ := f.surjective x
    rw [SymmetricCubic.pullback_apply]
    change h.apply (f (α, β, u, p, q)) (f (α, β, u, p, q)) (f (α, β, u, p, q)) =
      k.apply (E (f (α, β, u, p, q))) (E (f (α, β, u, p, q))) (E (f (α, β, u, p, q)))
    rw [hE]
    have hf := slotCubic_normalForm F h φ hF α β u p q
    have hg := slotCubic_normalForm G k ψ hG α β (ρ₁ u) (ρ₂ p) (ρ₃ q)
    have hi := ρ₃.inner_map_map (φ u p) q
    rw [hρ] at hi
    simp only [ρ₁.norm_map, ρ₂.norm_map, ρ₃.norm_map, hi] at hg
    change h.apply (slotCoordinateSum F (α, β, u, p, q)) (slotCoordinateSum F (α, β, u, p, q))
      (slotCoordinateSum F (α, β, u, p, q)) =
      k.apply (slotCoordinateSum G (α, β, ρ₁ u, ρ₂ p, ρ₃ q))
        (slotCoordinateSum G (α, β, ρ₁ u, ρ₂ p, ρ₃ q))
        (slotCoordinateSum G (α, β, ρ₁ u, ρ₂ p, ρ₃ q))
    simpa only [slotCoordinateSum, LinearMap.coe_mk, AddHom.coe_mk, add_assoc] using hf.trans hg.symm

end

end ThirteenPlanes.Peirce
