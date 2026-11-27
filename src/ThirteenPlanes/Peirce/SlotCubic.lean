module

public import ThirteenPlanes.Peirce.Slots

@[expose] public section

set_option backward.privateInPublic true

/-! The cubic coefficients and diagonal normal form of the three Peirce slots. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

open SymmetricCubic Module.End Submodule

variable {V S₁ S₂ S₃ : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup S₁] [InnerProductSpace ℝ S₁]
  [NormedAddCommGroup S₂] [InnerProductSpace ℝ S₂]
  [NormedAddCommGroup S₃] [InnerProductSpace ℝ S₃]

/-- Two unit vectors and three isometric coordinates for an exhaustive orthogonal decomposition. -/
structure SlotCoordinates (V S₁ S₂ S₃ : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup S₁] [InnerProductSpace ℝ S₁]
    [NormedAddCommGroup S₂] [InnerProductSpace ℝ S₂]
    [NormedAddCommGroup S₃] [InnerProductSpace ℝ S₃] where
  a : V
  b : V
  first : S₁ →ₗᵢ[ℝ] V
  second : S₂ →ₗᵢ[ℝ] V
  third : S₃ →ₗᵢ[ℝ] V
  a_unit : ‖a‖ = 1
  b_unit : ‖b‖ = 1
  a_perp : (ℝ ∙ a).IsOrtho ((ℝ ∙ b) ⊔ first.toLinearMap.range ⊔
    (second.toLinearMap.range ⊔ third.toLinearMap.range))
  b_perp : (ℝ ∙ b).IsOrtho (first.toLinearMap.range ⊔
    (second.toLinearMap.range ⊔ third.toLinearMap.range))
  first_perp : first.toLinearMap.range.IsOrtho
    (second.toLinearMap.range ⊔ third.toLinearMap.range)
  second_perp : second.toLinearMap.range.IsOrtho third.toLinearMap.range
  exhaustive : (ℝ ∙ a) ⊔ (((ℝ ∙ b) ⊔ first.toLinearMap.range) ⊔
    (second.toLinearMap.range ⊔ third.toLinearMap.range)) = ⊤

variable (F : SlotCoordinates V S₁ S₂ S₃)

abbrev SlotCoordinates.minusSpan : Submodule ℝ V := (ℝ ∙ F.b) ⊔ F.first.toLinearMap.range
abbrev SlotCoordinates.halfSpan : Submodule ℝ V :=
  F.second.toLinearMap.range ⊔ F.third.toLinearMap.range

/-- Conditions (N1)–(N3) on a metric symmetric cubic and its bilinear slot product. -/
structure SlotNormalConditions (h : SymmetricCubic V) (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃) : Prop where
  idempotent : h.L F.a F.a = F.a
  minus_action : ∀ x ∈ F.minusSpan, h.L F.a x = -x
  half_action : ∀ x ∈ F.halfSpan, h.L F.a x = (1 / 2 : ℝ) • x
  minus_minus_minus : ∀ x ∈ F.minusSpan, ∀ y ∈ F.minusSpan, ∀ z ∈ F.minusSpan,
    h.apply x y z = 0
  minus_minus_half : ∀ x ∈ F.minusSpan, ∀ y ∈ F.minusSpan, ∀ z ∈ F.halfSpan,
    h.apply x y z = 0
  half_half_half : ∀ x ∈ F.halfSpan, ∀ y ∈ F.halfSpan, ∀ z ∈ F.halfSpan,
    h.apply x y z = 0
  b_second_second : ∀ y y' : S₂, h.apply F.b (F.second y) (F.second y') =
    -(Real.sqrt 3 / 2) * ⟪y, y'⟫
  b_third_third : ∀ z z' : S₃, h.apply F.b (F.third z) (F.third z') =
    (Real.sqrt 3 / 2) * ⟪z, z'⟫
  b_second_third : ∀ (y : S₂) (z : S₃), h.apply F.b (F.second y) (F.third z) = 0
  first_second_second : ∀ (u : S₁) (y y' : S₂), h.apply (F.first u) (F.second y) (F.second y') = 0
  first_third_third : ∀ (u : S₁) (z z' : S₃), h.apply (F.first u) (F.third z) (F.third z') = 0
  first_second_third : ∀ (u : S₁) (y : S₂) (z : S₃),
    h.apply (F.first u) (F.second y) (F.third z) = (Real.sqrt 3 / 2) * ⟪φ u y, z⟫

private theorem diagonal_add (h : SymmetricCubic V) (x y : V) :
    h.apply (x + y) (x + y) (x + y) =
      h.apply x x x + 3 * h.apply x x y + 3 * h.apply x y y + h.apply y y y := by
  have h₁ := h.apply_swap₂₃ x y x
  have h₂ := (h.apply_swap₁₂ y x x).trans h₁
  have h₃ := h.apply_swap₁₂ y x y
  have h₄ := (h.apply_swap₂₃ y y x).trans h₃
  simp only [apply_add₁, apply_add₂, apply_add₃, h₁, h₂, h₃, h₄]
  ring

/-- Lemma 2b-normal, for any cubic satisfying the stated slot conditions. -/
theorem slotCubic_normalForm (h : SymmetricCubic V) (φ : S₁ →ₗ[ℝ] S₂ →ₗ[ℝ] S₃)
    (H : SlotNormalConditions F h φ) (α β : ℝ) (u : S₁) (p : S₂) (q : S₃) :
    let x := α • F.a + β • F.b + F.first u + F.second p + F.third q
    h.apply x x x =
      α ^ 3 - 3 * α * (β ^ 2 + ‖u‖ ^ 2) +
      (3 / 2 : ℝ) * α * (‖p‖ ^ 2 + ‖q‖ ^ 2) +
      (3 * Real.sqrt 3 / 2) * β * (‖q‖ ^ 2 - ‖p‖ ^ 2) +
      3 * Real.sqrt 3 * ⟪φ u p, q⟫ := by
  let v := β • F.b + F.first u
  let y := F.second p + F.third q
  let z := v + y
  have hu : F.first u ∈ F.first.toLinearMap.range := ⟨u, rfl⟩
  have hp : F.second p ∈ F.second.toLinearMap.range := ⟨p, rfl⟩
  have hq : F.third q ∈ F.third.toLinearMap.range := ⟨q, rfl⟩
  have hb : F.b ∈ ℝ ∙ F.b := Submodule.mem_span_singleton_self F.b
  have ha : F.a ∈ ℝ ∙ F.a := Submodule.mem_span_singleton_self F.a
  have hv : v ∈ F.minusSpan := Submodule.mem_sup.mpr
    ⟨β • F.b, (ℝ ∙ F.b).smul_mem β hb, F.first u, hu, rfl⟩
  have hy : y ∈ F.halfSpan := Submodule.mem_sup.mpr ⟨F.second p, hp, F.third q, hq, rfl⟩
  have huperp := F.first_perp.inner_eq hu hy
  have hbperp := F.b_perp.inner_eq hb (mem_sup_right hy)
  have hvperp : ⟪v, y⟫ = 0 := by
    simp only [v, inner_add_left, real_inner_smul_left, hbperp, huperp, mul_zero, add_zero]
  have hvperp' : ⟪y, v⟫ = 0 := (real_inner_comm _ _).trans hvperp
  have hnormv : ‖v‖ ^ 2 = β ^ 2 + ‖u‖ ^ 2 := by
    rw [show v = β • F.b + F.first u from rfl, norm_add_sq_real, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, F.b_unit, F.first.norm_map,
      real_inner_smul_left, F.b_perp.inner_eq hb (mem_sup_left hu)]
    ring
  have hnormy : ‖y‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    rw [show y = F.second p + F.third q from rfl, norm_add_sq_real, F.second.norm_map,
      F.third.norm_map, F.second_perp.inner_eq hp hq]
    ring
  have hza : ⟪F.a, z⟫ = 0 := F.a_perp.inner_eq ha
    (Submodule.mem_sup.mpr ⟨v, hv, y, hy, rfl⟩)
  have haaa : h.apply F.a F.a F.a = 1 := by
    rw [apply, H.idempotent, real_inner_self_eq_norm_sq, F.a_unit, one_pow]
  have haaz : h.apply F.a F.a z = 0 := by rw [apply, H.idempotent, hza]
  have hazz : h.apply F.a z z = -(β ^ 2 + ‖u‖ ^ 2) + (1 / 2 : ℝ) * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
    change ⟪h.L F.a (v + y), v + y⟫ = _
    rw [map_add, H.minus_action v hv, H.half_action y hy]
    simp only [inner_add_left, inner_add_right, inner_neg_left, real_inner_smul_left,
      hvperp, hvperp', real_inner_self_eq_norm_sq, hnormv, hnormy]
    ring
  have hvyy : h.apply v y y =
      β * (Real.sqrt 3 / 2) * (‖q‖ ^ 2 - ‖p‖ ^ 2) +
        Real.sqrt 3 * ⟪φ u p, q⟫ := by
    simp only [v, y, apply_add₁, apply_add₂, apply_add₃, apply_smul₁,
      H.b_second_second, H.b_third_third, H.b_second_third,
      h.apply_swap₂₃ F.b (F.third q) (F.second p),
      H.first_second_second, H.first_third_third, H.first_second_third,
      h.apply_swap₂₃ (F.first u) (F.third q) (F.second p), real_inner_self_eq_norm_sq]
    ring
  have hzzz : h.apply z z z = 3 * h.apply v y y := by
    rw [show z = v + y from rfl, diagonal_add, H.minus_minus_minus v hv v hv v hv,
      H.minus_minus_half v hv v hv y hy, H.half_half_half y hy y hy y hy]
    ring
  let w := α • F.a + z
  have hW : h.apply w w w =
      α ^ 3 - 3 * α * (β ^ 2 + ‖u‖ ^ 2) +
      (3 / 2 : ℝ) * α * (‖p‖ ^ 2 + ‖q‖ ^ 2) +
      (3 * Real.sqrt 3 / 2) * β * (‖q‖ ^ 2 - ‖p‖ ^ 2) +
      3 * Real.sqrt 3 * ⟪φ u p, q⟫ := by
    rw [show w = α • F.a + z from rfl, diagonal_add]
    simp only [apply_smul₁, apply_smul₂, apply_smul₃, haaa, haaz, hazz, hzzz, hvyy]
    ring
  simpa only [w, z, v, y, add_assoc] using hW


section RoundSlots

variable {h : SymmetricCubic V} {a : V}
variable (round : IsRound h 1) (ha : IsUnitIdempotent h a) {b : minusSpace h a}

private theorem range_subtype_comp (U : Submodule ℝ V) (W : Submodule ℝ U) :
    (U.subtypeₗᵢ.comp W.subtypeₗᵢ).toLinearMap.range = W.map U.subtype := by
  change (U.subtype.comp W.subtype).range = _
  rw [LinearMap.range_comp, Submodule.range_subtype]

private theorem ambient_half_eq (hb : ‖b‖ = 1) :
    slotTwoAmbient round ha b ⊔ slotThreeAmbient round ha b = halfSpace h a := by
  change ((slotTwo round ha b).map (halfSpace h a).subtype ⊔
    (slotThree round ha b).map (halfSpace h a).subtype) = _
  rw [← Submodule.map_sup, slotTwo_slotThree_sup round ha hb, Submodule.map_top,
    Submodule.range_subtype]

/-- The coordinates furnished by the actual round Peirce slots. -/
def roundSlotCoordinates (hb : ‖b‖ = 1) :
    SlotCoordinates V (slotOne b) (slotTwo round ha b) (slotThree round ha b) := by
  have hs := spectralSplit round ha
  have hhalf := ambient_half_eq round ha hb
  have hminus := line_slotOne_sup hb
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := slots_orthogonal round ha (b := b)
  have hbline : (ℝ ∙ (b : V)) ≤ minusSpace h a := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain rfl : v = (b : V) := Set.mem_singleton_iff.mp hv
    exact b.property
  let i₁ := (slotOne b).subtypeₗᵢ
  let i₂ := (halfSpace h a).subtypeₗᵢ.comp (slotTwo round ha b).subtypeₗᵢ
  let i₃ := (halfSpace h a).subtypeₗᵢ.comp (slotThree round ha b).subtypeₗᵢ
  have hr₁ : i₁.toLinearMap.range = slotOne b := Submodule.range_subtype _
  have hr₂ : i₂.toLinearMap.range = slotTwoAmbient round ha b := range_subtype_comp _ _
  have hr₃ : i₃.toLinearMap.range = slotThreeAmbient round ha b := range_subtype_comp _ _
  refine ⟨a, b, i₁, i₂, i₃, ha.norm_eq_one, hb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr₁, hr₂, hr₃, hminus, hhalf, Submodule.isOrtho_sup_right]
    exact ⟨hs.minus_perp, hs.half_perp⟩
  · rw [hr₁, hr₂, hr₃, hhalf, Submodule.isOrtho_sup_right]
    exact ⟨(Submodule.isOrtho_iff_le.mpr inf_le_right).symm, hs.minus_half_perp.mono_left hbline⟩
  · rw [hr₁, hr₂, hr₃, Submodule.isOrtho_sup_right]
    exact ⟨h₁₂, h₁₃⟩
  · rwa [hr₂, hr₃]
  · rw [hr₁, hr₂, hr₃, hminus, hhalf, hs.full_split]

theorem roundSlotCoordinates_minusSpan (hb : ‖b‖ = 1) :
    (roundSlotCoordinates round ha hb).minusSpan = minusSpace h a := by
  change (ℝ ∙ (b : V)) ⊔ (slotOne b).subtype.range = _
  rw [Submodule.range_subtype, line_slotOne_sup hb]

theorem roundSlotCoordinates_halfSpan (hb : ‖b‖ = 1) :
    (roundSlotCoordinates round ha hb).halfSpan = halfSpace h a := by
  change ((halfSpace h a).subtypeₗᵢ.comp (slotTwo round ha b).subtypeₗᵢ).toLinearMap.range ⊔
    ((halfSpace h a).subtypeₗᵢ.comp (slotThree round ha b).subtypeₗᵢ).toLinearMap.range = _
  rw [range_subtype_comp, range_subtype_comp]
  exact ambient_half_eq round ha hb

/-- All the polarized conditions (N1)–(N3) for the actual round Peirce slots. -/
theorem roundSlot_normalConditions (hb : ‖b‖ = 1) :
    SlotNormalConditions (roundSlotCoordinates round ha hb) h (slotProduct round ha (b := b)) := by
  let R := roundSlotCoordinates round ha hb
  have hm : R.minusSpan = minusSpace h a := roundSlotCoordinates_minusSpan round ha hb
  have hp : R.halfSpan = halfSpace h a := roundSlotCoordinates_halfSpan round ha hb
  obtain ⟨_, _, h₂₃⟩ := slots_orthogonal round ha (b := b)
  have mem₂ (y : slotTwo round ha b) : ((y : halfSpace h a) : V) ∈ slotTwoAmbient round ha b :=
    Submodule.mem_map_of_mem y.property
  have mem₃ (z : slotThree round ha b) : ((z : halfSpace h a) : V) ∈ slotThreeAmbient round ha b :=
    Submodule.mem_map_of_mem z.property
  change SlotNormalConditions R h (slotProduct round ha (b := b))
  refine ⟨ha.square_eq_self, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hm] at hx
    change h.L a x = -x
    simpa using mem_eigenspace_iff.mp hx
  · intro x hx
    rw [hp] at hx
    exact mem_eigenspace_iff.mp hx
  · intro x hx y hy z hz
    rw [hm] at hx hy hz
    exact cubic_vanishes_of_eigenvalue_sum round ha (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx hy hz
  · intro x hx y hy z hz
    rw [hm] at hx hy
    rw [hp] at hz
    exact cubic_vanishes_of_eigenvalue_sum round ha (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx hy hz
  · intro x hx y hy z hz
    rw [hp] at hx hy hz
    exact cubic_vanishes_of_eigenvalue_sum round ha (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx hy hz
  · intro y y'
    change ⟪h.L (b : V) ((y : halfSpace h a) : V), ((y' : halfSpace h a) : V)⟫ = _
    rw [(slotTwo_actions round ha y.property).2, real_inner_smul_left]
    rfl
  · intro z z'
    change ⟪h.L (b : V) ((z : halfSpace h a) : V), ((z' : halfSpace h a) : V)⟫ = _
    rw [(slotThree_actions round ha z.property).2, real_inner_smul_left]
    rfl
  · intro y z
    change ⟪h.L (b : V) ((y : halfSpace h a) : V), ((z : halfSpace h a) : V)⟫ = 0
    rw [(slotTwo_actions round ha y.property).2, real_inner_smul_left, h₂₃.inner_eq (mem₂ y) (mem₃ z),
      mul_zero]
  · intro u y y'
    exact h₂₃.symm.inner_eq (slotOne_mul_slotTwo round ha u y) (mem₂ y')
  · intro u z z'
    exact h₂₃.inner_eq (slotOne_mul_slotThree round ha u z) (mem₃ z')
  · intro u y z
    have he := congrArg (fun x : V => ⟪x, ((z : halfSpace h a) : V)⟫)
      (slotProduct_apply_coe round ha u y)
    rw [real_inner_smul_left] at he
    change ⟪slotProduct round ha u y, z⟫ = (2 / Real.sqrt 3) *
      h.apply (R.first u) (R.second y) (R.third z) at he
    rw [he, ← mul_assoc]
    have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hscale : (Real.sqrt 3 / 2 : ℝ) * (2 / Real.sqrt 3) = 1 := by field_simp
    rw [hscale, one_mul]

/-- Lemma 2b-abstract, including the full cubic on the actual marked slots. -/
theorem roundSlot_normalForm (hb : ‖b‖ = 1) :
    let R := roundSlotCoordinates round ha hb
    let φ := slotProduct round ha (b := b)
    SlotNormalConditions R h φ ∧
    ∀ (α β : ℝ) (u : slotOne b) (p : slotTwo round ha b) (q : slotThree round ha b),
      let x := α • a + β • (b : V) + R.first u + R.second p + R.third q
      h.apply x x x =
        α ^ 3 - 3 * α * (β ^ 2 + ‖u‖ ^ 2) +
        (3 / 2 : ℝ) * α * (‖p‖ ^ 2 + ‖q‖ ^ 2) +
        (3 * Real.sqrt 3 / 2) * β * (‖q‖ ^ 2 - ‖p‖ ^ 2) +
        3 * Real.sqrt 3 * ⟪φ u p, q⟫ := by
  refine ⟨roundSlot_normalConditions round ha hb, ?_⟩
  intro α β u p q
  exact slotCubic_normalForm _ h _ (roundSlot_normalConditions round ha hb) α β u p q

end RoundSlots

end

end ThirteenPlanes.Peirce
