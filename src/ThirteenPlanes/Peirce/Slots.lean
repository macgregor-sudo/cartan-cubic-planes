module

public import ThirteenPlanes.Peirce.Clifford
public import ThirteenPlanes.PeirceDimensions

@[expose] public section

set_option backward.privateInPublic true

/-! The three Peirce slots at a unit idempotent and a unit minus field. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

open Module.End Submodule SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {h : SymmetricCubic V} {a : V}
variable (round : IsRound h 1) (ha : IsUnitIdempotent h a)

/-- The perpendicular complement of the marked minus field inside the minus space. -/
abbrev slotOne (b : minusSpace h a) : Submodule ℝ V :=
  minusSpace h a ⊓ (ℝ ∙ (b : V))ᗮ

/-- The minus-one eigenspace of the marked scaled action on the half space. -/
abbrev slotTwo (b : minusSpace h a) : Submodule ℝ (halfSpace h a) :=
  eigenspace (scaledHalfAction round ha b) (-1)

/-- The plus-one eigenspace of the marked scaled action on the half space. -/
abbrev slotThree (b : minusSpace h a) : Submodule ℝ (halfSpace h a) :=
  eigenspace (scaledHalfAction round ha b) 1

/-- The second slot viewed as a subspace of the ambient fields. -/
abbrev slotTwoAmbient (b : minusSpace h a) : Submodule ℝ V :=
  (slotTwo round ha b).map (halfSpace h a).subtype

/-- The third slot viewed as a subspace of the ambient fields. -/
abbrev slotThreeAmbient (b : minusSpace h a) : Submodule ℝ V :=
  (slotThree round ha b).map (halfSpace h a).subtype

variable {b : minusSpace h a}

private theorem line_le_minus : (ℝ ∙ (b : V)) ≤ minusSpace h a := by
  apply Submodule.span_le.mpr
  intro v hv
  obtain rfl : v = (b : V) := Set.mem_singleton_iff.mp hv
  exact b.property

/-- The marked minus field and its perpendicular slot span the minus space. -/
theorem line_slotOne_sup (hb : ‖b‖ = 1) :
    (ℝ ∙ (b : V)) ⊔ slotOne b = minusSpace h a := by
  apply le_antisymm (sup_le line_le_minus inf_le_left)
  intro y hy
  let p : V := ⟪y, (b : V)⟫ • (b : V)
  have hp : p ∈ ℝ ∙ (b : V) := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hperp : y - p ∈ (ℝ ∙ (b : V))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    have hb' : ‖(b : V)‖ = 1 := hb
    rw [hb']
    ring
  exact Submodule.mem_sup.mpr ⟨p, hp, y - p,
    ⟨(minusSpace h a).sub_mem hy (line_le_minus hp), hperp⟩, by abel⟩

theorem marked_action_involution (hb : ‖b‖ = 1) :
    (scaledHalfAction round ha b) ^ 2 = 1 := by
  rw [scaledHalfAction_square round ha b, hb, one_pow, one_smul]

/-- The two eigenspaces of the marked action exhaust the half space. -/
theorem slotTwo_slotThree_sup (hb : ‖b‖ = 1) :
    slotTwo round ha b ⊔ slotThree round ha b = ⊤ := by
  apply eq_top_iff.mpr
  intro y _
  let B := scaledHalfAction round ha b
  have hB : B (B y) = y := by
    have he := congrArg (fun T : Module.End ℝ (halfSpace h a) => T y)
      (marked_action_involution round ha hb)
    rw [pow_two] at he
    exact he
  let y₂ := (1 / 2 : ℝ) • (y - B y)
  let y₃ := (1 / 2 : ℝ) • (y + B y)
  have h₂ : y₂ ∈ slotTwo round ha b := by
    apply mem_eigenspace_iff.mpr
    change B y₂ = (-1 : ℝ) • y₂
    simp only [y₂, map_smul, map_sub, hB]
    module
  have h₃ : y₃ ∈ slotThree round ha b := by
    apply mem_eigenspace_iff.mpr
    change B y₃ = (1 : ℝ) • y₃
    simp only [y₃, map_smul, map_add, hB]
    module
  exact Submodule.mem_sup.mpr ⟨y₂, h₂, y₃, h₃, by dsimp [y₂, y₃]; module⟩

theorem slotTwo_slotThree_orthogonal :
    (slotTwo round ha b).IsOrtho (slotThree round ha b) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx y hy
  have h := scaledHalfAction_isSymmetric round ha b x y
  rw [mem_eigenspace_iff.mp hx, mem_eigenspace_iff.mp hy,
    real_inner_smul_left, real_inner_smul_right] at h
  linarith

/-- The three ambient slots span precisely the perpendicular space of the marked plane. -/
theorem slots_span_perp (hb : ‖b‖ = 1) :
    slotOne b ⊔ (slotTwoAmbient round ha b ⊔ slotThreeAmbient round ha b) =
      ((ℝ ∙ a) ⊔ (ℝ ∙ (b : V)))ᗮ := by
  have hs := spectralSplit round ha
  have hHalf : slotTwoAmbient round ha b ⊔ slotThreeAmbient round ha b = halfSpace h a := by
    change (slotTwo round ha b).map (halfSpace h a).subtype ⊔
      (slotThree round ha b).map (halfSpace h a).subtype = halfSpace h a
    rw [← Submodule.map_sup, slotTwo_slotThree_sup round ha hb, Submodule.map_top,
      Submodule.range_subtype]
  have hbperp : halfSpace h a ≤ (ℝ ∙ (b : V))ᗮ := by
    intro y hy
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      (hs.minus_half_perp.inner_eq b.property hy)
  rw [hHalf, ← Submodule.inf_orthogonal, ← hs.perp_split]
  apply le_antisymm
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right) (le_inf le_sup_right hbperp)
  · intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy.1
    have huperp : u ∈ (ℝ ∙ (b : V))ᗮ := by
      simpa using ((ℝ ∙ (b : V))ᗮ).sub_mem hy.2 (hbperp hv)
    exact Submodule.mem_sup.mpr ⟨u, ⟨hu, huperp⟩, v, hv, rfl⟩

/-- Pairwise orthogonality of the three ambient slots. -/
theorem slots_orthogonal :
    (slotOne b).IsOrtho (slotTwoAmbient round ha b) ∧
    (slotOne b).IsOrtho (slotThreeAmbient round ha b) ∧
    (slotTwoAmbient round ha b).IsOrtho (slotThreeAmbient round ha b) := by
  have hm := (spectralSplit round ha).minus_half_perp
  have hOne (S : Submodule ℝ (halfSpace h a)) :
      (slotOne b).IsOrtho (S.map (halfSpace h a).subtype) := by
    rw [Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    obtain ⟨z, _, rfl⟩ := Submodule.mem_map.mp hy
    exact hm.inner_eq hx.1 z.property
  refine ⟨hOne _, hOne _, ?_⟩
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx y hy
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
  exact (slotTwo_slotThree_orthogonal round ha).inner_eq hu hv

include round ha in
/-- The two original multiplication operators on the first slot. -/
theorem slotOne_actions {u : V} (hu : u ∈ slotOne b) :
    h.L a u = -u ∧ h.L (b : V) u = 0 := by
  refine ⟨by simpa using mem_eigenspace_iff.mp hu.1, ?_⟩
  rw [minus_mul_minus round ha b.property hu.1,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hu.2, neg_zero, zero_smul]

private theorem restore_scale (u : minusSpace h a) (y : halfSpace h a) :
    h.L (u : V) (y : V) = (Real.sqrt 3 / 2) • (scaledHalfAction round ha u y : V) := by
  rw [scaledHalfAction_apply_coe, smul_smul]
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hscale : (Real.sqrt 3 / 2 : ℝ) * (2 / Real.sqrt 3) = 1 := by
    field_simp
  rw [hscale, one_smul]

/-- The two original multiplication operators on the second slot. -/
theorem slotTwo_actions {y : halfSpace h a} (hy : y ∈ slotTwo round ha b) :
    h.L a (y : V) = (1 / 2 : ℝ) • (y : V) ∧
      h.L (b : V) (y : V) = (-(Real.sqrt 3 / 2)) • (y : V) := by
  refine ⟨mem_eigenspace_iff.mp y.property, ?_⟩
  have hB := congrArg Subtype.val (mem_eigenspace_iff.mp hy)
  change (scaledHalfAction round ha b y : V) = (-1 : ℝ) • (y : V) at hB
  rw [restore_scale round ha b y, hB, smul_smul]
  module

/-- The two original multiplication operators on the third slot. -/
theorem slotThree_actions {y : halfSpace h a} (hy : y ∈ slotThree round ha b) :
    h.L a (y : V) = (1 / 2 : ℝ) • (y : V) ∧
      h.L (b : V) (y : V) = (Real.sqrt 3 / 2) • (y : V) := by
  refine ⟨mem_eigenspace_iff.mp y.property, ?_⟩
  have hB := congrArg Subtype.val (mem_eigenspace_iff.mp hy)
  change (scaledHalfAction round ha b y : V) = (1 : ℝ) • (y : V) at hB
  rw [restore_scale round ha b y, hB, one_smul]


include round ha in
/-- The two multiplication operators commute on the perpendicular space of the marked plane. -/
theorem slots_commute (hb : ‖b‖ = 1) {x : V}
    (hx : x ∈ ((ℝ ∙ a) ⊔ (ℝ ∙ (b : V)))ᗮ) :
    h.L a (h.L (b : V) x) = h.L (b : V) (h.L a x) := by
  rw [← slots_span_perp round ha hb] at hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨y₂, hy₂, rfl⟩ := Submodule.mem_map.mp hy
  obtain ⟨y₃, hy₃, rfl⟩ := Submodule.mem_map.mp hz
  change h.L a (h.L (b : V) (u + ((y₂ : V) + (y₃ : V)))) =
    h.L (b : V) (h.L a (u + ((y₂ : V) + (y₃ : V))))
  obtain ⟨ha₁, hb₁⟩ := slotOne_actions round ha hu
  obtain ⟨ha₂, hb₂⟩ := slotTwo_actions round ha hy₂
  obtain ⟨ha₃, hb₃⟩ := slotThree_actions round ha hy₃
  simp only [map_add, ha₁, hb₁, ha₂, hb₂, ha₃, hb₃, map_smul, map_zero, map_neg]
  module

private def slotOneToMinus : slotOne b →ₗ[ℝ] minusSpace h a := Submodule.inclusion inf_le_left

private theorem scaled_exchange (u : slotOne b) {r : ℝ} {y : halfSpace h a}
    (hy : y ∈ eigenspace (scaledHalfAction round ha b) r) :
    scaledHalfAction round ha (slotOneToMinus u) y ∈ eigenspace (scaledHalfAction round ha b) (-r) := by
  let B := scaledHalfAction round ha
  let v := slotOneToMinus u
  have ho : ⟪b, v⟫ = 0 := by
    change ⟪(b : V), (u : V)⟫ = 0
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp u.property.2
  have hc := congrArg (fun T : Module.End ℝ (halfSpace h a) => T y)
    (scaledHalfAction_clifford round ha b v)
  rw [ho, mul_zero, zero_smul] at hc
  change B b (B v y) + B v (B b y) = 0 at hc
  rw [mem_eigenspace_iff.mp hy, map_smul] at hc
  apply mem_eigenspace_iff.mpr
  change B b (B v y) = (-r) • B v y
  rw [neg_smul]
  exact eq_neg_iff_add_eq_zero.mpr hc

private theorem scaledHalfAction_slotTwo (u : slotOne b) {y : halfSpace h a}
    (hy : y ∈ slotTwo round ha b) :
    scaledHalfAction round ha (slotOneToMinus u) y ∈ slotThree round ha b := by
  simpa only [neg_neg] using scaled_exchange round ha u hy

private theorem scaledHalfAction_slotThree (u : slotOne b) {y : halfSpace h a}
    (hy : y ∈ slotThree round ha b) :
    scaledHalfAction round ha (slotOneToMinus u) y ∈ slotTwo round ha b :=
  scaled_exchange round ha u hy

/-- The unscaled multiplication by a first-slot field sends the second slot into the third. -/
theorem slotOne_mul_slotTwo (u : slotOne b) (y : slotTwo round ha b) :
    h.L (u : V) ((y : halfSpace h a) : V) ∈ slotThreeAmbient round ha b := by
  change h.L (slotOneToMinus u : V) ((y : halfSpace h a) : V) ∈ slotThreeAmbient round ha b
  rw [restore_scale round ha (slotOneToMinus u) (y : halfSpace h a)]
  exact (slotThreeAmbient round ha b).smul_mem _ (Submodule.mem_map_of_mem
    (scaledHalfAction_slotTwo round ha u y.property))

/-- The unscaled multiplication by a first-slot field sends the third slot into the second. -/
theorem slotOne_mul_slotThree (u : slotOne b) (y : slotThree round ha b) :
    h.L (u : V) ((y : halfSpace h a) : V) ∈ slotTwoAmbient round ha b := by
  change h.L (slotOneToMinus u : V) ((y : halfSpace h a) : V) ∈ slotTwoAmbient round ha b
  rw [restore_scale round ha (slotOneToMinus u) (y : halfSpace h a)]
  exact (slotTwoAmbient round ha b).smul_mem _ (Submodule.mem_map_of_mem
    (scaledHalfAction_slotThree round ha u y.property))

/-- The genuine bilinear slot product, scaled by `2/√3`. -/
def slotProduct : slotOne b →ₗ[ℝ] slotTwo round ha b →ₗ[ℝ] slotThree round ha b :=
  let B := (scaledHalfAction round ha).comp (slotOneToMinus (b := b))
  LinearMap.mk₂ ℝ
    (fun u y => ⟨B u (y : halfSpace h a), scaledHalfAction_slotTwo round ha u y.property⟩)
    (by intro u v y; apply Subtype.ext; exact LinearMap.congr_fun (B.map_add u v) y)
    (by intro r u y; apply Subtype.ext; exact LinearMap.congr_fun (B.map_smul r u) y)
    (by intro u y z; apply Subtype.ext; exact (B u).map_add (y : halfSpace h a) z)
    (by intro r u y; apply Subtype.ext; exact (B u).map_smul r (y : halfSpace h a))

@[simp] theorem slotProduct_apply_coe (u : slotOne b) (y : slotTwo round ha b) :
    ((slotProduct round ha u y : halfSpace h a) : V) =
      (2 / Real.sqrt 3 : ℝ) • h.L (u : V) ((y : halfSpace h a) : V) := rfl

theorem slotProduct_norm (u : slotOne b) (y : slotTwo round ha b) :
    ‖slotProduct round ha u y‖ = ‖u‖ * ‖y‖ :=
  scaledHalfAction_norm round ha (slotOneToMinus u) (y : halfSpace h a)


include ha in
private theorem marked_product_formula (hab : h.L a (b : V) = -(b : V))
    (hbb : h.L (b : V) (b : V) = -a) (α β γ δ : ℝ) :
    h.L (α • a + β • (b : V)) (γ • a + δ • (b : V)) =
      (α * γ - β * δ) • a - (α * δ + β * γ) • (b : V) := by
  have hba := (h.L_comm (b : V) a).trans hab
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    ha.square_eq_self, hab, hba, hbb]
  module

include round ha in
/-- Lemma 2b-slots (i). The marked plane is closed and has the binary cubic normal form. -/
theorem markedPlane_normalForm (hb : ‖b‖ = 1) :
    h.L a (b : V) = -(b : V) ∧ h.L (b : V) (b : V) = -a ∧
      IsClosedPiece h ((ℝ ∙ a) ⊔ (ℝ ∙ (b : V))) ∧
      Module.finrank ℝ ↥((ℝ ∙ a) ⊔ (ℝ ∙ (b : V))) = 2 ∧
      ∀ α β : ℝ, h.apply (α • a + β • (b : V)) (α • a + β • (b : V))
        (α • a + β • (b : V)) = α ^ 3 - 3 * α * β ^ 2 := by
  have hab : h.L a (b : V) = -(b : V) := by
    simpa using mem_eigenspace_iff.mp b.property
  have hb' : ‖(b : V)‖ = 1 := hb
  have hbb : h.L (b : V) (b : V) = -a := by
    rw [minus_mul_minus round ha b.property b.property, real_inner_self_eq_norm_sq, hb']
    norm_num
  have hortho := (spectralSplit round ha).minus_perp
  have hl : (ℝ ∙ a).IsOrtho (ℝ ∙ (b : V)) := hortho.mono_right line_le_minus
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ a) (ℝ ∙ (b : V))
  have ha0 : a ≠ 0 := by
    intro hz
    have hn := ha.norm_eq_one
    simp [hz] at hn
  have hb0 : (b : V) ≠ 0 := by
    intro hz
    simp [hz] at hb'
  rw [hl.disjoint.eq_bot, finrank_bot, add_zero, finrank_span_singleton ha0,
    finrank_span_singleton hb0] at hdim
  refine ⟨hab, hbb, ?_, hdim, ?_⟩
  · intro u v hu hv
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hu₂
    obtain ⟨γ, rfl⟩ := Submodule.mem_span_singleton.mp hv₁
    obtain ⟨δ, rfl⟩ := Submodule.mem_span_singleton.mp hv₂
    rw [marked_product_formula ha hab hbb]
    let W : Submodule ℝ V := (ℝ ∙ a) ⊔ (ℝ ∙ (b : V))
    exact W.sub_mem (W.smul_mem _ (mem_sup_left (mem_span_singleton_self a)))
      (W.smul_mem _ (mem_sup_right (mem_span_singleton_self (b : V))))
  · intro α β
    change ⟪h.L (α • a + β • (b : V)) (α • a + β • (b : V)),
      α • a + β • (b : V)⟫ = _
    have hz := hortho.inner_eq (mem_span_singleton_self a) b.property
    have hz' : ⟪(b : V), a⟫ = 0 := (real_inner_comm _ _).trans hz
    rw [marked_product_formula ha hab hbb]
    simp only [inner_sub_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, ha.norm_eq_one, hb', hz, hz', one_pow]
    ring

variable [FiniteDimensional ℝ V]

include round ha in
/-- With trace zero the first slot has exactly one dimension fewer than the minus space. -/
theorem slotOne_finrank (hb : ‖b‖ = 1) (hz : LinearMap.trace ℝ V (h.L a) = 0) :
    Module.finrank ℝ (slotOne b) = (Module.finrank ℝ V - 2) / 3 := by
  have hb' : ‖(b : V)‖ = 1 := hb
  have hb0 : (b : V) ≠ 0 := by
    intro h
    simp [h] at hb'
  have horth : (ℝ ∙ (b : V)).IsOrtho (slotOne b) := by
    exact Submodule.isOrtho_iff_le.mpr inf_le_right |>.symm
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ (b : V)) (slotOne b)
  rw [line_slotOne_sup hb, horth.disjoint.eq_bot, finrank_bot, add_zero,
    finrank_span_singleton hb0] at hdim
  obtain ⟨hn, hm, _⟩ := finrank_exact_of_trace_zero round ha hz
  omega

omit [FiniteDimensional ℝ V] in
private theorem scaledHalfAction_injective {u : minusSpace h a} (hu : u ≠ 0) :
    Function.Injective (scaledHalfAction round ha u) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro y hy
  have hn := scaledHalfAction_norm round ha u y
  rw [hy, norm_zero] at hn
  exact norm_eq_zero.mp ((mul_eq_zero.mp hn.symm).resolve_left
    (fun he => hu (norm_eq_zero.mp he)))

/-- With trace zero and positive first-slot dimension all three slots have that dimension. -/
theorem slot_finranks (hb : ‖b‖ = 1) (hz : LinearMap.trace ℝ V (h.L a) = 0)
    (hk : 0 < (Module.finrank ℝ V - 2) / 3) :
    Module.finrank ℝ (slotOne b) = (Module.finrank ℝ V - 2) / 3 ∧
      Module.finrank ℝ (slotTwo round ha b) = (Module.finrank ℝ V - 2) / 3 ∧
      Module.finrank ℝ (slotThree round ha b) = (Module.finrank ℝ V - 2) / 3 := by
  have h₁ := slotOne_finrank round ha hb hz
  have hnonzero : slotOne b ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at h₁
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnonzero
  let u : slotOne b := ⟨v, hv⟩
  have hu0 : slotOneToMinus u ≠ 0 := by
    intro he
    exact hv0 (congrArg Subtype.val he)
  have hB := scaledHalfAction_injective round ha hu0
  have h₂₃ : Function.Injective (slotProduct round ha u) := by
    intro x y he
    apply Subtype.ext
    exact hB (congrArg Subtype.val he)
  let back : slotThree round ha b →ₗ[ℝ] slotTwo round ha b :=
    ((scaledHalfAction round ha (slotOneToMinus u)).comp (slotThree round ha b).subtype).codRestrict
      (slotTwo round ha b) (fun y => scaledHalfAction_slotThree round ha u y.property)
  have h₃₂ : Function.Injective back := by
    intro x y he
    apply Subtype.ext
    exact hB (congrArg Subtype.val he)
  have h₂ := LinearMap.finrank_le_finrank_of_injective h₂₃
  have h₃ := LinearMap.finrank_le_finrank_of_injective h₃₂
  have hOrth := slotTwo_slotThree_orthogonal round ha (b := b)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (slotTwo round ha b) (slotThree round ha b)
  rw [slotTwo_slotThree_sup round ha hb, hOrth.disjoint.eq_bot, finrank_top, finrank_bot,
    add_zero] at hdim
  obtain ⟨_, _, hhalf⟩ := finrank_exact_of_trace_zero round ha hz
  omega

include round ha in
/-- The slot dimension for a proper closed plane system with a marked unit idempotent. -/
theorem slot_dimension_of_closed_planes {ι : Type*} [Fintype ι] {planes : PlaneDecomposition V ι}
    (closed : IsClosedPlaneSystem h planes) (i : ι) (hi : a ∈ planes.plane i)
    (hm : 1 < Fintype.card ι) :
    (Module.finrank ℝ V - 2) / 3 = 2 * (Fintype.card ι - 1) / 3 ∧
      2 ≤ (Module.finrank ℝ V - 2) / 3 := by
  obtain ⟨_, hmod, _, _, _, hn⟩ := closedPlaneDimensions round closed ha i hi
  have hn' := finrank_eq_twice_card planes
  omega

end

end ThirteenPlanes.Peirce
