module

public import ThirteenPlanes.RoundIdentities
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

set_option backward.privateInPublic true

/-! Peirce spaces and product rules of a unit idempotent in a normalized round cubic. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.Peirce

noncomputable section

open Module.End Submodule

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {h : SymmetricCubic V} {a : V}

/-- A norm-one field whose square equals itself. -/
structure IsUnitIdempotent (h : SymmetricCubic V) (a : V) : Prop where
  norm_eq_one : ‖a‖ = 1
  square_eq_self : h.L a a = a

/-- The minus-one Peirce space. -/
abbrev minusSpace (h : SymmetricCubic V) (a : V) : Submodule ℝ V :=
  eigenspace (h.L a) (-1)

/-- The one-half Peirce space. -/
abbrev halfSpace (h : SymmetricCubic V) (a : V) : Submodule ℝ V :=
  eigenspace (h.L a) (1 / 2)

/-- The operator identity obtained by repeating the first field in the polarized round law. -/
theorem square_operator (round : IsRound h 1) (x y : V) :
    h.L (h.L x x) y + (2 : ℝ) • h.L x (h.L x y) =
      ‖x‖ ^ 2 • y + (2 * ⟪x, y⟫) • x := by
  apply ext_inner_right ℝ
  intro z
  have hp := RoundCubics.polarized round x x y z
  have h₁ : ⟪h.L (h.L x x) y, z⟫ = ⟪h.L x x, h.L y z⟫ := by
    rw [h.L_comm (h.L x x) y]
    exact h.L_isSymmetric y _ _
  have h₂ := h.L_isSymmetric x (h.L x y) z
  have h₃ : ⟪h.L x (h.L x y), z⟫ = ⟪h.L x z, h.L x y⟫ :=
    h₂.trans (real_inner_comm _ _)
  simp only [one_mul, real_inner_self_eq_norm_sq, ← h₁, ← h₂, ← h₃] at hp
  simp only [inner_add_left, real_inner_smul_left]
  linear_combination hp


/-- The only eigenvalues on the perpendicular space of a unit idempotent. -/
theorem eigenvalues_on_perp (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    {x : V} (hnz : x ≠ 0) (hperp : ⟪a, x⟫ = 0) {r : ℝ} (hx : h.L a x = r • x) :
    r = -1 ∨ r = 1 / 2 := by
  have hs := congrArg (fun y : V => ⟪y, x⟫) (square_operator round a x)
  simp only [ha.square_eq_self, ha.norm_eq_one, one_pow, one_smul, hx, map_smul,
    hperp, mul_zero, zero_smul, add_zero, inner_add_left, real_inner_smul_left] at hs
  have hp : ((r + 1) * (2 * r - 1)) * ⟪x, x⟫ = 0 := by linear_combination hs
  have hinner : ⟪x, x⟫ ≠ 0 := fun he => hnz (inner_self_eq_zero.mp he)
  rcases mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hinner) with hm | hh
  · left
    linarith
  · right
    linarith

private theorem eigenvectors_orthogonal {r s : ℝ} (hrs : r ≠ s) :
    (eigenspace (h.L a) r).IsOrtho (eigenspace (h.L a) s) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx y hy
  have hi := h.L_isSymmetric a x y
  rw [mem_eigenspace_iff.mp hx, mem_eigenspace_iff.mp hy, real_inner_smul_left,
    real_inner_smul_right] at hi
  have hz : (r - s) * ⟪x, y⟫ = 0 := by linarith only [hi]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hrs)

private theorem eigenspace_one (round : IsRound h 1) (ha : IsUnitIdempotent h a) :
    eigenspace (h.L a) 1 = ℝ ∙ a := by
  apply le_antisymm
  · intro x hx
    have hx' : h.L a x = x := by simpa using mem_eigenspace_iff.mp hx
    have hp := square_operator round a x
    simp only [ha.square_eq_self, ha.norm_eq_one, one_pow, one_smul, hx'] at hp
    have hscaled := congrArg ((1 / 2 : ℝ) • ·) (add_left_cancel hp)
    have hspan : x = ⟪a, x⟫ • a := by
      convert hscaled using 1 <;> module
    rw [hspan]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  · apply Submodule.span_le.mpr
    intro x hx
    obtain rfl : x = a := Set.mem_singleton_iff.mp hx
    exact mem_eigenspace_iff.mpr (by simp [ha.square_eq_self])

private theorem split_of_orthogonal (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    {y : V} (hy : ⟪a, y⟫ = 0) : y ∈ minusSpace h a ⊔ halfSpace h a := by
  have hp := square_operator round a y
  simp only [ha.square_eq_self, ha.norm_eq_one, one_pow, one_smul, hy,
    mul_zero, zero_smul, add_zero] at hp
  have hq : h.L a (h.L a y) = (1 / 2 : ℝ) • (y - h.L a y) := by
    have hs := congrArg ((1 / 2 : ℝ) • ·) (eq_sub_of_add_eq' hp)
    convert hs using 1
    module
  let m := (1 / 3 : ℝ) • y - (2 / 3 : ℝ) • h.L a y
  let p := (2 / 3 : ℝ) • y + (2 / 3 : ℝ) • h.L a y
  have hm : m ∈ minusSpace h a := by
    apply mem_eigenspace_iff.mpr
    simp only [m, map_sub, map_smul, hq]
    module
  have hp' : p ∈ halfSpace h a := by
    apply mem_eigenspace_iff.mpr
    simp only [p, map_add, map_smul, hq]
    module
  exact Submodule.mem_sup.mpr ⟨m, hm, p, hp', by dsimp [m, p]; module⟩

/-- The three orthogonal summands of the Peirce decomposition. -/
structure SpectralSplit (h : SymmetricCubic V) (a : V) : Prop where
  line_action : h.L a a = a
  one_eigenspace : eigenspace (h.L a) 1 = ℝ ∙ a
  minus_perp : (ℝ ∙ a).IsOrtho (minusSpace h a)
  half_perp : (ℝ ∙ a).IsOrtho (halfSpace h a)
  minus_half_perp : (minusSpace h a).IsOrtho (halfSpace h a)
  perp_split : minusSpace h a ⊔ halfSpace h a = (ℝ ∙ a)ᗮ
  full_split : (ℝ ∙ a) ⊔ (minusSpace h a ⊔ halfSpace h a) = ⊤

/-- Lemma 2b-peirce (i). -/
theorem spectralSplit (round : IsRound h 1) (ha : IsUnitIdempotent h a) : SpectralSplit h a := by
  have hline := eigenspace_one round ha
  have hm : (ℝ ∙ a).IsOrtho (minusSpace h a) := by
    rw [← hline]
    exact eigenvectors_orthogonal (by norm_num)
  have hp : (ℝ ∙ a).IsOrtho (halfSpace h a) := by
    rw [← hline]
    exact eigenvectors_orthogonal (by norm_num)
  have hperp : minusSpace h a ⊔ halfSpace h a = (ℝ ∙ a)ᗮ := by
    apply le_antisymm (sup_le hm.ge hp.ge)
    intro y hy
    exact split_of_orthogonal round ha (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hy)
  refine ⟨ha.square_eq_self, hline, hm, hp, eigenvectors_orthogonal (by norm_num), hperp, ?_⟩
  rw [hperp]
  exact (Submodule.isCompl_orthogonal _).sup_eq_top


/-- A cubic term on eigenvectors perpendicular to the idempotent vanishes when their
eigenvalues have nonzero sum. -/
theorem cubic_vanishes_of_eigenvalue_sum (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    {r s t : ℝ} (hr : r ≠ 1) (hs : s ≠ 1) (ht : t ≠ 1) (hsum : r + s + t ≠ 0)
    {x y z : V} (hx : x ∈ eigenspace (h.L a) r) (hy : y ∈ eigenspace (h.L a) s)
    (hz : z ∈ eigenspace (h.L a) t) :
    h.apply x y z = 0 := by
  have ha' : a ∈ eigenspace (h.L a) 1 :=
    mem_eigenspace_iff.mpr (by simp [ha.square_eq_self])
  have ortho {q : ℝ} (hq : q ≠ 1) {v : V} (hv : v ∈ eigenspace (h.L a) q) :
      ⟪a, v⟫ = 0 :=
    (eigenvectors_orthogonal (h := h) hq.symm).inner_eq ha' hv
  have term {q : ℝ} {v : V} (hv : v ∈ eigenspace (h.L a) q) (w u : V) :
      ⟪h.L a v, h.L w u⟫ = q * h.apply v w u := by
    rw [mem_eigenspace_iff.mp hv, real_inner_smul_left]
    congr 1
    change ⟪v, h.L w u⟫ = ⟪h.L v w, u⟫
    rw [h.L_comm v w, h.L_isSymmetric w]
  have hp := RoundCubics.polarized round a x y z
  rw [term hx y z, term hy x z, term hz x y, h.apply_swap₁₂ y x z,
    h.apply_swap₁₂ z x y, h.apply_swap₂₃ x z y, ortho hr hx, ortho hs hy, ortho ht hz] at hp
  have hzero : (r + s + t) * h.apply x y z = 0 := by linear_combination hp
  exact (mul_eq_zero.mp hzero).resolve_left hsum

/-- In the two Peirce spaces, a nonzero cubic term has one minus slot and two half slots. -/
theorem cubic_nonzero_implies_one_minus (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    {r s t : ℝ} (hr : r = -1 ∨ r = 1 / 2) (hs : s = -1 ∨ s = 1 / 2)
    (ht : t = -1 ∨ t = 1 / 2) {x y z : V}
    (hx : x ∈ eigenspace (h.L a) r) (hy : y ∈ eigenspace (h.L a) s)
    (hz : z ∈ eigenspace (h.L a) t) (hnz : h.apply x y z ≠ 0) :
    (r = -1 ∧ s = 1 / 2 ∧ t = 1 / 2) ∨
    (r = 1 / 2 ∧ s = -1 ∧ t = 1 / 2) ∨
    (r = 1 / 2 ∧ s = 1 / 2 ∧ t = -1) := by
  have hsum : r + s + t = 0 := by
    by_contra h
    apply hnz
    exact cubic_vanishes_of_eigenvalue_sum round ha
      (by rcases hr with rfl | rfl <;> norm_num)
      (by rcases hs with rfl | rfl <;> norm_num)
      (by rcases ht with rfl | rfl <;> norm_num) h hx hy hz
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    norm_num at hsum <;> norm_num

private theorem inner_product_idempotent {r : ℝ} {x : V}
    (hx : x ∈ eigenspace (h.L a) r) (y : V) :
    ⟪h.L x y, a⟫ = r * ⟪x, y⟫ := by
  change h.apply x y a = _
  rw [h.apply_swap₂₃, SymmetricCubic.apply, h.L_comm x a, mem_eigenspace_iff.mp hx,
    real_inner_smul_left]

private theorem line_component_sub_mem_perp (ha : IsUnitIdempotent h a) (v : V) :
    v - ⟪v, a⟫ • a ∈ (ℝ ∙ a)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, ha.norm_eq_one]
  ring

private theorem sub_line_mem_perp {U : Submodule ℝ V} (hU : (ℝ ∙ a).IsOrtho U)
    {v : V} (hv : v ∈ Uᗮ) (r : ℝ) : v - r • a ∈ Uᗮ :=
  Uᗮ.sub_mem hv (Uᗮ.smul_mem r (hU.le (Submodule.mem_span_singleton_self a)))

private theorem mem_of_ortho_and_sup_eq_top {U W : Submodule ℝ V}
    (horth : U.IsOrtho W) (hsup : U ⊔ W = ⊤) {v : V} (hv : v ∈ Wᗮ) : v ∈ U := by
  have hmem : v ∈ U ⊔ W := by rw [hsup]; trivial
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hmem
  have hwperp : w ∈ Wᗮ := by simpa using Wᗮ.sub_mem hv (horth.le hu)
  have hw0 := inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hw hwperp)
  simpa [hw0] using hu

/-- The product of two fields in the minus space is their negative inner product times the idempotent. -/
theorem minus_mul_minus (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    {u v : V} (hu : u ∈ minusSpace h a) (hv : v ∈ minusSpace h a) :
    h.L u v = (-⟪u, v⟫) • a := by
  have ss := spectralSplit round ha
  have along : ⟪h.L u v, a⟫ = -⟪u, v⟫ := by simpa using inner_product_idempotent hu v
  have hm : h.L u v ∈ (minusSpace h a)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    exact cubic_vanishes_of_eigenvalue_sum round ha (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hu hv hw
  have hp : h.L u v ∈ (halfSpace h a)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    exact cubic_vanishes_of_eigenvalue_sum round ha (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hu hv hw
  have hout : h.L u v - (-⟪u, v⟫) • a ∈
      ((ℝ ∙ a) ⊔ (minusSpace h a ⊔ halfSpace h a))ᗮ := by
    rw [← Submodule.inf_orthogonal, ← Submodule.inf_orthogonal]
    refine ⟨?_, sub_line_mem_perp ss.minus_perp hm _, sub_line_mem_perp ss.half_perp hp _⟩
    rw [← along]
    exact line_component_sub_mem_perp ha _
  rw [ss.full_split, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hout
  exact sub_eq_zero.mp hout

/-- Multiplication by a minus field preserves the one-half Peirce space. -/
theorem minus_mul_half (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    {u x : V} (hu : u ∈ minusSpace h a) (hx : x ∈ halfSpace h a) :
    h.L u x ∈ halfSpace h a := by
  have ss := spectralSplit round ha
  have hline : h.L u x ∈ (ℝ ∙ a)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_product_idempotent hu,
      ss.minus_half_perp.inner_eq hu hx, mul_zero]
  have hm : h.L u x ∈ (minusSpace h a)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    exact cubic_vanishes_of_eigenvalue_sum round ha (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hu hx hw
  apply mem_of_ortho_and_sup_eq_top (W := (ℝ ∙ a) ⊔ minusSpace h a)
  · rw [Submodule.isOrtho_sup_right]
    exact ⟨ss.half_perp.symm, ss.minus_half_perp.symm⟩
  · rw [show halfSpace h a ⊔ ((ℝ ∙ a) ⊔ minusSpace h a) =
        (ℝ ∙ a) ⊔ (minusSpace h a ⊔ halfSpace h a) by ac_rfl, ss.full_split]
  · rw [← Submodule.inf_orthogonal]
    exact ⟨hline, hm⟩

/-- A product of two half fields has line component `⟪x,y⟫ a/2` and minus component. -/
theorem half_mul_half_sub_line (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    {x y : V} (hx : x ∈ halfSpace h a) (hy : y ∈ halfSpace h a) :
    h.L x y - ((1 / 2 : ℝ) * ⟪x, y⟫) • a ∈ minusSpace h a := by
  have ss := spectralSplit round ha
  have hp : h.L x y ∈ (halfSpace h a)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    exact cubic_vanishes_of_eigenvalue_sum round ha (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx hy hw
  apply mem_of_ortho_and_sup_eq_top (W := (ℝ ∙ a) ⊔ halfSpace h a)
  · rw [Submodule.isOrtho_sup_right]
    exact ⟨ss.minus_perp.symm, ss.minus_half_perp⟩
  · rw [show minusSpace h a ⊔ ((ℝ ∙ a) ⊔ halfSpace h a) =
        (ℝ ∙ a) ⊔ (minusSpace h a ⊔ halfSpace h a) by ac_rfl, ss.full_split]
  · rw [← Submodule.inf_orthogonal]
    refine ⟨?_, sub_line_mem_perp ss.half_perp hp _⟩
    rw [← inner_product_idempotent hx y]
    exact line_component_sub_mem_perp ha _


variable [FiniteDimensional ℝ V]

private theorem trace_starProjection (U : Submodule ℝ V) :
    LinearMap.trace ℝ V U.starProjection.toLinearMap = Module.finrank ℝ U := by
  have hp : LinearMap.IsProj U U.starProjection.toLinearMap :=
    ⟨U.starProjection_apply_mem, fun _ hx => Submodule.starProjection_eq_self_iff.mpr hx⟩
  exact hp.trace

private theorem operator_eq_weighted_projections (round : IsRound h 1)
    (ha : IsUnitIdempotent h a) :
    h.L a = (ℝ ∙ a).starProjection.toLinearMap - (minusSpace h a).starProjection.toLinearMap +
      (1 / 2 : ℝ) • (halfSpace h a).starProjection.toLinearMap := by
  have ss := spectralSplit round ha
  have vanish {U W : Submodule ℝ V} (huw : U.IsOrtho W) {x : V} (hx : x ∈ U) :
      W.starProjection x = 0 := by
    apply Submodule.eq_starProjection_of_mem_orthogonal (K := W) (Submodule.zero_mem W)
    simpa only [sub_zero] using (huw.le hx)
  apply LinearMap.ext
  intro x
  have hmem : x ∈ (ℝ ∙ a) ⊔ (minusSpace h a ⊔ halfSpace h a) := by
    rw [ss.full_split]
    trivial
  obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  have he : u ∈ eigenspace (h.L a) 1 := ss.one_eigenspace ▸ hu
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, map_add]
  rw [mem_eigenspace_iff.mp he, mem_eigenspace_iff.mp hv, mem_eigenspace_iff.mp hw,
    Submodule.starProjection_eq_self_iff.mpr hu, Submodule.starProjection_eq_self_iff.mpr hv,
    Submodule.starProjection_eq_self_iff.mpr hw, vanish ss.minus_perp hu, vanish ss.half_perp hu,
    vanish ss.minus_perp.symm hv, vanish ss.half_perp.symm hw, vanish ss.minus_half_perp hv,
    vanish ss.minus_half_perp.symm hw]
  module

omit [FiniteDimensional ℝ V] in
private theorem idempotent_ne_zero (ha : IsUnitIdempotent h a) : a ≠ 0 := by
  intro ha0
  have hn := ha.norm_eq_one
  simp [ha0] at hn

/-- The trace of the idempotent slice in terms of its three Peirce summands. -/
theorem trace_formula (round : IsRound h 1) (ha : IsUnitIdempotent h a) :
    LinearMap.trace ℝ V (h.L a) =
      1 - (Module.finrank ℝ (minusSpace h a) : ℝ) +
        (1 / 2 : ℝ) * Module.finrank ℝ (halfSpace h a) := by
  rw [operator_eq_weighted_projections round ha, map_add, map_sub, map_smul, smul_eq_mul,
    trace_starProjection, trace_starProjection, trace_starProjection,
    finrank_span_singleton (idempotent_ne_zero ha), Nat.cast_one]

/-- The line and the two Peirce spaces account for the entire ambient dimension. -/
theorem finrank_sum (round : IsRound h 1) (ha : IsUnitIdempotent h a) :
    1 + Module.finrank ℝ (minusSpace h a) + Module.finrank ℝ (halfSpace h a) =
      Module.finrank ℝ V := by
  have ss := spectralSplit round ha
  have horth : (ℝ ∙ a).IsOrtho (minusSpace h a ⊔ halfSpace h a) :=
    Submodule.isOrtho_sup_right.mpr ⟨ss.minus_perp, ss.half_perp⟩
  have hfull := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ a)
    (minusSpace h a ⊔ halfSpace h a)
  have hperp := Submodule.finrank_sup_add_finrank_inf_eq (minusSpace h a) (halfSpace h a)
  rw [ss.full_split, horth.disjoint.eq_bot, finrank_top, finrank_bot, add_zero,
    finrank_span_singleton (idempotent_ne_zero ha)] at hfull
  rw [ss.minus_half_perp.disjoint.eq_bot, finrank_bot, add_zero] at hperp
  omega

/-- The exact integral dimension balances under trace zero of the idempotent slice. -/
theorem finrank_exact_of_trace_zero (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    (hz : LinearMap.trace ℝ V (h.L a) = 0) :
    2 ≤ Module.finrank ℝ V ∧
    3 * Module.finrank ℝ (minusSpace h a) = Module.finrank ℝ V + 1 ∧
    3 * Module.finrank ℝ (halfSpace h a) = 2 * (Module.finrank ℝ V - 2) := by
  have hdim := finrank_sum round ha
  have htrace := trace_formula round ha
  rw [hz] at htrace
  have htrace' : 2 * Module.finrank ℝ (minusSpace h a) =
      2 + Module.finrank ℝ (halfSpace h a) := by
    exact_mod_cast (show 2 * (Module.finrank ℝ (minusSpace h a) : ℝ) =
      2 + (Module.finrank ℝ (halfSpace h a) : ℝ) by linarith only [htrace])
  omega

/-- Lemma 2b-peirce (iii), under trace zero of the idempotent slice. -/
theorem finrank_of_trace_zero (round : IsRound h 1) (ha : IsUnitIdempotent h a)
    (hz : LinearMap.trace ℝ V (h.L a) = 0) :
    2 ≤ Module.finrank ℝ V ∧
    Module.finrank ℝ (minusSpace h a) = (Module.finrank ℝ V + 1) / 3 ∧
    Module.finrank ℝ (halfSpace h a) = 2 * (Module.finrank ℝ V - 2) / 3 := by
  obtain ⟨hn, hm, hp⟩ := finrank_exact_of_trace_zero round ha hz
  omega

/-- Lemma 2b-peirce. The dimension formulas require only the trace of `L_a` to vanish. -/
theorem peirceDecomposition (round : IsRound h 1) (ha : IsUnitIdempotent h a) :
    SpectralSplit h a ∧
    (∀ {x : V}, x ≠ 0 → ⟪a, x⟫ = 0 → ∀ {r : ℝ},
      h.L a x = r • x → r = -1 ∨ r = 1 / 2) ∧
    (∀ {r s t : ℝ}, (r = -1 ∨ r = 1 / 2) → (s = -1 ∨ s = 1 / 2) →
      (t = -1 ∨ t = 1 / 2) → ∀ {x y z : V},
      x ∈ eigenspace (h.L a) r → y ∈ eigenspace (h.L a) s → z ∈ eigenspace (h.L a) t →
      h.apply x y z ≠ 0 →
      (r = -1 ∧ s = 1 / 2 ∧ t = 1 / 2) ∨
        (r = 1 / 2 ∧ s = -1 ∧ t = 1 / 2) ∨ (r = 1 / 2 ∧ s = 1 / 2 ∧ t = -1)) ∧
    (∀ u ∈ minusSpace h a, ∀ v ∈ minusSpace h a, h.L u v = (-⟪u, v⟫) • a) ∧
    (∀ u ∈ minusSpace h a, ∀ x ∈ halfSpace h a, h.L u x ∈ halfSpace h a) ∧
    (∀ x ∈ halfSpace h a, ∀ y ∈ halfSpace h a,
      h.L x y - ((1 / 2 : ℝ) * ⟪x, y⟫) • a ∈ minusSpace h a) ∧
    (LinearMap.trace ℝ V (h.L a) = 0 →
      2 ≤ Module.finrank ℝ V ∧
      Module.finrank ℝ (minusSpace h a) = (Module.finrank ℝ V + 1) / 3 ∧
      Module.finrank ℝ (halfSpace h a) = 2 * (Module.finrank ℝ V - 2) / 3) := by
  exact ⟨spectralSplit round ha, eigenvalues_on_perp round ha,
    cubic_nonzero_implies_one_minus round ha,
    fun _ hu _ hv => minus_mul_minus round ha hu hv,
    fun _ hu _ hx => minus_mul_half round ha hu hx,
    fun _ hx _ hy => half_mul_half_sub_line round ha hx hy,
    finrank_of_trace_zero round ha⟩

end

end ThirteenPlanes.Peirce
