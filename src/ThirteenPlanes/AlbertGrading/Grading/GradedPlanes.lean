module

public import ThirteenPlanes.AlbertGrading.Grading.GradedFrames
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-! # ternary grading theorem (ii)–(iii): planes of the graded frames

The plane of the frame of a normalized `u ∈ A_g` is `J ∩ (A_g ⊕ A_{-g})`, which lies in `V`;
planes of different points are orthogonal, frames of different points are unbiased, and the
thirteen planes fill `V`. -/

namespace ThirteenPlanes.AlbertGrading.Grading

open JC

noncomputable section

variable {ρ : TernaryAction}

theorem ip_real_smul_left (r : ℝ) (z w : JC) : ip (r • z) w = r * ip z w :=
  ip_smul_left (r : ℂ) z w

theorem inner_eq_ip_re (x y : Glennie.Albert) : Glennie.inner x y = (ip (of x) (of y)).re := by
  rw [ip_of, Complex.ofReal_re]

theorem mem_gradedPlaneJ_iff (g : Charge) (x : Glennie.Albert) :
    x ∈ gradedPlaneJ ρ g ↔ of x ∈ charSpace ρ g ⊔ charSpace ρ (-g) := Iff.rfl

theorem gradedPlaneJ_neg (g : Charge) : gradedPlaneJ ρ (-g) = gradedPlaneJ ρ g := by
  ext x
  rw [mem_gradedPlaneJ_iff, mem_gradedPlaneJ_iff, neg_neg, sup_comm]

theorem gradedPlane_neg (g : Charge) : gradedPlane ρ (-g) = gradedPlane ρ g := by
  unfold gradedPlane; rw [gradedPlaneJ_neg]

/-- Pairings vanish against a sum of two character spaces. -/
theorem ip_eq_zero_of_mem_sup (hρ : IsTernaryGrading ρ) {g₁ g₂ h : Charge} {z w : JC}
    (hz : z ∈ charSpace ρ g₁ ⊔ charSpace ρ g₂) (hw : w ∈ charSpace ρ h)
    (h₁ : g₁ + h ≠ 0) (h₂ : g₂ + h ≠ 0) : ip z w = 0 := by
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
  rw [ip_add_left, ip_eq_zero_of_charSpace hρ hz₁ hw h₁, ip_eq_zero_of_charSpace hρ hz₂ hw h₂,
    add_zero]

theorem ip_eq_zero_of_mem_sup_sup (hρ : IsTernaryGrading ρ) {g₁ g₂ h₁ h₂ : Charge} {z w : JC}
    (hz : z ∈ charSpace ρ g₁ ⊔ charSpace ρ g₂) (hw : w ∈ charSpace ρ h₁ ⊔ charSpace ρ h₂)
    (e₁₁ : g₁ + h₁ ≠ 0) (e₂₁ : g₂ + h₁ ≠ 0) (e₁₂ : g₁ + h₂ ≠ 0) (e₂₂ : g₂ + h₂ ≠ 0) :
    ip z w = 0 := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hw
  rw [ip_add_right, ip_eq_zero_of_mem_sup hρ hz hw₁ e₁₁ e₂₁,
    ip_eq_zero_of_mem_sup hρ hz hw₂ e₁₂ e₂₂, add_zero]

/-- `J ∩ (A_g ⊕ A_{-g}) ⊂ V`. -/
theorem gradedPlaneJ_le_ker (hρ : IsTernaryGrading ρ) {g : Charge} (hg : g ≠ 0) :
    gradedPlaneJ ρ g ≤ Glennie.traceLinear.ker := by
  intro x hx
  have hx' : of x ∈ charSpace ρ g ⊔ charSpace ρ (-g) := hx
  rw [LinearMap.mem_ker, Glennie.traceLinear_apply, ← nativeInner_one_right, inner_eq_ip_re]
  rw [show of (1 : Glennie.Albert) = one from rfl, ip_eq_zero_of_mem_sup hρ hx' (one_mem_charSpace_zero hρ) (by simpa using hg)
    (by simpa using hg), Complex.zero_re]

/-- Graded planes of independent grades are orthogonal. -/
theorem inner_eq_zero_of_gradedPlaneJ (hρ : IsTernaryGrading ρ) {g h : Charge}
    (h₁ : g + h ≠ 0) (h₂ : g - h ≠ 0) {x y : Glennie.Albert} (hx : x ∈ gradedPlaneJ ρ g)
    (hy : y ∈ gradedPlaneJ ρ h) : Glennie.inner x y = 0 := by
  have e₂ : -g + h ≠ 0 := by rw [← sub_eq_neg_add, ← neg_sub]; exact neg_ne_zero.mpr h₂
  have e₃ : g + -h ≠ 0 := by rwa [← sub_eq_add_neg]
  have e₄ : -g + -h ≠ 0 := by rw [← neg_add]; exact neg_ne_zero.mpr h₁
  rw [inner_eq_ip_re, ip_eq_zero_of_mem_sup_sup hρ ((mem_gradedPlaneJ_iff _ _).mp hx)
    ((mem_gradedPlaneJ_iff _ _).mp hy) h₁ e₂ e₃ e₄, Complex.zero_re]

theorem gradedPlane_orthogonal (hρ : IsTernaryGrading ρ) {g h : Charge}
    (h₁ : g + h ≠ 0) (h₂ : g - h ≠ 0) : (gradedPlane ρ g).IsOrtho (gradedPlane ρ h) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx y hy
  exact inner_eq_zero_of_gradedPlaneJ hρ h₁ h₂ hx hy

section Plane

variable (hρ : IsTernaryGrading ρ) {g : Charge} (hg : g ≠ 0) {u : JC}
  (hu : u ∈ charSpace ρ g) (hun : IsNormalized u)

theorem framePointReal_sub (a : Fin 3) :
    of (framePointReal u a - (1 / 3 : ℝ) • (1 : Glennie.Albert)) =
      (1 / 3 : ℂ) • (chargePhase (-(outcome a)) • u + chargePhase (outcome a) • conj u) := by
  rw [of_sub, of_framePointReal, of_smul]
  unfold framePoint
  rw [show (of 1) = one from rfl]
  rw [show ((1 / 3 : ℝ) • one : JC) = ((1 / 3 : ℝ) : ℂ) • one from rfl]
  push_cast
  module

include hu in
theorem framePointReal_sub_mem (a : Fin 3) :
    framePointReal u a - (1 / 3 : ℝ) • (1 : Glennie.Albert) ∈ gradedPlaneJ ρ g := by
  rw [mem_gradedPlaneJ_iff, framePointReal_sub]
  exact Submodule.smul_mem _ _ (Submodule.add_mem_sup (Submodule.smul_mem _ _ hu)
    (Submodule.smul_mem _ _ (conj_mem_charSpace hu)))

include hρ hg hu hun in
theorem nativeFramePlane_le_gradedPlane :
    nativeFramePlane (framePointReal u) ≤ gradedPlane ρ g := by
  have hF := (isFrameOf_framePointReal hρ hg hu hun).1
  rintro _ ⟨v, rfl⟩
  change (nativeFrameChart (framePointReal u) v : Glennie.Albert) ∈ gradedPlaneJ ρ g
  rw [nativeFrameChart_coe hF]
  have hs := nativeFrameEntries_sum v
  have e : nativeFrameSynthesis (framePointReal u) (nativeFrameEntries v) =
      ∑ b, nativeFrameEntries v b • (framePointReal u b - (1 / 3 : ℝ) • (1 : Glennie.Albert)) := by
    change ∑ b, nativeFrameEntries v b • framePointReal u b = _
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, smul_smul]
    rw [show (∑ b, nativeFrameEntries v b * (1 / 3 : ℝ)) = 0 by
      rw [← Finset.sum_mul, hs, zero_mul], zero_smul, sub_zero]
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (framePointReal_sub_mem hu b)

include hρ hg hu hun in
/-- The real-linear coordinate `x ↦ ⟨x, ū⟩` is injective on `J ∩ (A_g ⊕ A_{-g})`. -/
theorem gradedPlane_finrank_le : Module.finrank ℝ (gradedPlane ρ g) ≤ 2 := by
  let f : gradedPlane ρ g →ₗ[ℝ] ℂ :=
    { toFun := fun x => ip (of (x : NativeTraceless)) (conj u)
      map_add' := fun x y => by
        simp only [Submodule.coe_add, of_add, ip_add_left]
      map_smul' := fun r x => by
        simp only [Submodule.coe_smul, of_smul, ip_real_smul_left, RingHom.id_apply,
          Complex.real_smul] }
  have hub : conj u ∈ charSpace ρ (-g) := conj_mem_charSpace hu
  have hub0 : conj u ≠ 0 := conj_ne_zero (ne_zero_of_normalized hun)
  have h3 : ip u (conj u) = 3 := by
    rw [show ip u (conj u) = ip (mul u (conj u)) one by rw [ip_mul_assoc, JC.mul_one], hun.2,
      ip_one_one]
  have h0 : ip (conj u) (conj u) = 0 :=
    ip_eq_zero_of_charSpace hρ hub hub (by rw [← neg_add, charge_add_self, neg_neg]; exact hg)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hx0 : ip (of (x : NativeTraceless)) (conj u) = 0 := hx
    have hmem : of (x : Glennie.Albert) ∈ charSpace ρ g ⊔ charSpace ρ (-g) := x.property
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨α, rfl⟩ := exists_smul_of_mem hρ hu (ne_zero_of_normalized hun) ha
    obtain ⟨β, rfl⟩ := exists_smul_of_mem hρ hub hub0 hb
    have hα : α = 0 := by
      rw [← hab, ip_add_left, ip_smul_left, ip_smul_left, h3, h0] at hx0
      linear_combination hx0 / 3
    have hreal := congrArg conj hab
    rw [conj_of, hα, zero_smul, zero_add, conj_smul, conj_conj] at hreal
    have hβ : β = 0 := by
      have e := congrArg (fun z => ip z (conj u)) hreal
      simp only [ip_smul_left, h3, h0, ← hab, hα, zero_smul, zero_add] at e
      have : star β = 0 := by linear_combination e / 3
      simpa using this
    apply Subtype.ext
    apply Subtype.ext
    apply of_injective
    rw [← hab, hα, hβ, zero_smul, zero_smul, add_zero]
    rfl
  calc Module.finrank ℝ (gradedPlane ρ g) ≤ Module.finrank ℝ ℂ :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = 2 := Complex.finrank_real_complex

include hρ hg hu hun in
theorem nativeFramePlane_eq_gradedPlane :
    nativeFramePlane (framePointReal u) = gradedPlane ρ g := by
  apply Submodule.eq_of_le_of_finrank_le (nativeFramePlane_le_gradedPlane hρ hg hu hun)
  rw [nativeFramePlane_dimension (isFrameOf_framePointReal hρ hg hu hun).1]
  exact gradedPlane_finrank_le hρ hg hu hun

end Plane

/-- Each nonzero grade has a two-dimensional graded plane. -/
theorem gradedPlane_finrank (hρ : IsTernaryGrading ρ) {g : Charge} (hg : g ≠ 0) :
    Module.finrank ℝ (gradedPlane ρ g) = 2 := by
  obtain ⟨u, hu, hun⟩ := exists_normalized hρ hg
  rw [← nativeFramePlane_eq_gradedPlane hρ hg hu hun,
    nativeFramePlane_dimension (isFrameOf_framePointReal hρ hg hu hun).1]

theorem gradedPlane_closed (hρ : IsTernaryGrading ρ) {g : Charge} (hg : g ≠ 0) :
    IsClosedPiece nativeEqualCubic (gradedPlane ρ g) := by
  obtain ⟨u, hu, hun⟩ := exists_normalized hρ hg
  rw [← nativeFramePlane_eq_gradedPlane hρ hg hu hun]
  intro x y hx hy
  exact nativeFramePlane_closed (isFrameOf_framePointReal hρ hg hu hun).1 hx hy

/-- Ternary grading theorem (ii). -/
theorem graded_part_two (hρ : IsTernaryGrading ρ) (g : Charge) (hg : g ≠ 0) :
    (∃ u ∈ charSpace ρ g, IsNormalized u) ∧
    (∀ u ∈ charSpace ρ g, IsNormalized u → ∀ v ∈ charSpace ρ g, IsNormalized v →
      ∃ a : ZMod 3, v = chargePhase a • u) ∧
    (∀ u ∈ charSpace ρ g, IsNormalized u →
      ∃ p : Fin 3 → Glennie.Albert, IsFrameOf u p ∧ contrast p = u ∧
        nativeFramePlane p = gradedPlane ρ g ∧ gradedPlaneJ ρ g ≤ Glennie.traceLinear.ker) :=
  ⟨exists_normalized hρ hg, fun _ hu hun _ hv hvn => normalized_unique hρ hu hun hv hvn,
    fun _ hu hun => ⟨framePointReal _, isFrameOf_framePointReal hρ hg hu hun,
      contrast_framePointReal, nativeFramePlane_eq_gradedPlane hρ hg hu hun,
      gradedPlaneJ_le_ker hρ hg⟩⟩

/-! ## Unbiasedness of the frames of different points -/

theorem ip_framePoint_framePoint (hρ : IsTernaryGrading ρ) {g h : Charge} (hg : g ≠ 0)
    (hh : h ≠ 0) (h₁ : g + h ≠ 0) (h₂ : g - h ≠ 0) {u v : JC} (hu : u ∈ charSpace ρ g)
    (hv : v ∈ charSpace ρ h) (a b : Fin 3) :
    ip (framePoint u a) (framePoint v b) = 1 / 3 := by
  have hub := conj_mem_charSpace hu
  have hvb := conj_mem_charSpace hv
  have hz0 := one_mem_charSpace_zero hρ
  have e1 : ip one v = 0 := ip_eq_zero_of_charSpace hρ hz0 hv (by simpa using hh)
  have e2 : ip one (conj v) = 0 := ip_eq_zero_of_charSpace hρ hz0 hvb (by simpa using hh)
  have e3 : ip u one = 0 := ip_eq_zero_of_charSpace hρ hu hz0 (by simpa using hg)
  have e4 : ip (conj u) one = 0 := ip_eq_zero_of_charSpace hρ hub hz0 (by simpa using hg)
  have e5 : ip u v = 0 := ip_eq_zero_of_charSpace hρ hu hv h₁
  have e6 : ip u (conj v) = 0 := ip_eq_zero_of_charSpace hρ hu hvb (by rwa [← sub_eq_add_neg])
  have e7 : ip (conj u) v = 0 := ip_eq_zero_of_charSpace hρ hub hv
    (by rw [← sub_eq_neg_add, ← neg_sub]; exact neg_ne_zero.mpr h₂)
  have e8 : ip (conj u) (conj v) = 0 := ip_eq_zero_of_charSpace hρ hub hvb
    (by rw [← neg_add]; exact neg_ne_zero.mpr h₁)
  unfold framePoint
  simp only [ip_smul_left, ip_smul_right, ip_add_left, ip_add_right, e1, e2, e3, e4, e5, e6, e7,
    e8, ip_one_one]
  ring

/-- Frames of different points are unbiased. -/
theorem inner_frames (hρ : IsTernaryGrading ρ) {g h : Charge} (hg : g ≠ 0) (hh : h ≠ 0)
    (h₁ : g + h ≠ 0) (h₂ : g - h ≠ 0) {u v : JC} (hu : u ∈ charSpace ρ g) (hv : v ∈ charSpace ρ h)
    {P Q : Fin 3 → Glennie.Albert} (hP : IsFrameOf u P) (hQ : IsFrameOf v Q) (a b : Fin 3) :
    Glennie.inner (P a) (Q b) = 1 / 3 := by
  rw [inner_eq_ip_re, hP.2, hQ.2, ip_framePoint_framePoint hρ hg hh h₁ h₂ hu hv]
  norm_num

/-! ## Points of `PG(2,3)` -/

theorem rep_ne_zero (p : SignedPlaneIndex) : p.val.val ≠ 0 := p.val.property

theorem rep_ne_neg (p q : SignedPlaneIndex) : p.val.val ≠ -q.val.val := by
  intro h
  have hq := (oppositeCharge_isRepresentative_iff q.val).mp
  apply hq _ q.property
  have : (oppositeCharge q.val).val = p.val.val := by rw [h]; rfl
  rw [this]; exact p.property

theorem rep_injective {p q : SignedPlaneIndex} (h : p.val.val = q.val.val) : p = q :=
  Subtype.ext (Subtype.ext h)

theorem rep_add_ne_zero {p q : SignedPlaneIndex} : p.val.val + q.val.val ≠ 0 := by
  intro h; exact rep_ne_neg p q (eq_neg_of_add_eq_zero_left h)

theorem rep_sub_ne_zero {p q : SignedPlaneIndex} (hpq : p ≠ q) : p.val.val - q.val.val ≠ 0 :=
  fun h => hpq (rep_injective (sub_eq_zero.mp h))

/-- The chosen normalized element of each point. -/
def pointUnit (hρ : IsTernaryGrading ρ) (p : SignedPlaneIndex) : JC :=
  Classical.choose (exists_normalized hρ (rep_ne_zero p))

theorem pointUnit_spec (hρ : IsTernaryGrading ρ) (p : SignedPlaneIndex) :
    pointUnit hρ p ∈ charSpace ρ p.val.val ∧ IsNormalized (pointUnit hρ p) :=
  Classical.choose_spec (exists_normalized hρ (rep_ne_zero p))

/-- The thirteen graded frames as an accepted tight native code. -/
def gradedCode (hρ : IsTernaryGrading ρ) : TightNativeCode := by
  let e := (Fintype.equivFinOfCardEq signedPlaneIndex_card).symm
  exact ⟨fun i => framePointReal (pointUnit hρ (e i)),
    fun i => (isFrameOf_framePointReal hρ (rep_ne_zero _) (pointUnit_spec hρ _).1
      (pointUnit_spec hρ _).2).1,
    fun {i j} hij a b => inner_frames hρ (rep_ne_zero _) (rep_ne_zero _) rep_add_ne_zero
      (rep_sub_ne_zero (e.injective.ne hij)) (pointUnit_spec hρ _).1 (pointUnit_spec hρ _).1
      (isFrameOf_framePointReal hρ (rep_ne_zero _) (pointUnit_spec hρ _).1 (pointUnit_spec hρ _).2)
      (isFrameOf_framePointReal hρ (rep_ne_zero _) (pointUnit_spec hρ _).1 (pointUnit_spec hρ _).2)
      a b⟩

theorem pointPlane_eq_nativeFramePlane (hρ : IsTernaryGrading ρ) (p : SignedPlaneIndex) :
    pointPlane ρ p = nativeFramePlane (framePointReal (pointUnit hρ p)) :=
  (nativeFramePlane_eq_gradedPlane hρ (rep_ne_zero p) (pointUnit_spec hρ p).1
    (pointUnit_spec hρ p).2).symm

/-- The thirteen planes fill `V`. -/
theorem pointPlanes_fill (hρ : IsTernaryGrading ρ) : (⨆ p : SignedPlaneIndex, pointPlane ρ p) = ⊤ := by
  have h := (gradedCode hρ).planes_exhaustive
  let e := (Fintype.equivFinOfCardEq signedPlaneIndex_card).symm
  rw [← h, ← e.iSup_comp]
  congr 1
  funext i
  exact pointPlane_eq_nativeFramePlane hρ (e i)

theorem pointPlane_finrank (hρ : IsTernaryGrading ρ) (p : SignedPlaneIndex) :
    Module.finrank ℝ (pointPlane ρ p) = 2 := gradedPlane_finrank hρ (rep_ne_zero p)

theorem pointPlane_orthogonal (hρ : IsTernaryGrading ρ) :
    Pairwise fun p q : SignedPlaneIndex => (pointPlane ρ p).IsOrtho (pointPlane ρ q) :=
  fun _ _ hpq => gradedPlane_orthogonal hρ rep_add_ne_zero (rep_sub_ne_zero hpq)

/-- The graded planes as an orthogonal plane decomposition of `V`. -/
def gradedDecomposition (hρ : IsTernaryGrading ρ) :
    PlaneDecomposition NativeTraceless SignedPlaneIndex :=
  ⟨pointPlane ρ, pointPlane_finrank hρ, pointPlane_orthogonal hρ, pointPlanes_fill hρ⟩

/-- Ternary grading theorem (iii). -/
theorem graded_part_three (hρ : IsTernaryGrading ρ) :
    (∀ (u : Charge → JC) (P : Charge → Fin 3 → Glennie.Albert),
      (∀ g, g ≠ 0 → u g ∈ charSpace ρ g ∧ IsNormalized (u g) ∧ IsFrameOf (u g) (P g)) →
      ∀ g h, g ≠ 0 → h ≠ 0 → h ≠ g → h ≠ -g → ∀ a b, Glennie.inner (P g a) (P h b) = 1 / 3) ∧
    (⨆ p : SignedPlaneIndex, pointPlane ρ p) = ⊤ := by
  refine ⟨?_, pointPlanes_fill hρ⟩
  intro u P hup g h hg hh hhg hhng a b
  exact inner_frames hρ hg hh (fun e => hhng (eq_neg_of_add_eq_zero_right e))
    (fun e => hhg (sub_eq_zero.mp e).symm) (hup g hg).1 (hup h hh).1 (hup g hg).2.2
    (hup h hh).2.2 a b

end

end ThirteenPlanes.AlbertGrading.Grading
