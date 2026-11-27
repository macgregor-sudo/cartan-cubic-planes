module

public import ThirteenPlanes.Basic
public import ThirteenPlanes.NativeTitsRecognition
public import ThirteenPlanes.NativeFramesPlaneData
public import ThirteenPlanes.SignedEnergyBasic

@[expose] public section

set_option backward.privateInPublic true

/-! Native frames obtained by Fourier inversion on the opposite nonzero grades. -/

namespace ThirteenPlanes.Graded

open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- The native traceless realization of the coordinates supported on two opposite grades. -/
def planeChart (p : SignedPlaneIndex) : ℂ →ₗ[ℝ] NativeTraceless :=
  signedNativeEquiv.toLinearMap.comp (signedPlaneInclusion p)

/-- The real plane of the projective point represented by the grade of (p). -/
def plane (p : SignedPlaneIndex) : Submodule ℝ NativeTraceless :=
  (signedPlane p).map signedNativeEquiv.toLinearMap

private theorem chart_mem (p : SignedPlaneIndex) (z : ℂ) : planeChart p z ∈ plane p :=
  ⟨signedPlaneInclusion p z, ⟨z, rfl⟩, rfl⟩

theorem plane_eq_range (p : SignedPlaneIndex) : plane p = LinearMap.range (planeChart p) := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact chart_mem p z

theorem plane_finrank (p : SignedPlaneIndex) : Module.finrank ℝ (plane p) = 2 :=
  (signedNativeEquiv.submoduleMap (signedPlane p)).toLinearEquiv.finrank_eq.symm.trans
    (signedPlane_finrank p)

theorem plane_orthogonal : Pairwise fun p q : SignedPlaneIndex => (plane p).IsOrtho (plane q) := by
  intro p q hpq
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
  change ⟪signedNativeEquiv u, signedNativeEquiv v⟫ = 0
  rw [LinearIsometryEquiv.inner_map_map]
  exact (Submodule.isOrtho_iff_inner_eq.mp (signedPlane_pairwise_orthogonal hpq)) u hu v hv

theorem plane_exhaustive : (⨆ p, plane p) = ⊤ := by
  simp_rw [plane]
  rw [← Submodule.map_iSup, signedPlane_iSup_eq_top, Submodule.map_top,
    LinearMap.range_eq_top.mpr signedNativeEquiv.surjective]

private def chartInAlbert (p : SignedPlaneIndex) : ℂ →ₗ[ℝ] Glennie.Albert :=
  Glennie.traceLinear.ker.subtype.comp (planeChart p)

@[simp] private theorem chartInAlbert_apply (p : SignedPlaneIndex) (z : ℂ) :
    chartInAlbert p z = (planeChart p z : Glennie.Albert) := rfl

private def outcomeGrade (a : Fin 3) : ZMod 3 := a

/-- The point with outcome (a) has Fourier coefficient (omega^{-a}/3) at the chosen grade. -/
def point (p : SignedPlaneIndex) (a : Fin 3) : Glennie.Albert :=
  (1 / 3 : ℝ) • ((1 : Glennie.Albert) + chartInAlbert p (chargePhase (-(outcomeGrade a))))

private theorem planeChart_product (p : SignedPlaneIndex) (z w : ℂ) :
    nativeEqualCubic.L (planeChart p z) (planeChart p w) = planeChart p (star (z * w)) := by
  change nativeEqualCubic.L (signedNativeEquiv _) (signedNativeEquiv _) = signedNativeEquiv _
  rw [← signedNativeEquiv_product, signedEqualCubic_L_same_plane]

private theorem chart_inner (p : SignedPlaneIndex) (z w : ℂ) :
    Glennie.inner (chartInAlbert p z) (chartInAlbert p w) = 6 * (star z * w).re := by
  change ⟪signedNativeEquiv (signedPlaneInclusion p z),
    signedNativeEquiv (signedPlaneInclusion p w)⟫ = _
  rw [LinearIsometryEquiv.inner_map_map, signedPlaneInclusion_inner]

private theorem chart_jordan (p : SignedPlaneIndex) (z w : ℂ) :
    Glennie.jordan (chartInAlbert p z) (chartInAlbert p w) =
      (2 * (star z * w).re) • (1 : Glennie.Albert) + chartInAlbert p (star (z * w)) := by
  have hc := congrArg Subtype.val (planeChart_product p z w)
  change Glennie.jordan (chartInAlbert p z) (chartInAlbert p w) -
    (Glennie.inner (chartInAlbert p z) (chartInAlbert p w) / 3) • (1 : Glennie.Albert) = _ at hc
  rw [chart_inner p z w, show (6 * (star z * w).re) / 3 = 2 * (star z * w).re by ring] at hc
  rw [add_comm]
  exact sub_eq_iff_eq_add.mp hc

private theorem phase_sum : (∑ a : Fin 3, chargePhase (-(outcomeGrade a))) = 0 := by
  rw [Fin.sum_univ_three]
  change 1 + chargeRoot ^ 2 + chargeRoot ^ 1 = 0
  linear_combination chargeRoot_quadratic

private theorem phase_gram (a b : ZMod 3) :
    (star (chargePhase (-a)) * chargePhase (-b)).re = if a = b then 1 else -1 / 2 := by
  rw [← chargePhase_neg, neg_neg, ← chargePhase_add, ← sub_eq_add_neg]
  by_cases hab : a = b
  · simp [hab]
  · have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    rw [ite_eq_right hab]
    generalize a - b = c at hne ⊢
    fin_cases c
    · exact (hne rfl).elim
    · change (chargeRoot ^ 1).re = _
      rw [pow_one, chargeRoot_re]
    · change (chargeRoot ^ 2).re = _
      rw [chargeRoot_sq_eq_star]
      exact chargeRoot_re

private theorem phase_product_sum (a b : ZMod 3) :
    chargePhase (-a) + chargePhase (-b) + star (chargePhase (-a) * chargePhase (-b)) =
      if a = b then 3 * chargePhase (-a) else 0 := by
  rw [← chargePhase_add, ← chargePhase_neg, neg_add_rev, neg_neg, neg_neg, add_comm b a]
  have triple (x : ZMod 3) : x + x = -x := by
    linear_combination x * (by decide : (3 : ZMod 3) = 0)
  by_cases h : a = b
  · simp [h, triple]
    ring
  · rw [ite_eq_right h]
    have h₁ : -a ≠ -b := fun e => h (neg_injective e)
    have h₂ : -a ≠ a + b := by
      intro he
      rw [← triple a] at he
      exact h (add_left_cancel he)
    have h₃ : -b ≠ a + b := by
      intro he
      rw [← triple b, add_comm a b] at he
      exact h (add_left_cancel he).symm
    have hn₁ : -a ∉ ({-b, a + b} : Finset (ZMod 3)) := by simp [h₁, h₂]
    have hn₂ : -b ∉ ({a + b} : Finset (ZMod 3)) := by simpa using h₃
    have he : ({-a, -b, a + b} : Finset (ZMod 3)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_insert_of_notMem hn₁, Finset.card_insert_of_notMem hn₂, Finset.card_singleton]
      decide
    have hs : (∑ i : ZMod 3, chargePhase i) = 0 := by
      change (∑ i : Fin 3, chargePhase (show ZMod 3 from i)) = 0
      rw [Fin.sum_univ_three]
      change 1 + chargeRoot ^ 1 + chargeRoot ^ 2 = 0
      linear_combination chargeRoot_quadratic
    rw [← he, Finset.sum_insert hn₁, Finset.sum_insert hn₂, Finset.sum_singleton] at hs
    linear_combination hs

private theorem point_jordan (p : SignedPlaneIndex) (a b : Fin 3) :
    Glennie.jordan (point p a) (point p b) = if a = b then point p a else 0 := by
  let g := outcomeGrade a
  let k := outcomeGrade b
  let z := chargePhase (-g)
  let w := chargePhase (-k)
  have hc := phase_product_sum g k
  have hi := phase_gram g k
  change z + w + star (z * w) = _ at hc
  change (star z * w).re = _ at hi
  have hunit (x : Glennie.Albert) : Glennie.jordan 1 x = x := by simp
  have hunit' (x : Glennie.Albert) : Glennie.jordan x 1 = x := by
    rw [Glennie.jordan_comm, hunit]
  have hex :
      Glennie.jordan (point p a) (point p b) =
        (1 / 9 : ℝ) •
          ((1 + 2 * (star z * w).re) • (1 : Glennie.Albert) +
            chartInAlbert p (z + w + star (z * w))) := by
    unfold point
    change Glennie.jordan ((1 / 3 : ℝ) • (1 + chartInAlbert p z))
      ((1 / 3 : ℝ) • (1 + chartInAlbert p w)) = _
    rw [Glennie.jordan_smul_left, Glennie.jordan_smul_right, smul_smul]
    norm_num only [show (1 / 3 : ℝ) * (1 / 3) = 1 / 9 by norm_num]
    congr 1
    rw [Glennie.jordan_add_left, Glennie.jordan_add_right, Glennie.jordan_add_right,
      hunit, hunit, hunit', chart_jordan]
    simp only [map_add]
    module
  rw [hex, hc, hi]
  by_cases hab : a = b
  · subst b
    have h : g = k := rfl
    rw [ite_eq_left h, ite_eq_left h, ite_eq_left rfl]
    change _ = (1 / 3 : ℝ) • (1 + chartInAlbert p z)
    rw [show (3 : ℂ) * z = (3 : ℝ) • z by norm_num [Complex.real_smul]]
    rw [map_smul]
    module
  · have hn : g ≠ k := hab
    rw [ite_eq_right hn, ite_eq_right hn, ite_eq_right hab, map_zero]
    norm_num

/-- The first-Tits construction gives an actual native Jordan frame at each projective point. -/
theorem isFrame (p : SignedPlaneIndex) : Glennie.Frame (point p) where
  idempotent a := by simp [point_jordan]
  orthogonal a b hab := by simp [point_jordan, hab]
  sum_unit := by
    rw [← Fin.sum_univ_three (point p)]
    have hs := map_sum (chartInAlbert p)
      (fun a : Fin 3 => chargePhase (-(outcomeGrade a))) Finset.univ
    rw [phase_sum, map_zero] at hs
    unfold point at *
    rw [← Finset.smul_sum, Finset.sum_add_distrib, ← hs]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    module
  trace_one a := by
    unfold point
    simp [Glennie.trace_smul, Glennie.trace_add, Glennie.trace_unit]

theorem center_point (p : SignedPlaneIndex) (a : Fin 3) :
    nativeCenter (point p a) = (1 / 3 : ℝ) • planeChart p (chargePhase (-(outcomeGrade a))) := by
  apply Subtype.ext
  rw [nativeCenter_coe, Glennie.traceless, (isFrame p).trace_one]
  simp only [point, chartInAlbert_apply, Submodule.coe_smul, smul_add]
  abel

theorem nativeFramePlane_point (p : SignedPlaneIndex) : nativeFramePlane (point p) = plane p := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨a, rfl⟩
    change nativeCenter (∑ b, nativeFrameEntries a b • point p b) ∈ plane p
    rw [map_sum]
    apply Submodule.sum_mem
    intro b _
    rw [map_smul, center_point]
    exact (plane p).smul_mem _ ((plane p).smul_mem _ (chart_mem p _))
  · rw [nativeFramePlane_dimension (isFrame p), plane_finrank]

/-- Distinct projective points yield pairwise unbiased native frames. -/
theorem point_unbiased {p q : SignedPlaneIndex} (hpq : p ≠ q) (a b : Fin 3) :
    Glennie.inner (point p a) (point q b) = 1 / 3 := by
  have hh := Submodule.isOrtho_iff_inner_eq.mp (plane_orthogonal hpq)
    _ (chart_mem p (chargePhase (-(outcomeGrade a))))
    _ (chart_mem q (chargePhase (-(outcomeGrade b))))
  change Glennie.inner (chartInAlbert p _) (chartInAlbert q _) = 0 at hh
  unfold point
  rw [Glennie.inner_smul_left, Glennie.inner_smul_right, Glennie.inner_add_left,
    Glennie.inner_add_right, Glennie.inner_add_right, nativeInner_one_left,
    nativeInner_one_left, nativeInner_one_right, hh]
  simp [Glennie.trace_unit]

/-- The thirteen native frame planes form the actual orthogonal decomposition of the traceless part. -/
def decomposition : PlaneDecomposition NativeTraceless SignedPlaneIndex :=
  ⟨plane, plane_finrank, plane_orthogonal, plane_exhaustive⟩

theorem closedPlanes : IsClosedPlaneSystem nativeEqualCubic decomposition := by
  intro p
  rw [show decomposition.plane p = nativeFramePlane (point p) by
    exact (nativeFramePlane_point p).symm]
  intro x y hx hy
  exact nativeFramePlane_closed (isFrame p) hx hy

/-- The concrete thirteen native frames, labelled by the finite projective points. -/
def nativeCode : TightNativeCode := by
  let e := Fintype.equivFinOfCardEq signedPlaneIndex_card
  exact ⟨fun p => point (e.symm p), fun p => isFrame (e.symm p),
    fun h a b => point_unbiased (e.symm.injective.ne h) a b⟩

end

end ThirteenPlanes.Graded
