module

public import ThirteenPlanes.ChargeFixedSupport
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option backward.privateInPublic true

/-! The normal equations and a smooth chart for the purely exterior sector of the chamber. -/

open scoped ContDiff

namespace ThirteenPlanes
namespace ChargeFixed

set_option maxRecDepth 3000

noncomputable section

abbrev OutsideDiagonal := OutsidePlane → ℂ
abbrev OutsideMixing := OutsideTriple → ℂ
abbrev OutsidePhases := OutsidePlane → ℝ

/-- Each exterior plane sees one unit of diagonal strength and half a unit per incident triple,
with the mass normalized to one third for a single exterior super-Ising plane. -/
def outsideMixingSq (b : OutsideMixing) (p : OutsidePlane) : ℝ :=
  ∑ T : OutsideTriple, if p.val ∈ T.val then Complex.normSq (b T) else 0

def outsideMass (a : OutsideDiagonal) (b : OutsideMixing) (p : OutsidePlane) : ℝ :=
  Complex.normSq (a p) / 3 + outsideMixingSq b p / 6

private theorem outsideTriple_mem_nonmarked (T : OutsideTriple) (p : ↥T.val) : p.val ∈ outsidePlanes := by
  have hc : markedCount T.val = 0 := (Finset.mem_filter.mp T.property).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro h
  have hp := Finset.mem_filter.mpr ⟨p.property,h⟩
  rw [markedCount, Finset.card_eq_zero] at hc
  rw [hc] at hp
  exact Finset.notMem_empty _ hp

private def triplePlane (T : OutsideTriple) (p : ↥T.val) : OutsidePlane :=
  ⟨p.val,outsideTriple_mem_nonmarked T p⟩

private theorem outsideTriple_card (T : OutsideTriple) : T.val.card = 3 := by
  have ht : T.val ∈ signedCollinearTriples := (Finset.mem_filter.mp T.property).1
  obtain ⟨l,_,hl⟩ := Finset.mem_biUnion.mp ht
  exact (Finset.mem_powersetCard.mp hl).2

/-- The rescaled exterior coefficient equations obtained when the triangle term is zero. -/
def exteriorNormalEquations (a : OutsideDiagonal) (b : OutsideMixing) :
    OutsideDiagonal × OutsideMixing :=
  (fun p => ((3 * outsideMass a b p - 1) / 2 : ℝ) • a p,
   fun T => (((∑ p : ↥T.val, outsideMass a b (triplePlane T p)) - 1) / 2 : ℝ) • b T)

/-- Near the exterior product point, the nonzero diagonal entries force each mass separately. -/
theorem exteriorNormalEquations_zero_iff (a : OutsideDiagonal) (b : OutsideMixing)
    (ha : ∀ p, a p ≠ 0) :
    exteriorNormalEquations a b = 0 ↔ ∀ p, outsideMass a b p = 1 / 3 := by
  constructor
  · intro h p
    have hp : ((3 * outsideMass a b p - 1) / 2 : ℝ) • a p = 0 := congrFun (congrArg Prod.fst h) p
    exact (by linarith [(smul_eq_zero.mp hp).resolve_right (ha p)])
  · intro h
    apply Prod.ext
    · funext p
      change ((3 * outsideMass a b p - 1) / 2 : ℝ) • a p = 0
      rw [h p, show (3 * (1 / 3) - 1) / 2 = (0 : ℝ) by norm_num, zero_smul]
    · funext T
      change (((∑ p : ↥T.val, outsideMass a b (triplePlane T p)) - 1) / 2 : ℝ) • b T = 0
      simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_coe, outsideTriple_card]
      rw [show ((3 : ℕ) • (1 / 3 : ℝ) - 1) / 2 = 0 by norm_num, zero_smul]

/-- Squared real part of the diagonal coefficient in the positive-real branch. -/
def exteriorRadiusSq (q : OutsidePhases × OutsideMixing) (p : OutsidePlane) : ℝ :=
  1 - q.1 p ^ 2 - outsideMixingSq q.2 p / 2

def exteriorChartDomain : Set (OutsidePhases × OutsideMixing) :=
  {q | ∀ p, 0 < exteriorRadiusSq q p}

/-- Real and imaginary parts give a smooth local chart on the exterior fixed solutions. -/
def exteriorFixedChart (q : OutsidePhases × OutsideMixing) :
    OutsideDiagonal × OutsideMixing :=
  (fun p => ⟨Real.sqrt (exteriorRadiusSq q p),q.1 p⟩,q.2)

def exteriorFixedRead (x : OutsideDiagonal × OutsideMixing) :
    OutsidePhases × OutsideMixing := (fun p => (x.1 p).im,x.2)

@[simp] theorem exteriorFixedRead_chart (q : OutsidePhases × OutsideMixing) :
    exteriorFixedRead (exteriorFixedChart q) = q := by
  cases q
  rfl

private theorem exteriorChart_mass (q : OutsidePhases × OutsideMixing) (hq : q ∈ exteriorChartDomain)
    (p : OutsidePlane) : outsideMass (exteriorFixedChart q).1 q.2 p = 1 / 3 := by
  unfold outsideMass
  change Complex.normSq ⟨Real.sqrt (exteriorRadiusSq q p),q.1 p⟩ / 3 + _ = _
  rw [Complex.normSq_apply]
  change (Real.sqrt (exteriorRadiusSq q p) * Real.sqrt (exteriorRadiusSq q p) + q.1 p*q.1 p) / 3 + _ = _
  rw [Real.mul_self_sqrt (le_of_lt (hq p))]
  unfold exteriorRadiusSq
  ring

theorem exteriorChart_fixed (q : OutsidePhases × OutsideMixing) (hq : q ∈ exteriorChartDomain) :
    exteriorNormalEquations (exteriorFixedChart q).1 (exteriorFixedChart q).2 = 0 := by
  have ha (p : OutsidePlane) : (exteriorFixedChart q).1 p ≠ 0 := by
    intro h
    have he : Real.sqrt (exteriorRadiusSq q p) = 0 := congrArg Complex.re h
    exact (ne_of_gt (Real.sqrt_pos.mpr (hq p))) he
  exact (exteriorNormalEquations_zero_iff _ _ ha).2 (exteriorChart_mass q hq)

theorem exteriorChart_right_inv (x : OutsideDiagonal × OutsideMixing)
    (hp : ∀ p, 0 < (x.1 p).re) (hx : exteriorNormalEquations x.1 x.2 = 0) :
    exteriorFixedRead x ∈ exteriorChartDomain ∧ exteriorFixedChart (exteriorFixedRead x) = x := by
  have hs := (exteriorNormalEquations_zero_iff x.1 x.2 (fun p he =>
    (ne_of_gt (hp p)) (congrArg Complex.re he))).1 hx
  have key (p : OutsidePlane) : exteriorRadiusSq (exteriorFixedRead x) p = (x.1 p).re ^ 2 := by
    have h := hs p
    rw [outsideMass, Complex.normSq_apply] at h
    unfold exteriorRadiusSq exteriorFixedRead
    dsimp
    linarith
  constructor
  · intro p
    rw [key]
    exact pow_pos (hp p) _
  · apply Prod.ext
    · funext p
      apply Complex.ext
      · change Real.sqrt (exteriorRadiusSq (exteriorFixedRead x) p) = _
        rw [key, Real.sqrt_sq_eq_abs, abs_of_pos (hp p)]
      · rfl
    · rfl

private theorem outsideMixingSq_contDiff (n : ℕ∞ω) (p : OutsidePlane) :
    ContDiff ℝ n (fun q : OutsidePhases × OutsideMixing => outsideMixingSq q.2 p) := by
  unfold outsideMixingSq
  apply ContDiff.sum
  intro T _
  by_cases hp : p.val ∈ T.val
  · simp only [ite_eq_left hp, Complex.normSq_apply]
    have hT : ContDiff ℝ n (fun q : OutsidePhases × OutsideMixing => q.2 T) :=
      (contDiff_apply ℝ (fun _ : OutsideTriple => ℂ) T).comp contDiff_snd
    have hr : ContDiff ℝ n (fun q : OutsidePhases × OutsideMixing => (q.2 T).re) :=
      Complex.reCLM.contDiff.comp hT
    have hi : ContDiff ℝ n (fun q : OutsidePhases × OutsideMixing => (q.2 T).im) :=
      Complex.imCLM.contDiff.comp hT
    exact (hr.mul hr).add (hi.mul hi)
  · simpa only [ite_eq_right hp] using
      (contDiff_const : ContDiff ℝ n (fun _ : OutsidePhases × OutsideMixing => (0 : ℝ)))

theorem exteriorRadiusSq_contDiff (n : ℕ∞ω) (p : OutsidePlane) :
    ContDiff ℝ n (fun q : OutsidePhases × OutsideMixing => exteriorRadiusSq q p) := by
  unfold exteriorRadiusSq
  have h := outsideMixingSq_contDiff n p
  fun_prop

theorem exteriorChartDomain_open : IsOpen exteriorChartDomain := by
  rw [show exteriorChartDomain = ⋂ p : OutsidePlane, {q | 0 < exteriorRadiusSq q p} by
    ext q; simp [exteriorChartDomain]]
  apply isOpen_iInter_of_finite
  intro p
  exact isOpen_lt continuous_const (exteriorRadiusSq_contDiff 0 p).continuous

theorem exteriorChart_smooth : ContDiffOn ℝ ∞ exteriorFixedChart exteriorChartDomain := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  unfold exteriorFixedChart
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro p
    have hs : ContDiffAt ℝ ∞ (fun u => Real.sqrt (exteriorRadiusSq u p)) q :=
      (exteriorRadiusSq_contDiff ∞ p).contDiffAt.sqrt (ne_of_gt (hq p))
    have hi : ContDiffAt ℝ ∞ (fun u : OutsidePhases × OutsideMixing => u.1 p) q := by fun_prop
    change ContDiffAt ℝ ∞ (fun u : OutsidePhases × OutsideMixing =>
      (⟨Real.sqrt (exteriorRadiusSq u p),u.1 p⟩ : ℂ)) q
    have he : (fun u : OutsidePhases × OutsideMixing =>
      (⟨Real.sqrt (exteriorRadiusSq u p),u.1 p⟩ : ℂ)) =
      fun u => (Real.sqrt (exteriorRadiusSq u p) : ℂ) + (u.1 p : ℂ) * Complex.I := by
        funext u; apply Complex.ext <;> simp
    rw [he]
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp q hs).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp q hi).mul contDiffAt_const)
  · fun_prop

/-- The free exterior coordinates have nine diagonal phases and twelve complex mixed coefficients. -/
theorem exteriorFixedChart_finrank : Module.finrank ℝ (OutsidePhases × OutsideMixing) = 33 := by
  rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi_fintype,
    Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    Fintype.card_coe, outsidePlanes_card, outsideTriples_card]
  decide

/-- The exterior product of the nine unit-strength scalar cubics. -/
def exteriorProduct : OutsideDiagonal × OutsideMixing := (fun _ => 1,0)

private theorem exteriorRadiusSq_zero (p : OutsidePlane) : exteriorRadiusSq 0 p = 1 := by
  simp [exteriorRadiusSq, outsideMixingSq]

theorem zero_mem_exteriorChartDomain : 0 ∈ exteriorChartDomain := by
  intro p
  rw [exteriorRadiusSq_zero]
  norm_num

@[simp] theorem exteriorFixedChart_zero : exteriorFixedChart 0 = exteriorProduct := by
  apply Prod.ext
  · funext p
    apply Complex.ext
    · change Real.sqrt (exteriorRadiusSq 0 p) = 1
      rw [exteriorRadiusSq_zero, Real.sqrt_one]
    · rfl
  · rfl

theorem exteriorProduct_fixed : exteriorNormalEquations exteriorProduct.1 exteriorProduct.2 = 0 := by
  simpa only [exteriorFixedChart_zero] using exteriorChart_fixed 0 zero_mem_exteriorChartDomain

theorem exteriorRead_smooth : ContDiff ℝ ∞ exteriorFixedRead := by
  unfold exteriorFixedRead
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro p
    exact Complex.imCLM.contDiff.comp
      ((contDiff_apply ℝ (fun _ : OutsidePlane => ℂ) p).comp contDiff_fst)
  · exact contDiff_snd

/-- The differential of the exterior mass constraints in the diagonal real directions. -/
def exteriorRadialDifferential : (OutsideDiagonal × OutsideMixing) →ₗ[ℝ] OutsidePhases where
  toFun q p := (2 / 3 : ℝ) * (q.1 p).re
  map_add' a b := by funext p; simp [mul_add]
  map_smul' a b := by funext p; simp; ring

private theorem outsidePhase_finrank : Module.finrank ℝ OutsidePhases = 9 := by
  rw [Module.finrank_pi, Fintype.card_coe, outsidePlanes_card]

theorem exteriorRadialDifferential_surjective : Function.Surjective exteriorRadialDifferential := by
  intro f
  refine ⟨(fun p => ((3/2 : ℝ) * f p : ℝ),0),?_⟩
  funext p
  change (2 / 3 : ℝ) * (((3/2 : ℝ) * f p : ℝ) : ℂ).re = f p
  simp
  ring

theorem exteriorRadialDifferential_rank : Module.finrank ℝ exteriorRadialDifferential.range = 9 := by
  rw [LinearMap.range_eq_top.mpr exteriorRadialDifferential_surjective,finrank_top,outsidePhase_finrank]

private theorem outsideMixingSq_smul (s : ℝ) (b : OutsideMixing) (p : OutsidePlane) :
    outsideMixingSq (s • b) p = s^2 * outsideMixingSq b p := by
  unfold outsideMixingSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hp : p.val ∈ T.val
  · simp only [ite_eq_left hp, Pi.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal, pow_two]
  · simp [hp]

private theorem exteriorPath_mass (s : ℝ) (v : OutsideDiagonal × OutsideMixing) (p : OutsidePlane) :
    outsideMass (exteriorProduct + s • v).1 (exteriorProduct + s • v).2 p =
      ((1+s*(v.1 p).re)^2 + (s*(v.1 p).im)^2) / 3 + s^2 * outsideMixingSq v.2 p / 6 := by
  unfold outsideMass
  change Complex.normSq (1 + s • v.1 p) / 3 + outsideMixingSq (0+s • v.2) p / 6 = _
  rw [zero_add, outsideMixingSq_smul, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.smul_re,
    Complex.smul_im, zero_add]
  ring

/-- The nine exterior mass constraints have the indicated full-rank directional derivative at
 the exterior product point. -/
theorem exteriorMass_hasDerivAt (v : OutsideDiagonal × OutsideMixing) (p : OutsidePlane) :
    HasDerivAt (fun s : ℝ => outsideMass (exteriorProduct + s • v).1 (exteriorProduct + s • v).2 p)
      (exteriorRadialDifferential v p) 0 := by
  simp_rw [exteriorPath_mass]
  have h0 := hasDerivAt_id (0 : ℝ)
  have h1 := (h0.mul_const (v.1 p).re).const_add 1
  have h2 := h0.mul_const (v.1 p).im
  have h3 := ((h0.pow 2).mul_const (outsideMixingSq v.2 p)).div_const 6
  convert (((h1.pow 2).add (h2.pow 2)).div_const 3).add h3 using 1
  · funext s
    simp
  · change (2 / 3 : ℝ) * (v.1 p).re = _
    norm_num
    ring

/-- The rescaled potential for the exterior block when its triangle term vanishes. -/
def exteriorPotential (a : OutsideDiagonal) (b : OutsideMixing) : ℝ :=
  ∑ p : OutsidePlane, 2 * (-(1 / 4) * outsideMass a b p + 3 / 8 * outsideMass a b p ^ 2)

theorem exteriorChart_potential (q : OutsidePhases × OutsideMixing) (hq : q ∈ exteriorChartDomain) :
    exteriorPotential (exteriorFixedChart q).1 q.2 = -(3 / 4 : ℝ) := by
  simp only [exteriorPotential, exteriorChart_mass _ hq, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, outsidePlanes_card]
  norm_num

end
end ChargeFixed
end ThirteenPlanes
