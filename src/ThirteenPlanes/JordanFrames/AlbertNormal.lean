module

public import ThirteenPlanes.JordanFrames.AlbertSlots
public import Glennie.Diagonalization
public import Glennie.Automorphism

@[expose] public section

set_option backward.privateInPublic true

/-! The Fourier normal form of all unbiased compact Albert frame pairs. -/

open scoped BigOperators

namespace ThirteenPlanes.JordanFrames

open AlbertSequential.NativeAnalysis

noncomputable section

/- The paper uses Yokota's diagonalization result (arXiv:0902.0431, Proposition 2.8.2)
for diagonal frames. This proof transports the frame normalization theorem
`AlbertSequential.native_frame_to_standardFrame` to the native carrier. -/
private theorem native_frame_to_diagonal (p : Fin 3 → Glennie.Albert) (hp : Glennie.Frame p) :
    ∃ g : Glennie.CompactAutomorphism, ∀ i, g.equiv (p i) = Glennie.standardFrame i := by
  let F : AlbertSequential.NativeJordanFrame :=
    { atom := fun i => recoveredCoordinateEquiv.symm (p i)
      atoms := fun i => by
        constructor
        · apply recoveredCoordinateEquiv.injective
          rw [recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply, hp.idempotent]
        · rw [← recoveredCoordinateEquiv_trace, LinearEquiv.apply_symm_apply, hp.trace_one]
      orthogonal := fun i j hij => by
        apply recoveredCoordinateEquiv.injective
        rw [recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply, hp.orthogonal i j hij, map_zero]
      sum_unit := by
        rw [← map_sum, Fin.sum_univ_three, hp.sum_unit, ← recoveredCoordinateEquiv_unit,
          LinearEquiv.symm_apply_apply] }
  obtain ⟨f, hf⟩ := AlbertSequential.native_frame_to_standardFrame F
  refine ⟨AlbertSequential.nativeAutoToCompactAuto f, fun i => ?_⟩
  rw [AlbertSequential.nativeAutoToCompactAuto_apply, ← recovered_diagonalAtom i]
  exact congrArg recoveredCoordinateEquiv (hf i)

private theorem native_diagonal_of_unbiased (x : Glennie.Albert)
    (h : ∀ i, Glennie.inner (Glennie.standardFrame i) x = 1 / 3) :
    x.d0 = 1 / 3 ∧ x.d1 = 1 / 3 ∧ x.d2 = 1 / 3 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Glennie.inner_coordinates, Glennie.standardFrame, Glennie.octDot_coordinates] using h 0
  · simpa [Glennie.inner_coordinates, Glennie.standardFrame, Glennie.octDot_coordinates] using h 1
  · simpa [Glennie.inner_coordinates, Glennie.standardFrame, Glennie.octDot_coordinates] using h 2

private theorem native_balanced_slot_norms (p : Glennie.Albert) (hp : Glennie.jordan p p = p)
    (h0 : p.d0 = 1 / 3) (h1 : p.d1 = 1 / 3) (h2 : p.d2 = 1 / 3) :
    Glennie.octNormSq p.o01 = 1 / 9 ∧ Glennie.octNormSq p.o02 = 1 / 9 ∧
      Glennie.octNormSq p.o12 = 1 / 9 := by
  have e0 := congrArg Glennie.Albert.d0 hp
  have e1 := congrArg Glennie.Albert.d1 hp
  have e2 := congrArg Glennie.Albert.d2 hp
  simp only [Glennie.jordan_d0, h0, Glennie.octDot_self] at e0
  simp only [Glennie.jordan_d1, h1, Glennie.octDot_self] at e1
  simp only [Glennie.jordan_d2, h2, Glennie.octDot_self] at e2
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem native_balanced_slot_product (p : Glennie.Albert) (hp : Glennie.jordan p p = p)
    (h0 : p.d0 = 1 / 3) (h2 : p.d2 = 1 / 3) :
    p.o02 = (3 : ℝ) • Glennie.octMul p.o01 p.o12 := by
  have e := congrArg Glennie.Albert.o02 hp
  simp only [Glennie.jordan_o02, h0, h2] at e
  linear_combination (norm := module) (-3 : ℝ) • e

/-- The first Fourier projector, with every entry equal to one third. -/
def nativeFourierZero : Glennie.Albert :=
  ⟨1/3, 1/3, 1/3, (1/3 : ℝ) • Glennie.octScalar 1,
    (1/3 : ℝ) • Glennie.octScalar 1, (1/3 : ℝ) • Glennie.octScalar 1⟩

private theorem native_slot_product (x y : Glennie.Octonion) :
    Glennie.jordan (⟨0, 0, 0, x, 0, 0⟩ : Glennie.Albert) ⟨0, 0, 0, 0, 0, y⟩ =
      (1 / 2 : ℝ) • (⟨0, 0, 0, 0, Glennie.octMul x y, 0⟩ : Glennie.Albert) := by
  have h := congrArg recoveredCoordinateEquiv (AlbertSequential.jordanMul_slotElem01_slotElem12 x y)
  rw [recoveredCoordinateEquiv_jordanMul, map_smul] at h
  exact h

private theorem native_normSq_smul (r : ℝ) (x : Glennie.Octonion) :
    Glennie.octNormSq (r • x) = r ^ 2 * Glennie.octNormSq x := by
  simp [Glennie.octNormSq, Quaternion.normSq_def']
  ring

private theorem native_normSq_neg (x : Glennie.Octonion) :
    Glennie.octNormSq (-x) = Glennie.octNormSq x := by
  simp [Glennie.octNormSq, Quaternion.normSq_def']

private theorem native_balanced_to_fourier_zero (p : Glennie.Albert) (hp : Glennie.jordan p p = p)
    (h0 : p.d0 = 1 / 3) (h1 : p.d1 = 1 / 3) (h2 : p.d2 = 1 / 3) :
    ∃ g : Glennie.CompactAutomorphism,
      (∀ i, g.equiv (Glennie.standardFrame i) = Glennie.standardFrame i) ∧
      g.equiv p = nativeFourierZero := by
  let x := (3 : ℝ) • p.o01
  let y := (3 : ℝ) • p.o12
  obtain ⟨h01, _, h12⟩ := native_balanced_slot_norms p hp h0 h1 h2
  have hx : Glennie.octNormSq x = 1 := by
    rw [show x = (3 : ℝ) • p.o01 from rfl, native_normSq_smul, h01]
    norm_num
  have hy : Glennie.octNormSq y = 1 := by
    rw [show y = (3 : ℝ) • p.o12 from rfl, native_normSq_smul, h12]
    norm_num
  obtain ⟨g, hg, hgx, hgy⟩ := native_normalize_two_slots x y hx hy
  let A : Glennie.Albert := ⟨0, 0, 0, x, 0, 0⟩
  let B : Glennie.Albert := ⟨0, 0, 0, 0, 0, y⟩
  let A₀ : Glennie.Albert := ⟨0, 0, 0, Glennie.octScalar 1, 0, 0⟩
  let B₀ : Glennie.Albert := ⟨0, 0, 0, 0, 0, Glennie.octScalar 1⟩
  have hp' : p = (1 / 3 : ℝ) • (1 + A + B + (2 : ℝ) • Glennie.jordan A B) := by
    rw [show Glennie.jordan A B = _ from native_slot_product x y, smul_smul,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
    apply Glennie.Albert.ext
    · change p.d0 = (1 / 3) * (1 + 0 + 0 + 0)
      linarith
    · change p.d1 = (1 / 3) * (1 + 0 + 0 + 0)
      linarith
    · change p.d2 = (1 / 3) * (1 + 0 + 0 + 0)
      linarith
    · change p.o01 = (1 / 3 : ℝ) • (0 + x + 0 + 0)
      simp [x, smul_smul]
    · change p.o02 = (1 / 3 : ℝ) • (0 + 0 + 0 + Glennie.octMul x y)
      simp only [zero_add, x, y, Glennie.octMul_smul_left, Glennie.octMul_smul_right, smul_smul]
      convert native_balanced_slot_product p hp h0 h2 using 2; norm_num
    · change p.o12 = (1 / 3 : ℝ) • (0 + 0 + y + 0)
      simp [y, smul_smul]
  refine ⟨g, hg, ?_⟩
  rw [hp', map_smul, map_add, map_add, map_add, map_smul, g.map_unit, g.map_jordan,
    show g.equiv A = A₀ from hgx, show g.equiv B = B₀ from hgy,
    show Glennie.jordan A₀ B₀ = _ from native_slot_product _ _,
    Glennie.octMul_scalar_left, one_smul, smul_smul,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
  apply Glennie.Albert.ext
  · change (1 / 3 : ℝ) * (1 + 0 + 0 + 0) = 1 / 3
    norm_num
  · change (1 / 3 : ℝ) * (1 + 0 + 0 + 0) = 1 / 3
    norm_num
  · change (1 / 3 : ℝ) * (1 + 0 + 0 + 0) = 1 / 3
    norm_num
  · change (1 / 3 : ℝ) • (0 + Glennie.octScalar 1 + 0 + 0) = _
    simp [nativeFourierZero]
  · change (1 / 3 : ℝ) • (0 + 0 + 0 + Glennie.octScalar 1) = _
    simp [nativeFourierZero]
  · change (1 / 3 : ℝ) • (0 + 0 + Glennie.octScalar 1 + 0) = _
    simp [nativeFourierZero]

private theorem native_dot_scalar (x : Glennie.Octonion) (r : ℝ) :
    Glennie.octDot (r • Glennie.octScalar 1) x = r * Glennie.octRe x := by
  rw [Glennie.octDot_coordinates]
  simp [Glennie.octScalar, Glennie.octRe]

/-- The Fourier projector whose (0,1) and (1,2) entries equal `(-1 + √3 u)/6`. -/
def nativeFourierPhase (u : Glennie.Octonion) : Glennie.Albert :=
  let a := (-1 / 6 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 6) • u
  ⟨1 / 3, 1 / 3, 1 / 3, a, Glennie.octConj a, a⟩

private theorem native_balanced_orthogonal_slice (p : Glennie.Albert) (hp : Glennie.jordan p p = p)
    (h0 : p.d0 = 1 / 3) (h1 : p.d1 = 1 / 3) (h2 : p.d2 = 1 / 3)
    (ho : Glennie.jordan nativeFourierZero p = 0) :
    ∃ u : Glennie.Octonion, Glennie.octRe u = 0 ∧ Glennie.octNormSq u = 1 ∧
      p = nativeFourierPhase u := by
  have e0 := congrArg Glennie.Albert.d0 ho
  have e1 := congrArg Glennie.Albert.d1 ho
  have e2 := congrArg Glennie.Albert.d2 ho
  simp only [Glennie.jordan_d0, Glennie.jordan_d1, Glennie.jordan_d2,
    nativeFourierZero, native_dot_scalar, h0, h1, h2] at e0 e1 e2
  change _ = (0 : ℝ) at e0 e1 e2
  have r01 : Glennie.octRe p.o01 = -1 / 6 := by linarith
  have r12 : Glennie.octRe p.o12 = -1 / 6 := by linarith
  have hconj (z : Glennie.Octonion) (h : Glennie.octRe z = -1 / 6) :
      Glennie.octConj z = (-1 / 3 : ℝ) • Glennie.octScalar 1 - z := by
    have hsum := Glennie.octAdd_conj z
    rw [h, show Glennie.octScalar (-1 / 6) = (-1 / 6 : ℝ) • Glennie.octScalar 1
      from AlbertSequential.octonionScalar_eq_smul _, smul_smul] at hsum
    linear_combination (norm := module) hsum
  have e01 := congrArg Glennie.Albert.o01 ho
  have e02 := congrArg Glennie.Albert.o02 ho
  have e12 := congrArg Glennie.Albert.o12 ho
  change _ = (0 : Glennie.Octonion) at e01 e02 e12
  simp only [Glennie.jordan_o01, nativeFourierZero, h0, h1, Glennie.octMul_smul_left,
    Glennie.octMul_smul_right, Glennie.octMul_scalar_left, Glennie.octMul_scalar_right,
    Glennie.octConj_smul, Glennie.octConj_scalar, one_smul, hconj _ r12] at e01
  simp only [Glennie.jordan_o02, nativeFourierZero, h0, h2, Glennie.octMul_smul_left,
    Glennie.octMul_smul_right, Glennie.octMul_scalar_left, Glennie.octMul_scalar_right,
    one_smul] at e02
  simp only [Glennie.jordan_o12, nativeFourierZero, h1, h2, Glennie.octMul_smul_left,
    Glennie.octMul_smul_right, Glennie.octMul_scalar_left, Glennie.octMul_scalar_right,
    Glennie.octConj_smul, Glennie.octConj_scalar, one_smul, hconj _ r01] at e12
  have hy : p.o12 = p.o01 := by
    linear_combination (norm := module) (2 : ℝ) • e12 - (2 : ℝ) • e01
  have hz : p.o02 = Glennie.octConj p.o01 := by
    rw [hconj _ r01]
    rw [hy] at e02
    linear_combination (norm := module) (3 : ℝ) • e02
  let w : Glennie.Octonion := p.o01 - Glennie.octScalar (Glennie.octRe p.o01)
  let u : Glennie.Octonion := (2 * Real.sqrt 3) • w
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hu₀ : Glennie.octRe u = 0 := by
    change (2 * Real.sqrt 3) * (p.o01.1.re - p.o01.1.re) = 0
    ring
  have hn := (native_balanced_slot_norms p hp h0 h1 h2).1
  have hni : Glennie.octNormSq w = 1 / 12 := by
    change p.o01.1.re = -1 / 6 at r01
    simp [w, Glennie.octNormSq, Quaternion.normSq_def', Glennie.octScalar, Glennie.octRe] at hn ⊢
    nlinarith
  have hu₁ : Glennie.octNormSq u = 1 := by
    rw [show u = (2 * Real.sqrt 3) • w from rfl, native_normSq_smul, hni]
    nlinarith
  have hx : p.o01 = (-1 / 6 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 6) • u := by
    dsimp only [u, w]
    rw [r01, show Glennie.octScalar (-1 / 6) = (-1 / 6 : ℝ) • Glennie.octScalar 1
      from AlbertSequential.octonionScalar_eq_smul _]
    have hc : (Real.sqrt 3 / 6) * (2 * Real.sqrt 3) = 1 := by nlinarith
    rw [smul_smul, hc, one_smul]
    abel
  refine ⟨u, hu₀, hu₁, Glennie.Albert.ext h0 h1 h2 hx ?_ ?_⟩
  · change p.o02 = Glennie.octConj ((-1 / 6 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 6) • u)
    rw [hz, ← hx]
  · exact hy.trans hx

/-- The Fourier frame in the complex slice generated by `u`, ordered by exponents 0, 1, 2. -/
def nativeFourierFrame (u : Glennie.Octonion) : Fin 3 → Glennie.Albert :=
  ![nativeFourierZero, nativeFourierPhase (-u), nativeFourierPhase u]

private theorem nativeFourier_sum (u : Glennie.Octonion) (hu : Glennie.octRe u = 0) :
    nativeFourierZero + nativeFourierPhase (-u) + nativeFourierPhase u = 1 := by
  have h : Glennie.octConj u = -u := AlbertSequential.octonionConj_eq_neg_of_real_zero hu
  apply Glennie.Albert.ext
  · change (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1
    norm_num
  · change (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1
    norm_num
  · change (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1
    norm_num
  · change (1 / 3 : ℝ) • Glennie.octScalar 1 + _ + _ = (0 : Glennie.Octonion)
    unfold nativeFourierPhase
    change (1 / 3 : ℝ) • Glennie.octScalar 1 +
      ((-1 / 6 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 6) • (-u)) +
      ((-1 / 6 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 6) • u) = 0
    module
  · change (1 / 3 : ℝ) • Glennie.octScalar 1 +
      Glennie.octConj ((-1 / 6 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 6) • (-u)) +
      Glennie.octConj ((-1 / 6 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 6) • u) = 0
    simp only [Glennie.octConj_add, Glennie.octConj_smul, Glennie.octConj_scalar,
      show Glennie.octConj (-u) = -Glennie.octConj u from map_neg Glennie.octConjAddHom u, h]
    module
  · change (1 / 3 : ℝ) • Glennie.octScalar 1 +
      ((-1 / 6 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 6) • (-u)) +
      ((-1 / 6 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 6) • u) = 0
    module

set_option maxHeartbeats 1000000 in
/-- Every unbiased pair of compact Albert frames is carried by an actual automorphism
to the diagonal and Fourier frames in a single unit-imaginary complex slice. -/
theorem native_normalize_unbiased_pair (p q : Fin 3 → Glennie.Albert)
    (hp : Glennie.Frame p) (hq : Glennie.Frame q)
    (unbiased : ∀ i j, Glennie.inner (p i) (q j) = 1 / 3) :
    ∃ (g : Glennie.CompactAutomorphism) (u : Glennie.Octonion),
      Glennie.octRe u = 0 ∧ Glennie.octNormSq u = 1 ∧
      (∀ i, g.equiv (p i) = Glennie.standardFrame i) ∧
      (∀ i, g.equiv (q i) = nativeFourierFrame u i) := by
  obtain ⟨f, hf⟩ := native_frame_to_diagonal p hp
  have hqd (j : Fin 3) :
      ∀ i, Glennie.inner (Glennie.standardFrame i) (f.equiv (q j)) = 1 / 3 := by
    intro i
    rw [← hf, f.inner_map]
    exact unbiased i j
  obtain ⟨h0, h1, h2⟩ := native_diagonal_of_unbiased _ (hqd 0)
  obtain ⟨g, hg, hgp⟩ := native_balanced_to_fourier_zero _ ((f.map_frame q hq).idempotent 0) h0 h1 h2
  let φ := g.comp f
  have hφ (i : Fin 3) : φ.equiv (p i) = Glennie.standardFrame i := by
    rw [show φ = g.comp f from rfl, Glennie.CompactAutomorphism.comp_apply, hf, hg]
  have hq₀ : φ.equiv (q 0) = nativeFourierZero := hgp
  have hq' := φ.map_frame q hq
  have hdiag : ∀ i, Glennie.inner (Glennie.standardFrame i) (φ.equiv (q 1)) = 1 / 3 := by
    intro i
    rw [← hφ, φ.inner_map]
    exact unbiased i 1
  obtain ⟨d0, d1, d2⟩ := native_diagonal_of_unbiased _ hdiag
  have hmul : Glennie.jordan nativeFourierZero (φ.equiv (q 1)) = 0 := by
    rw [← hq₀]
    exact hq'.orthogonal 0 1 (by decide)
  obtain ⟨v, hv, hn, hq₁⟩ := native_balanced_orthogonal_slice _ (hq'.idempotent 1) d0 d1 d2 hmul
  let u := -v
  have hu : Glennie.octRe u = 0 := by
    change -Glennie.octRe v = 0
    exact neg_eq_zero.mpr hv
  have hun : Glennie.octNormSq u = 1 := by
    rw [show u = -v from rfl, native_normSq_neg]
    exact hn
  have hq₁' : φ.equiv (q 1) = nativeFourierPhase (-u) := by
    rw [hq₁, show -u = v from neg_neg v]
  have hq₂ : φ.equiv (q 2) = nativeFourierPhase u := by
    have hs := hq'.sum_unit
    change φ.equiv (q 0) + φ.equiv (q 1) + φ.equiv (q 2) = 1 at hs
    rw [hq₀, hq₁'] at hs
    exact add_left_cancel (hs.trans (nativeFourier_sum u hu).symm)
  refine ⟨φ, u, hu, hun, hφ, fun i => ?_⟩
  fin_cases i
  · exact hq₀
  · exact hq₁'
  · exact hq₂

end
end ThirteenPlanes.JordanFrames
