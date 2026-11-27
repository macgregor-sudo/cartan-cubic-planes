module

public import ThirteenPlanes.SphereVariance
public import ThirteenPlanes.AllCubicSquares

@[expose] public section

/-!
# The variances of the harmonic parts of the field energy

For a real symmetric cubic `h` in `n ≥ 1` variables, the field energy `U = ‖Q_h‖²/8` on the unit
sphere is `σ/(8n(n+2)) + U₂ + U₄`, with harmonic parts of degree two and four
`U₂ = Σ̊(φ,φ)/(4(n+4))` and `U₄ = H(φ⁴)/24` (`energy_decomp`). Both have sphere mean zero, they are
uncorrelated, and their variances are

  `Var₂ = |Σ̊|²/(8n(n+2)(n+4)²)`,   `Var₄ = |H|²/(24n(n+2)(n+4)(n+6))`.

With these, the five-square identity reads

  `A(h) − A* = (n+10)/(8n(n+2)) (x−x*)² + |v|²(4x+|v|²)/(4n(n+2)) + |M̊|²/8
               + 4n(n+2)(n+4) Var₂ + 2n(n+2)(n+4)(n+6) Var₄`.
-/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open Quartic Coords SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Nontrivial V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

namespace SymmetricCubic

/-- The degree-two harmonic part `Σ̊(φ,φ)/(4(n+4))` of the field energy. -/
def energyPart2 (h : SymmetricCubic V) (y : V) : ℝ :=
  1 / (4 * (Module.finrank ℝ V + 4)) * quadraticForm e (h.sigTraceless e) y

/-- The degree-four harmonic part `H(φ⁴)/24` of the field energy. -/
def energyPart4 (h : SymmetricCubic V) (y : V) : ℝ :=
  1 / 24 * quarticForm e (h.harmQuartic e) y

end SymmetricCubic

/-- On the unit sphere the field energy is its mean plus its harmonic parts of degrees two and
four. -/
theorem energy_eq_mean_add_parts (h : SymmetricCubic V) (y : V) (hy : ‖y‖ = 1) :
    ‖h.squareMap y‖ ^ 2 / 8 =
      sphereAverage (fun y => ‖h.squareMap y‖ ^ 2 / 8) + h.energyPart2 e y + h.energyPart4 e y := by
  rw [energy_on_sphere_decomp e h y hy, sphereAverage_energy e h]
  simp only [SymmetricCubic.energyPart2, SymmetricCubic.energyPart4]
  ring

/-- The degree-two harmonic part has sphere mean zero. -/
theorem sphereAverage_energyPart2 (h : SymmetricCubic V) :
    sphereAverage (h.energyPart2 e) = 0 := by
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hne : Nonempty ι := by
    rw [Module.finrank_eq_card_basis e.toBasis] at hn; exact Fintype.card_pos_iff.mp hn
  have hdim : dim ι ≠ 0 := (dim_pos (ι := ι)).ne'
  have hc := coefficient_symm e h
  have hBs : MSymm (h.sigTraceless e) := sig0_symm (sq4_symm hc)
  have hHq : QSymm (h.harmQuartic e) := harm_symm (sq4_symm hc)
  have hHs := (qsymm_iff_isSymmetric4 _).mp hHq
  have hH0 := (isTraceFree4_iff_contr hHq).mpr (contr_harm (sq4_symm hc))
  have hBt : ∑ t, h.sigTraceless e t t = 0 := mtrace_traceless hdim
  have hN : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast hn
  unfold SymmetricCubic.energyPart2
  rw [sphereAverage_const_mul, sphereAverage_quadraticForm, hBt]
  simp

/-- The degree-four harmonic part has sphere mean zero. -/
theorem sphereAverage_energyPart4 (h : SymmetricCubic V) :
    sphereAverage (h.energyPart4 e) = 0 := by
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hne : Nonempty ι := by
    rw [Module.finrank_eq_card_basis e.toBasis] at hn; exact Fintype.card_pos_iff.mp hn
  have hdim : dim ι ≠ 0 := (dim_pos (ι := ι)).ne'
  have hc := coefficient_symm e h
  have hBs : MSymm (h.sigTraceless e) := sig0_symm (sq4_symm hc)
  have hHq : QSymm (h.harmQuartic e) := harm_symm (sq4_symm hc)
  have hHs := (qsymm_iff_isSymmetric4 _).mp hHq
  have hH0 := (isTraceFree4_iff_contr hHq).mpr (contr_harm (sq4_symm hc))
  have hBt : ∑ t, h.sigTraceless e t t = 0 := mtrace_traceless hdim
  have hN : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast hn
  unfold SymmetricCubic.energyPart4
  rw [sphereAverage_const_mul, sphereAverage_quarticForm_traceFree e hHs hH0, mul_zero]

/-- The two harmonic parts are uncorrelated on the sphere. -/
theorem sphereAverage_energyPart2_mul_energyPart4 (h : SymmetricCubic V) :
    sphereAverage (fun y => h.energyPart2 e y * h.energyPart4 e y) = 0 := by
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hne : Nonempty ι := by
    rw [Module.finrank_eq_card_basis e.toBasis] at hn; exact Fintype.card_pos_iff.mp hn
  have hdim : dim ι ≠ 0 := (dim_pos (ι := ι)).ne'
  have hc := coefficient_symm e h
  have hBs : MSymm (h.sigTraceless e) := sig0_symm (sq4_symm hc)
  have hHq : QSymm (h.harmQuartic e) := harm_symm (sq4_symm hc)
  have hHs := (qsymm_iff_isSymmetric4 _).mp hHq
  have hH0 := (isTraceFree4_iff_contr hHq).mpr (contr_harm (sq4_symm hc))
  have hBt : ∑ t, h.sigTraceless e t t = 0 := mtrace_traceless hdim
  have hN : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast hn
  have hfun : (fun y => h.energyPart2 e y * h.energyPart4 e y) = fun y =>
      (1 / (4 * (Module.finrank ℝ V + 4)) * (1 / 24)) *
        (quarticForm e (h.harmQuartic e) y * quadraticForm e (h.sigTraceless e) y) := by
    funext y; simp only [SymmetricCubic.energyPart2, SymmetricCubic.energyPart4]; ring
  rw [hfun, sphereAverage_const_mul, sphereAverage_quarticForm_mul_quadraticForm e hHs hH0,
    mul_zero]

/-- `Var₂ = |Σ̊|²/(8n(n+2)(n+4)²)`. -/
theorem sphereVariance_energyPart2 (h : SymmetricCubic V) :
    sphereVariance (h.energyPart2 e) =
      minner (h.sigTraceless e) (h.sigTraceless e) /
        (8 * Module.finrank ℝ V * (Module.finrank ℝ V + 2) * (Module.finrank ℝ V + 4) ^ 2) := by
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hne : Nonempty ι := by
    rw [Module.finrank_eq_card_basis e.toBasis] at hn; exact Fintype.card_pos_iff.mp hn
  have hdim : dim ι ≠ 0 := (dim_pos (ι := ι)).ne'
  have hc := coefficient_symm e h
  have hBs : MSymm (h.sigTraceless e) := sig0_symm (sq4_symm hc)
  have hHq : QSymm (h.harmQuartic e) := harm_symm (sq4_symm hc)
  have hHs := (qsymm_iff_isSymmetric4 _).mp hHq
  have hH0 := (isTraceFree4_iff_contr hHq).mpr (contr_harm (sq4_symm hc))
  have hBt : ∑ t, h.sigTraceless e t t = 0 := mtrace_traceless hdim
  have hN : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast hn
  set B := h.sigTraceless e
  unfold sphereVariance
  rw [sphereAverage_energyPart2 e h]
  have hfun : (fun y => (h.energyPart2 e y - 0) ^ 2) = fun y =>
      (1 / (4 * (Module.finrank ℝ V + 4))) ^ 2 * (quadraticForm e B y * quadraticForm e B y) := by
    funext y; simp only [SymmetricCubic.energyPart2, B]; ring
  rw [hfun, sphereAverage_const_mul, sphereAverage_quadraticForm_mul]
  have hsum : ∑ w, ∑ t, (B t t * B w w + B t w * B t w + B t w * B w t) = 2 * minner B B := by
    have e0 : ∑ w, ∑ t, B t t * B w w = 0 := by
      simp only [← Finset.sum_mul, hBt, zero_mul, Finset.sum_const_zero]
    have e1 : ∀ w t, B t t * B w w + B t w * B t w + B t w * B w t =
        B t t * B w w + 2 * (B t w * B t w) := by
      intro w t; rw [hBs w t]; ring
    have e2 : ∑ w, ∑ t, B t w * B t w = ∑ i, ∑ j, B i j * B i j := Finset.sum_comm
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, e0, zero_add, minner]
    rw [e2]
  rw [hsum]
  field_simp
  ring

/-- `Var₄ = |H|²/(24n(n+2)(n+4)(n+6))`. -/
theorem sphereVariance_energyPart4 (h : SymmetricCubic V) :
    sphereVariance (h.energyPart4 e) =
      qinner (h.harmQuartic e) (h.harmQuartic e) /
        (24 * Module.finrank ℝ V * (Module.finrank ℝ V + 2) * (Module.finrank ℝ V + 4) *
          (Module.finrank ℝ V + 6)) := by
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hne : Nonempty ι := by
    rw [Module.finrank_eq_card_basis e.toBasis] at hn; exact Fintype.card_pos_iff.mp hn
  have hdim : dim ι ≠ 0 := (dim_pos (ι := ι)).ne'
  have hc := coefficient_symm e h
  have hBs : MSymm (h.sigTraceless e) := sig0_symm (sq4_symm hc)
  have hHq : QSymm (h.harmQuartic e) := harm_symm (sq4_symm hc)
  have hHs := (qsymm_iff_isSymmetric4 _).mp hHq
  have hH0 := (isTraceFree4_iff_contr hHq).mpr (contr_harm (sq4_symm hc))
  have hBt : ∑ t, h.sigTraceless e t t = 0 := mtrace_traceless hdim
  have hN : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast hn
  set H := h.harmQuartic e
  unfold sphereVariance
  rw [sphereAverage_energyPart4 e h]
  have hfun : (fun y => (h.energyPart4 e y - 0) ^ 2) = fun y =>
      (1 / 24) ^ 2 * (quarticForm e H y * quarticForm e H y) := by
    funext y; simp only [SymmetricCubic.energyPart4, H]; ring
  rw [hfun, sphereAverage_const_mul, sphereAverage_quarticForm_mul_quarticForm e hHs hH0 hHs]
  simp only [qinner]
  field_simp

/-- The five squares with the last two written as variances of the harmonic parts:
`A(h) − A* = (n+10)/(8n(n+2)) (x−x*)² + |v|²(4x+|v|²)/(4n(n+2)) + |M̊|²/8
+ 4n(n+2)(n+4) Var₂ + 2n(n+2)(n+4)(n+6) Var₄`. -/
theorem aFunction_sub_floor_variances (h : SymmetricCubic V) :
    let n : ℝ := Module.finrank ℝ V
    let x := h.tensorPairing h
    let w := vinner (h.traceVec e) (h.traceVec e)
    aFunction h - floorValue n =
      (n + 10) / (8 * n * (n + 2)) * (x - floorStrength n) ^ 2 +
        w * (4 * x + w) / (4 * n * (n + 2)) +
        minner (h.mTraceless e) (h.mTraceless e) / 8 +
        4 * n * (n + 2) * (n + 4) * sphereVariance (h.energyPart2 e) +
        2 * n * (n + 2) * (n + 4) * (n + 6) * sphereVariance (h.energyPart4 e) := by
  intro n x w
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hN : (0 : ℝ) < n := by simp only [n]; exact_mod_cast hn
  have key := aFunction_sub_floor e hn h
  simp only at key
  rw [key, sphereVariance_energyPart2, sphereVariance_energyPart4]
  have h2 : n + 2 ≠ 0 := by linarith
  have h4 : n + 4 ≠ 0 := by linarith
  have h6 : n + 6 ≠ 0 := by linarith
  field_simp
  ring

end

end ThirteenPlanes
