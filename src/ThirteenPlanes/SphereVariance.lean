module

public import ThirteenPlanes.AllCubicSquares
public import ThirteenPlanes.SphereMoments

@[expose] public section

/-!
# Sphere variance of the field energy of an arbitrary cubic

For every real symmetric cubic `h` in `n ≥ 1` variables, with `Σ̊` the traceless part of the
contraction `S_ijkk` of the symmetrized quartic tensor and `H` its totally traceless part, the
variance of `U = ‖Q_h‖²/8` over the unit sphere is

  `Var(U) = |Σ̊|² / (8 n (n+2) (n+4)²) + |H|² / (24 n (n+2) (n+4) (n+6))`,

and its mean is `σ/(8n(n+2))`, `σ = 2⟨h,h⟩ + |v|²`. The proof uses the pointwise harmonic splitting
`energy_decomp`, the orthogonality of the degree-two and degree-four parts on the sphere, and the
second moments of a traceless quadratic and a harmonic quartic form.
-/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open Quartic Coords SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Nontrivial V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

omit [Nontrivial V] [DecidableEq ι] [FiniteDimensional ℝ V] in
theorem continuous_quadraticForm (B : ι → ι → ℝ) : Continuous (quadraticForm e B) := by
  unfold quadraticForm; fun_prop

/-- On the unit sphere the field energy is `σ/(8n(n+2)) + Σ̊(x,x)/(4(n+4)) + H(x⁴)/24`. -/
theorem energy_on_sphere_decomp (h : SymmetricCubic V) (y : V) (hy : ‖y‖ = 1) :
    ‖h.squareMap y‖ ^ 2 / 8 =
      (2 * h.tensorPairing h + vinner (h.traceVec e) (h.traceVec e)) /
          (8 * Module.finrank ℝ V * (Module.finrank ℝ V + 2)) +
        (1 / (4 * (Module.finrank ℝ V + 4)) * quadraticForm e (h.sigTraceless e) y +
          1 / 24 * quarticForm e (h.harmQuartic e) y) := by
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  rw [energy_decomp e hn h y, hy]
  change _ = _ + (_ * form2 (h.sigTraceless e) (fun i => ⟪e i, y⟫) + _ * form4 _ _)
  ring

/-- **Mean of the field energy** of any cubic: `σ/(8n(n+2))`, `σ = 2⟨h,h⟩ + |v|²`. -/
theorem sphereAverage_energy (h : SymmetricCubic V) :
    sphereAverage (fun y => ‖h.squareMap y‖ ^ 2 / 8) =
      (2 * h.tensorPairing h + vinner (h.traceVec e) (h.traceVec e)) /
        (8 * Module.finrank ℝ V * (Module.finrank ℝ V + 2)) := by
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hne : Nonempty ι := by
    rw [Module.finrank_eq_card_basis e.toBasis] at hn; exact Fintype.card_pos_iff.mp hn
  have hdim : dim ι ≠ 0 := (dim_pos (ι := ι)).ne'
  have hc := coefficient_symm e h
  have hHq : QSymm (h.harmQuartic e) := harm_symm (sq4_symm hc)
  have hHs := (qsymm_iff_isSymmetric4 _).mp hHq
  have hH0 := (isTraceFree4_iff_contr hHq).mpr (contr_harm (sq4_symm hc))
  have hBt : ∑ t, h.sigTraceless e t t = 0 := mtrace_traceless hdim
  rw [sphereAverage_congr_sphere (energy_on_sphere_decomp e h)]
  have cB := continuous_quadraticForm e (h.sigTraceless e)
  have cH := continuous_quarticForm e (h.harmQuartic e)
  rw [sphereAverage_add (f := fun _ => (2 * h.tensorPairing h + vinner (h.traceVec e) (h.traceVec e)) /
        (8 * Module.finrank ℝ V * (Module.finrank ℝ V + 2)))
      (g := fun y => 1 / (4 * (Module.finrank ℝ V + 4)) * quadraticForm e (h.sigTraceless e) y +
        1 / 24 * quarticForm e (h.harmQuartic e) y) continuous_const
      ((continuous_const.mul cB).add (continuous_const.mul cH)),
    sphereAverage_add (f := fun y => 1 / (4 * (Module.finrank ℝ V + 4)) *
        quadraticForm e (h.sigTraceless e) y)
      (g := fun y => 1 / 24 * quarticForm e (h.harmQuartic e) y)
      (continuous_const.mul cB) (continuous_const.mul cH),
    sphereAverage_const, sphereAverage_const_mul, sphereAverage_const_mul,
    sphereAverage_quadraticForm, hBt, sphereAverage_quarticForm_traceFree e hHs hH0]
  ring

/-- **Variance of the field energy** of any cubic over the unit sphere:
`Var(‖Q_h‖²/8) = |Σ̊|²/(8n(n+2)(n+4)²) + |H|²/(24n(n+2)(n+4)(n+6))`. -/
/- The quartic tensor splitting used in the paper is described by Matthijs Hogervorst
and Chiara Toldo (arXiv:2010.16222, Eqs. (3.12)–(3.16)). The variance formula
here follows from the sphere moment identities for the explicit harmonic parts. -/
theorem sphereVariance_energy (h : SymmetricCubic V) :
    sphereVariance (fun y => ‖h.squareMap y‖ ^ 2 / 8) =
      minner (h.sigTraceless e) (h.sigTraceless e) /
          (8 * Module.finrank ℝ V * (Module.finrank ℝ V + 2) * (Module.finrank ℝ V + 4) ^ 2) +
        qinner (h.harmQuartic e) (h.harmQuartic e) /
          (24 * Module.finrank ℝ V * (Module.finrank ℝ V + 2) * (Module.finrank ℝ V + 4) *
            (Module.finrank ℝ V + 6)) := by
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hne : Nonempty ι := by
    rw [Module.finrank_eq_card_basis e.toBasis] at hn; exact Fintype.card_pos_iff.mp hn
  have hdim : dim ι ≠ 0 := (dim_pos (ι := ι)).ne'
  have hc := coefficient_symm e h
  set B := h.sigTraceless e
  set H := h.harmQuartic e
  have hBs : MSymm B := sig0_symm (sq4_symm hc)
  have hHq : QSymm H := harm_symm (sq4_symm hc)
  have hHs := (qsymm_iff_isSymmetric4 _).mp hHq
  have hH0 := (isTraceFree4_iff_contr hHq).mpr (contr_harm (sq4_symm hc))
  have hBt : ∑ t, B t t = 0 := mtrace_traceless hdim
  set N : ℝ := (Module.finrank ℝ V : ℝ)
  have hN : (0 : ℝ) < N := by simp only [N]; exact_mod_cast hn
  unfold sphereVariance
  rw [sphereAverage_energy e h]
  rw [sphereAverage_congr_sphere (g := fun y => 1 / (16 * (N + 4) ^ 2) *
      (quadraticForm e B y * quadraticForm e B y) +
      (1 / (48 * (N + 4)) * (quarticForm e H y * quadraticForm e B y) +
        1 / 576 * (quarticForm e H y * quarticForm e H y))) fun y hy => by
    simp only
    rw [energy_on_sphere_decomp e h y hy]
    simp only [B, H, N]
    have h4 : (Module.finrank ℝ V : ℝ) + 4 ≠ 0 := by positivity
    field_simp
    ring]
  have cB := continuous_quadraticForm e B
  have cH := continuous_quarticForm e H
  rw [sphereAverage_add (f := fun y => 1 / (16 * (N + 4) ^ 2) *
        (quadraticForm e B y * quadraticForm e B y))
      (g := fun y => 1 / (48 * (N + 4)) * (quarticForm e H y * quadraticForm e B y) +
        1 / 576 * (quarticForm e H y * quarticForm e H y))
      (continuous_const.mul (cB.mul cB))
      ((continuous_const.mul (cH.mul cB)).add (continuous_const.mul (cH.mul cH))),
    sphereAverage_add (f := fun y => 1 / (48 * (N + 4)) * (quarticForm e H y * quadraticForm e B y))
      (g := fun y => 1 / 576 * (quarticForm e H y * quarticForm e H y))
      (continuous_const.mul (cH.mul cB)) (continuous_const.mul (cH.mul cH)),
    sphereAverage_const_mul, sphereAverage_const_mul, sphereAverage_const_mul,
    sphereAverage_quadraticForm_mul, sphereAverage_quarticForm_mul_quadraticForm e hHs hH0,
    sphereAverage_quarticForm_mul_quarticForm e hHs hH0 hHs]
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
  simp only [qinner]
  field_simp
  ring

end

end ThirteenPlanes
