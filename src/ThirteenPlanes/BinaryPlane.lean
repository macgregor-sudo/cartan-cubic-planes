module

public import ThirteenPlanes.RoundContractions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-! The orthonormal complex normal form of a round binary cubic. -/

open scoped InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.RoundCubics

open SymmetricCubic PlaneContractions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {h : SymmetricCubic V} {c : ℝ}

/-- The binary cubic normal form. A round real plane has a harmonic cubic and an
orthonormal complex coordinate in which its cubic is `√c * Re(z³)`. -/
theorem binaryPlaneNormalForm (round : IsRound h c) (hdim : Module.finrank ℝ V = 2) :
    h.TraceFree ∧ ∃ z : V ≃ₗᵢ[ℝ] ℂ, ∀ x : V,
      h.apply x x x = Real.sqrt c * ((z x) ^ 3).re := by
  let e := (stdOrthonormalBasis ℝ V).reindex (finCongr hdim)
  let a := h.apply (e 0) (e 0) (e 0)
  let b := h.apply (e 0) (e 0) (e 1)
  have tf := traceFree_of_round_finrank_two round hdim
  have hb₁ : h.apply (e 0) (e 1) (e 0) = b := h.apply_swap₂₃ _ _ _
  have hb₂ : h.apply (e 1) (e 0) (e 0) = b := (h.apply_swap₁₂ _ _ _).trans hb₁
  have hd : h.apply (e 0) (e 1) (e 1) = -a := by
    have ht := tf (e 0)
    rw [← sum_apply_diag e, Fin.sum_univ_two] at ht
    change a + h.apply (e 0) (e 1) (e 1) = 0 at ht
    linarith
  have hd₁ : h.apply (e 1) (e 0) (e 1) = -a := (h.apply_swap₁₂ _ _ _).trans hd
  have hd₂ : h.apply (e 1) (e 1) (e 0) = -a := (h.apply_swap₂₃ _ _ _).trans hd₁
  have hf : h.apply (e 1) (e 1) (e 1) = -b := by
    have ht := tf (e 1)
    rw [← sum_apply_diag e, Fin.sum_univ_two, hb₂] at ht
    linarith
  have hab : a ^ 2 + b ^ 2 = c := by
    have hs := round.square_norm (e 0)
    rw [squareMap, ← real_inner_self_eq_norm_sq, ← sum_inner_mul_inner' e,
      Fin.sum_univ_two, e.orthonormal.1 0] at hs
    change a * a + b * b = c * 1 ^ 4 at hs
    nlinarith only [hs]
  let α : ℂ := ⟨a, -b⟩
  have hα : ‖α‖ = Real.sqrt c := by
    have hsq : ‖α‖ ^ 2 = c := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      change a * a + (-b) * (-b) = c
      nlinarith only [hab]
    rw [← Real.sqrt_sq (norm_nonneg α), hsq]
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 round.positive
  have hunit : ‖α / (Real.sqrt c : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, hα, div_self hs.ne']
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (α / (Real.sqrt c : ℂ)) (n := 3) (by decide)
  have hu_norm : ‖u‖ = 1 := by
    apply (pow_left_inj₀ (norm_nonneg u) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp
    rw [← norm_pow, hu, hunit, one_pow]
  let phase : Circle := ⟨u, mem_sphere_zero_iff_norm.2 hu_norm⟩
  let f : V ≃ₗᵢ[ℝ] ℂ := e.repr.trans Complex.orthonormalBasisOneI.repr.symm
  refine ⟨tf, f.trans (rotation phase), fun x => ?_⟩
  let p := e.repr x 0
  let q := e.repr x 1
  have hx : p • e 0 + q • e 1 = x := by
    simpa only [Fin.sum_univ_two, p, q] using e.sum_repr x
  have hcoords := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v.ofLp)
    (show Complex.orthonormalBasisOneI.repr (f x) = e.repr x from
      Complex.orthonormalBasisOneI.repr.apply_symm_apply _)
  rw [Complex.orthonormalBasisOneI_repr_apply] at hcoords
  have hp : (f x).re = p := congrArg (fun v : Fin 2 → ℝ => v 0) hcoords
  have hq : (f x).im = q := congrArg (fun v : Fin 2 → ℝ => v 1) hcoords
  have heval : h.apply x x x = a * (p ^ 3 - 3 * p * q ^ 2) + b * (3 * p ^ 2 * q - q ^ 3) := by
    rw [← hx]
    have ha : h.apply (e 0) (e 0) (e 0) = a := rfl
    have hb : h.apply (e 0) (e 0) (e 1) = b := rfl
    simp only [apply_add₁, apply_add₂, apply_add₃, apply_smul₁, apply_smul₂, apply_smul₃,
      ha, hb, hb₁, hb₂, hd, hd₁, hd₂, hf]
    ring
  have hre : (α * (f x) ^ 3).re =
      a * (p ^ 3 - 3 * p * q ^ 2) + b * (3 * p ^ 2 * q - q ^ 3) := by
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, hp, hq, α]
    ring
  have hscale : (Real.sqrt c : ℂ) * (α / (Real.sqrt c : ℂ)) = α := by
    rw [mul_comm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hs.ne')]
  calc
    _ = (α * (f x) ^ 3).re := heval.trans hre.symm
    _ = ((Real.sqrt c : ℂ) * ((rotation phase (f x)) ^ 3)).re := by
      rw [rotation_apply, mul_pow, show (phase : ℂ) ^ 3 = α / (Real.sqrt c : ℂ) from hu,
        ← mul_assoc, hscale]
    _ = _ := by simp [Complex.mul_re]

end ThirteenPlanes.RoundCubics
