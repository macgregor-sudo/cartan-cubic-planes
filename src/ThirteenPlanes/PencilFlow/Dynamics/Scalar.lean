module

public import ThirteenPlanes.PencilFlow.TensorStatements

@[expose] public section

/-! Scalar facts for the Section 9 flow: the dimension of a closed plane system, the positivity
of `lam = (n - 2)/12`, the fixed ratios and the infrared exponent at the round point. -/

open Filter Set
open scoped Topology

namespace ThirteenPlanes.PencilFlow.Dynamics

noncomputable section

open Statements

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Two orthogonal two-planes already give four dimensions. -/
theorem four_le_finrank {m : ℕ} (hm : 2 ≤ m) (planes : PlaneDecomposition V (Fin m)) :
    4 ≤ Module.finrank ℝ V := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hortho := planes.pairwise_orthogonal hij
  have hdis : (planes.plane i) ⊓ (planes.plane j) = ⊥ := hortho.disjoint.eq_bot
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (planes.plane i) (planes.plane j)
  rw [hdis, finrank_bot, add_zero, planes.dimension, planes.dimension] at hsum
  have hle := Submodule.finrank_le ((planes.plane i) ⊔ (planes.plane j))
  omega

theorem four_le_finrank_real {m : ℕ} (hm : 2 ≤ m) (planes : PlaneDecomposition V (Fin m)) :
    (4 : ℝ) ≤ Module.finrank ℝ V := by
  exact_mod_cast four_le_finrank hm planes

theorem pencilLambda_pos {m : ℕ} (hm : 2 ≤ m) (planes : PlaneDecomposition V (Fin m)) :
    0 < pencilLambda V := by
  have := four_le_finrank_real hm planes
  unfold pencilLambda
  linarith

omit [FiniteDimensional ℝ V] in
theorem one_add_pencilLambda :
    1 + pencilLambda V = ((Module.finrank ℝ V : ℝ) + 10) / 12 := by
  unfold pencilLambda; ring

theorem ratioRate_eq (c lam g t : ℝ) :
    ratioRate c lam g t = 6 * c * g ^ 2 / flowScale * ratioPolynomial lam t := by
  unfold ratioRate ratioPolynomial; ring

theorem ratioRate_eq_zero_iff {c lam g t : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) (hg : g ≠ 0) :
    ratioRate c lam g t = 0 ↔ t = 0 ∨ t = 1 ∨ t = -1 / lam := by
  rw [ratioRate_eq, mul_eq_zero, ← ratioPolynomial_eq_zero_iff hlam]
  have : 6 * c * g ^ 2 / flowScale ≠ 0 := by
    have := flowScale_pos
    have : 0 < g ^ 2 := by positivity
    positivity
  simp [this]

end

end ThirteenPlanes.PencilFlow.Dynamics

namespace ThirteenPlanes.PencilFlow.Proofs

open Statements Dynamics

/-- The one-loop pencil flow, the fixed ratios. -/
theorem fixedRatios (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.FixedRatios V := by
  intro m hm h c planes hround _ g hg
  have hc := hround.positive
  have hlam := pencilLambda_pos hm planes
  refine ⟨hlam, fun t => ratioRate_eq_zero_iff hc hlam.ne' hg, ?_⟩
  refine ⟨fun t => 6 * c * g ^ 2 * (pencilLambda V * t + 1) * (1 - t) / flowScale, ?_, ?_, ?_⟩
  · fun_prop
  · have := flowScale_pos
    have : 0 < g ^ 2 := by positivity
    simp only [mul_zero, zero_add, sub_zero, mul_one]
    positivity
  · intro t
    unfold ratioRate
    ring

/-- The one-loop pencil flow, the infrared exponent at the round fixed strength. -/
theorem infraredExponent (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.InfraredExponent V := by
  intro m hm h c planes hround _ ε g _ hg
  have hc := hround.positive
  have hn := four_le_finrank_real hm planes
  have hK := flowScale_pos
  refine ⟨?_, ?_⟩
  · have hd : HasDerivAt (ratioRate c (pencilLambda V) g)
        (6 * c * g ^ 2 * (1 ^ 2 * (pencilLambda V * 1 + 1) * (-1) +
          (2 * 1 * (pencilLambda V * 1 + 1) + 1 ^ 2 * pencilLambda V) * (1 - 1)) /
          flowScale) 1 := by
      have h1 : HasDerivAt (fun t : ℝ => t ^ 2 * (pencilLambda V * t + 1) * (1 - t))
          ((2 * 1 * (pencilLambda V * 1 + 1) + 1 ^ 2 * (pencilLambda V * 1)) * (1 - 1) +
            1 ^ 2 * (pencilLambda V * 1 + 1) * (0 - 1)) 1 := by
        have ht2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * 1) 1 := by
          simpa using (hasDerivAt_pow 2 (1 : ℝ))
        have hl : HasDerivAt (fun t : ℝ => pencilLambda V * t + 1) (pencilLambda V * 1) 1 :=
          ((hasDerivAt_id 1).const_mul _).add_const 1
        have hr : HasDerivAt (fun t : ℝ => 1 - t) (0 - 1) 1 :=
          (hasDerivAt_const 1 (1 : ℝ)).sub (hasDerivAt_id 1)
        exact (ht2.mul hl).mul hr
      have h2 := (h1.const_mul (6 * c * g ^ 2)).div_const flowScale
      convert h2 using 1
      · funext t; unfold ratioRate; ring
      · ring
    convert hd using 1
    have e : g ^ 2 = 2 * ε / (c * ((Module.finrank ℝ V : ℝ) + 10)) * flowScale := by
      rw [← hg]; field_simp
    rw [e]
    unfold pencilLambda
    field_simp
    ring
  · have : (fun r => ratioRate c (pencilLambda V) r 1) = fun _ => 0 := by
      funext r; unfold ratioRate; ring
    rw [this]
    exact hasDerivAt_const _ _

end ThirteenPlanes.PencilFlow.Proofs
