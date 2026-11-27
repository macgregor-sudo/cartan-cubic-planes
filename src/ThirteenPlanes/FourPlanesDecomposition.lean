/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.FourPlanesEnergy
public import ThirteenPlanes.Matrix3Dimension
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The exhaustive orthogonal decomposition by trace-free diagonals in the four qutrit bases. -/

noncomputable section

namespace ThirteenPlanes

open TracelessHermitian3

def matrixPlane (k : Fin 4) : Submodule ℝ TracelessHermitian3 :=
  LinearMap.range (matrixFrameProjection k)

theorem mem_matrixPlane_iff (k : Fin 4) (x : TracelessHermitian3) :
    x ∈ matrixPlane k ↔ matrixFrameProjection k x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [matrixFrameProjection_comp, ite_eq_left rfl]
  · intro hx
    exact ⟨x, hx⟩

def traceFreeDiagonalEntries (u : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![u 0, u 1, -(u 0 + u 1)]

theorem traceFreeDiagonalEntries_sum (u : Fin 2 → ℝ) :
    ∑ b, traceFreeDiagonalEntries u b = 0 := by
  simp [traceFreeDiagonalEntries, Fin.sum_univ_three]

def matrixPlaneChartValue (k : Fin 4) (u : Fin 2 → ℝ) : TracelessHermitian3 :=
  ofMatrix (matrixFrameSynthesis k (traceFreeDiagonalEntries u))
    (matrixFrameSynthesis_hermitian _ _) (by simp [traceFreeDiagonalEntries_sum])

def matrixPlaneChart (k : Fin 4) : (Fin 2 → ℝ) →ₗ[ℝ] TracelessHermitian3 where
  toFun := matrixPlaneChartValue k
  map_add' u v := by
    apply toMatrix_injective
    simp only [matrixPlaneChartValue, toMatrix_ofMatrix, map_add]
    rw [← map_add]
    congr 1
    funext b
    fin_cases b <;> simp [traceFreeDiagonalEntries, add_comm, add_assoc, add_left_comm]
  map_smul' r u := by
    apply toMatrix_injective
    simp only [matrixPlaneChartValue, toMatrix_ofMatrix, map_smul, RingHom.id_apply]
    rw [← map_smul]
    congr 1
    funext b
    fin_cases b <;> simp [traceFreeDiagonalEntries, Pi.smul_apply, smul_eq_mul, mul_add]

theorem matrixPlaneChart_fixed (k : Fin 4) (u : Fin 2 → ℝ) :
    matrixFrameProjection k (matrixPlaneChart k u) = matrixPlaneChart k u :=
  matrixFrameProjection_synthesis k _ (traceFreeDiagonalEntries_sum u)

theorem matrixPlaneChart_injective (k : Fin 4) : Function.Injective (matrixPlaneChart k) := by
  intro u v h
  have heq := congrArg toMatrix h
  change matrixFrameSynthesis k (traceFreeDiagonalEntries u) =
    matrixFrameSynthesis k (traceFreeDiagonalEntries v) at heq
  funext b
  fin_cases b
  · simpa [matrixFrameAnalysis_synthesis, traceFreeDiagonalEntries] using
      congrArg (fun X => matrixFrameAnalysis k X 0) heq
  · simpa [matrixFrameAnalysis_synthesis, traceFreeDiagonalEntries] using
      congrArg (fun X => matrixFrameAnalysis k X 1) heq

theorem matrixPlaneChart_range (k : Fin 4) : LinearMap.range (matrixPlaneChart k) = matrixPlane k := by
  ext x
  rw [mem_matrixPlane_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact matrixPlaneChart_fixed k u
  · intro hx
    let v := matrixFrameAnalysis k (toMatrix x)
    have hsum : v 2 = -(v 0 + v 1) := by
      have h : ∑ b, v b = 0 := by
        rw [show (∑ b, v b) = ∑ b, matrixFrameAnalysis k (toMatrix x) b from rfl,
          sum_matrixFrameAnalysis, trace_eq_zero, Complex.zero_re]
      rw [Fin.sum_univ_three] at h
      linarith
    refine ⟨![v 0, v 1], toMatrix_injective ?_⟩
    have hm := congrArg toMatrix hx
    rw [toMatrix_matrixFrameProjection] at hm
    change matrixFrameSynthesis k (traceFreeDiagonalEntries ![v 0, v 1]) = _
    rw [← hm]
    congr 1
    funext b
    fin_cases b <;> simp [traceFreeDiagonalEntries, ← hsum] <;> rfl

theorem matrixPlane_dim (k : Fin 4) : Module.finrank ℝ (matrixPlane k) = 2 := by
  rw [← matrixPlaneChart_range, LinearMap.finrank_range_of_inj (matrixPlaneChart_injective k)]
  simp

theorem matrixPlane_pairwiseOrthogonal :
    Pairwise fun k l : Fin 4 => Submodule.IsOrtho (𝕜 := ℝ) (E := TracelessHermitian3)
      (matrixPlane k) (matrixPlane l) := by
  intro k l hkl
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx y hy
  exact matrixFrameOrthogonality k l hkl x y
    ((mem_matrixPlane_iff k x).1 hx) ((mem_matrixPlane_iff l y).1 hy)

theorem matrixPlane_iSup_finrank : Module.finrank ℝ ↥(⨆ k : Fin 4, matrixPlane k) = 8 := by
  have h : iSupIndep matrixPlane := by
    rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hsum k hk
    have h := congrArg (matrixFrameProjection k) hsum
    rw [map_sum, map_zero] at h
    rw [Finset.sum_eq_single k, (mem_matrixPlane_iff k (v k)).1 (hv k hk)] at h
    · exact h
    · intro l hl hne
      rw [matrixFrameProjection_fixed k l _ ((mem_matrixPlane_iff l (v l)).1 (hv l hl)),
        ite_eq_right hne.symm]
    · simp [hk]
  rw [Submodule.iSup_eq_range_dfinsupp_lsum,
    LinearMap.finrank_range_of_inj h.dfinsupp_lsum_injective]
  change Module.finrank ℝ (DirectSum (Fin 4) (fun i => ↥(matrixPlane i))) = 8
  rw [Module.finrank_directSum]
  simp [matrixPlane_dim]

theorem matrixPlane_exhaustive : (⨆ k : Fin 4, matrixPlane k) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [matrixPlane_iSup_finrank]
  have hle := Submodule.finrank_le (⨆ k : Fin 4, matrixPlane k)
  rw [matrixPlane_iSup_finrank] at hle
  exact le_antisymm hle finrank_le_eight

abbrev fourPlaneDecomposition : PlaneDecomposition TracelessHermitian3 (Fin 4) where
  plane := matrixPlane
  dimension := matrixPlane_dim
  pairwise_orthogonal := matrixPlane_pairwiseOrthogonal
  exhaustive := matrixPlane_exhaustive

theorem fourPlaneDecomposition_proj (k : Fin 4) :
    fourPlaneDecomposition.proj k = matrixFrameProjection k := by
  apply LinearMap.ext
  intro x
  change (matrixPlane k).starProjection (𝕜 := ℝ) x = matrixFrameProjection k x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨x, rfl⟩
  · intro w hw
    rw [inner_sub_left, matrixFrameProjection_inner_swap, (mem_matrixPlane_iff k w).1 hw,
      sub_self]

theorem fourPlaneDecomposition_diagonal_eq :
    fourPlanePair.diagonalCubic =
      ∑ k : Fin 4, (interactionCubic fourPlanePair 1).pullback (fourPlaneDecomposition.proj k) := by
  simp only [interactionCubic_fourPlanePair_one, fourPlaneDecomposition_proj]
  rfl

theorem fourPlaneDecomposition_repeatedPlane (k : Fin 4) (x y : matrixPlane k)
    (z : ↥(Submodule.orthogonal (𝕜 := ℝ) (E := TracelessHermitian3) (matrixPlane k))) : (interactionCubic fourPlanePair 1).apply x y z = 0 := by
  rw [interactionCubic_fourPlanePair_one]
  change inner ℝ (jordan x y) z = 0
  have hmem : jordan x y ∈ matrixPlane k :=
    (mem_matrixPlane_iff k _).2 (project_jordan_of_fixed k _ _
      ((mem_matrixPlane_iff k _).1 x.property) ((mem_matrixPlane_iff k _).1 y.property))
  exact z.property (jordan x y) hmem

end ThirteenPlanes
