module

public import ThirteenPlanes.Quaternionic.FrameGeometry
public import ThirteenPlanes.Quaternionic.RealAction
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Native Frobenius geometry for quaternionic frame capacity

The Euclidean carrier is a finite L2 family of actual quaternion entries.
Its real linear equivalence with the native matrix carrier is explicit.
Hermitian and traceless spaces are pulled back as actual submodules.
No incompatible inner product is installed on the native function supnorm.
The finite Bessel capacity inequality is completed in FrameCapacity.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

/-- Nine quaternion entries with their real Euclidean L2 geometry. -/
abbrev MatrixHilbert := PiLp 2 (fun _ : Outcome × Outcome => Q)

def matrixHilbertEquiv : MatrixHilbert ≃ₗ[ℝ] QMat where
  toFun v := fun i j => v (i, j)
  invFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  left_inv v := by
    apply (WithLp.linearEquiv 2 ℝ (Outcome × Outcome → Q)).injective
    funext ij
    cases ij
    rfl
  right_inv A := rfl
  map_add' v w := rfl
  map_smul' r v := rfl

def hermitianHilbertSubmodule : Submodule ℝ MatrixHilbert :=
  hermitianSubmodule.comap matrixHilbertEquiv.toLinearMap

def tracelessHilbertSubmodule : Submodule ℝ MatrixHilbert :=
  tracelessHermitianSubmodule.comap matrixHilbertEquiv.toLinearMap

abbrev HermitianHilbert := hermitianHilbertSubmodule
abbrev TracelessHilbert := tracelessHilbertSubmodule

lemma matrixHilbert_inner (v w : MatrixHilbert) :
    inner ℝ v w =
      ∑ i, ∑ j, (star (matrixHilbertEquiv v i j) * matrixHilbertEquiv w i j).re := by
  change (∑ ij : Outcome × Outcome, inner ℝ (v ij) (w ij)) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact quaternion_inner_eq_qInner_re _ _

lemma rtrace_adjoint_mul (A B : QMat) :
    rtrace (Aᴴ * B) = ∑ i, ∑ j, (star (A i j) * B i j).re := by
  simp only [rtrace, Matrix.mul_apply, quaternion_re_sum, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

/-- The actual induced Euclidean inner product is precisely the source pairing. -/
lemma hermitianHilbert_inner (v w : HermitianHilbert) :
    inner ℝ v w =
      traceForm (matrixHilbertEquiv v.val) (matrixHilbertEquiv w.val) := by
  change inner ℝ v.val w.val = _
  have hv : (matrixHilbertEquiv v.val)ᴴ = matrixHilbertEquiv v.val := v.property
  rw [matrixHilbert_inner, ← rtrace_adjoint_mul, hv, traceForm_eq_rtrace_mul]

lemma tracelessHilbert_inner (v w : TracelessHilbert) :
    inner ℝ v w =
      traceForm (matrixHilbertEquiv v.val) (matrixHilbertEquiv w.val) := by
  change inner ℝ v.val w.val = _
  have hv : (matrixHilbertEquiv v.val)ᴴ = matrixHilbertEquiv v.val := v.property.1
  rw [matrixHilbert_inner, ← rtrace_adjoint_mul, hv, traceForm_eq_rtrace_mul]

/-- Real coordinates are the three real diagonal entries and three quaternionic
upper-triangular entries; no spectral theorem is used. -/
def hermCoordinates (A : Herm3) : (Outcome → ℝ) × (Outcome → Q) :=
  (fun i => (A.val i i).re, ![A.val 0 1, A.val 0 2, A.val 1 2])

def matrixOfHermCoordinates (d : Outcome → ℝ) (q : Outcome → Q) : QMat :=
  ![![(d 0 : Q), q 0, q 1],
    ![star (q 0), (d 1 : Q), q 2],
    ![star (q 1), star (q 2), (d 2 : Q)]]

lemma matrixOfHermCoordinates_isHermitian (d : Outcome → ℝ) (q : Outcome → Q) :
    (matrixOfHermCoordinates d q).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [matrixOfHermCoordinates]

lemma matrixOfHermCoordinates_inverse (A : Herm3) :
    matrixOfHermCoordinates (hermCoordinates A).1 (hermCoordinates A).2 = A.val := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfHermCoordinates, hermCoordinates]
  all_goals first
    | exact (Quaternion.star_eq_self.mp (A.property.apply _ _)).symm
    | exact A.property.apply _ _

def hermCoordinatesEquiv : Herm3 ≃ₗ[ℝ] ((Outcome → ℝ) × (Outcome → Q)) where
  toFun := hermCoordinates
  invFun x := ⟨matrixOfHermCoordinates x.1 x.2,
    matrixOfHermCoordinates_isHermitian _ _⟩
  left_inv A := by
    apply Subtype.ext
    exact matrixOfHermCoordinates_inverse A
  right_inv x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [hermCoordinates, matrixOfHermCoordinates]
  map_add' A B := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' r A := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

theorem finrank_Herm3 : Module.finrank ℝ Herm3 = 15 := by
  rw [hermCoordinatesEquiv.finrank_eq, Module.finrank_prod]
  simp [Module.finrank_pi_fintype, Quaternion.finrank_eq_four]

def hermitianTrace : Herm3 →ₗ[ℝ] ℝ :=
  rtraceLinear.comp hermitianSubmodule.subtype

lemma hermitianTrace_surjective : Function.Surjective hermitianTrace := by
  intro r
  refine ⟨⟨(r / 3) • (1 : QMat), ?_⟩, ?_⟩
  · apply Matrix.IsHermitian.smul Matrix.isHermitian_one
    rfl
  · change rtrace ((r / 3) • (1 : QMat)) = r
    rw [rtrace_smul, rtrace_one]
    ring

/-- Native trace-zero Hermitian matrices are literally the trace kernel. -/
def tracelessTraceKernelEquiv : J0 ≃ₗ[ℝ] LinearMap.ker hermitianTrace where
  toFun A := ⟨⟨A.val, A.property.1⟩, A.property.2⟩
  invFun A := ⟨A.val.val, A.val.property, A.property⟩
  left_inv A := rfl
  right_inv A := rfl
  map_add' A B := rfl
  map_smul' r A := rfl

theorem finrank_J0 : Module.finrank ℝ J0 = 14 := by
  rw [tracelessTraceKernelEquiv.finrank_eq]
  have h := hermitianTrace.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hermitianTrace_surjective,
    finrank_Herm3, _root_.finrank_top, Module.finrank_self] at h
  omega

def hermitianHilbertEquiv : HermitianHilbert ≃ₗ[ℝ] Herm3 where
  toFun A := ⟨matrixHilbertEquiv A.val, A.property⟩
  invFun A := ⟨matrixHilbertEquiv.symm A.val, by
    change (matrixHilbertEquiv (matrixHilbertEquiv.symm A.val)).IsHermitian
    rw [matrixHilbertEquiv.apply_symm_apply]
    exact A.property⟩
  left_inv A := by apply Subtype.ext; exact matrixHilbertEquiv.symm_apply_apply A.val
  right_inv A := by apply Subtype.ext; exact matrixHilbertEquiv.apply_symm_apply A.val
  map_add' A B := by apply Subtype.ext; exact matrixHilbertEquiv.map_add A.val B.val
  map_smul' r A := by apply Subtype.ext; exact matrixHilbertEquiv.map_smul r A.val

def tracelessHilbertEquiv : TracelessHilbert ≃ₗ[ℝ] J0 where
  toFun A := ⟨matrixHilbertEquiv A.val, A.property⟩
  invFun A := ⟨matrixHilbertEquiv.symm A.val, by
    change matrixHilbertEquiv (matrixHilbertEquiv.symm A.val) ∈ tracelessHermitianSubmodule
    simpa using A.property⟩
  left_inv A := by apply Subtype.ext; exact matrixHilbertEquiv.symm_apply_apply A.val
  right_inv A := by apply Subtype.ext; exact matrixHilbertEquiv.apply_symm_apply A.val
  map_add' A B := by apply Subtype.ext; exact matrixHilbertEquiv.map_add A.val B.val
  map_smul' r A := by apply Subtype.ext; exact matrixHilbertEquiv.map_smul r A.val

theorem finrank_HermitianHilbert : Module.finrank ℝ HermitianHilbert = 15 := by
  rw [hermitianHilbertEquiv.finrank_eq, finrank_Herm3]

theorem finrank_TracelessHilbert : Module.finrank ℝ TracelessHilbert = 14 := by
  rw [tracelessHilbertEquiv.finrank_eq, finrank_J0]

/-- Centered frame points in the correctly normed real Hilbert space. -/
def Frame.centeredHilbert (F : Frame) (a : Outcome) : TracelessHilbert :=
  tracelessHilbertEquiv.symm (F.centeredPoint a)

lemma Frame.centeredHilbert_inner (F G : Frame) (a b : Outcome) :
    inner ℝ (F.centeredHilbert a) (G.centeredHilbert b) =
      traceForm (F.centeredPointMatrix a) (G.centeredPointMatrix b) := by
  rw [tracelessHilbert_inner]
  change traceForm
    (matrixHilbertEquiv (tracelessHilbertEquiv.symm (F.centeredPoint a)).val)
    (matrixHilbertEquiv (tracelessHilbertEquiv.symm (G.centeredPoint b)).val) = _
  have hF := congrArg Subtype.val (tracelessHilbertEquiv.apply_symm_apply (F.centeredPoint a))
  have hG := congrArg Subtype.val (tracelessHilbertEquiv.apply_symm_apply (G.centeredPoint b))
  exact congrArg₂ traceForm hF hG


lemma Frame.sum_centeredPointMatrix (F : Frame) :
    (∑ a, F.centeredPointMatrix a) = 0 := by
  unfold Frame.centeredPointMatrix
  rw [Finset.sum_sub_distrib, F.sum_points]
  simp only [Fin.sum_univ_three]
  module

lemma Frame.sum_centeredHilbert (F : Frame) : (∑ a, F.centeredHilbert a) = 0 := by
  apply tracelessHilbertEquiv.injective
  simp only [map_sum, map_zero, Frame.centeredHilbert, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact F.sum_centeredPointMatrix

/-- Explicit orthonormal coordinates in the actual two-dimensional frame plane. -/
def Frame.planeOrtho (F : Frame) (a : Fin 2) : TracelessHilbert :=
  if a = 0 then Real.sqrt (3 / 2 : ℝ) • F.centeredHilbert 0
  else Real.sqrt 2 • (F.centeredHilbert 1 + (1 / 2 : ℝ) • F.centeredHilbert 0)

@[simp] lemma Frame.planeOrtho_zero (F : Frame) :
    F.planeOrtho 0 = Real.sqrt (3 / 2 : ℝ) • F.centeredHilbert 0 := by
  simp only [Frame.planeOrtho, if_pos rfl, ite_true]

@[simp] lemma Frame.planeOrtho_one (F : Frame) :
    F.planeOrtho 1 =
      Real.sqrt 2 • (F.centeredHilbert 1 + (1 / 2 : ℝ) • F.centeredHilbert 0) := by
  simp only [Frame.planeOrtho, if_neg (show (1 : Fin 2) ≠ 0 by decide)]

lemma traceless_inner_smul_left (x y : TracelessHilbert) (r : ℝ) :
    inner ℝ (r • x) y = r * inner ℝ x y := by
  change inner ℝ (r • x.val) y.val = r * inner ℝ x.val y.val
  exact real_inner_smul_left x.val y.val r

lemma traceless_inner_smul_right (x y : TracelessHilbert) (r : ℝ) :
    inner ℝ x (r • y) = r * inner ℝ x y := by
  change inner ℝ x.val (r • y.val) = r * inner ℝ x.val y.val
  exact real_inner_smul_right x.val y.val r

lemma traceless_inner_add_left (x y z : TracelessHilbert) :
    inner ℝ (x + y) z = inner ℝ x z + inner ℝ y z := by
  change inner ℝ (x.val + y.val) z.val = _
  exact inner_add_left _ _ _

lemma traceless_inner_add_right (x y z : TracelessHilbert) :
    inner ℝ x (y + z) = inner ℝ x y + inner ℝ x z := by
  change inner ℝ x.val (y.val + z.val) = _
  exact inner_add_right _ _ _

lemma Frame.planeOrtho_gram (F : Frame) (a b : Fin 2) :
    inner ℝ (F.planeOrtho a) (F.planeOrtho b) = if a = b then 1 else 0 := by
  have h3 : Real.sqrt (3 / 2 : ℝ) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  fin_cases a <;> fin_cases b
  · change inner ℝ (Real.sqrt (3 / 2 : ℝ) • F.centeredHilbert 0)
      (Real.sqrt (3 / 2 : ℝ) • F.centeredHilbert 0) = 1
    simp only [traceless_inner_smul_left, traceless_inner_smul_right,
      Frame.centeredHilbert_inner, Frame.centeredPoint_gram]
    norm_num only [ite_true, ite_false,
      show (0 : Outcome) ≠ 1 by decide, show (1 : Outcome) ≠ 0 by decide]
    nlinarith [h3]
  · change inner ℝ (Real.sqrt (3 / 2 : ℝ) • F.centeredHilbert 0)
      (Real.sqrt 2 • (F.centeredHilbert 1 + (1 / 2 : ℝ) • F.centeredHilbert 0)) = 0
    simp only [traceless_inner_smul_left, traceless_inner_smul_right,
      traceless_inner_add_left, traceless_inner_add_right,
      Frame.centeredHilbert_inner, Frame.centeredPoint_gram]
    norm_num <;> ring
  · change inner ℝ
      (Real.sqrt 2 • (F.centeredHilbert 1 + (1 / 2 : ℝ) • F.centeredHilbert 0))
      (Real.sqrt (3 / 2 : ℝ) • F.centeredHilbert 0) = 0
    simp only [traceless_inner_smul_left, traceless_inner_smul_right,
      traceless_inner_add_left, traceless_inner_add_right,
      Frame.centeredHilbert_inner, Frame.centeredPoint_gram]
    norm_num <;> ring
  · change inner ℝ
      (Real.sqrt 2 • (F.centeredHilbert 1 + (1 / 2 : ℝ) • F.centeredHilbert 0))
      (Real.sqrt 2 • (F.centeredHilbert 1 + (1 / 2 : ℝ) • F.centeredHilbert 0)) = 1
    simp only [traceless_inner_smul_left, traceless_inner_smul_right,
      traceless_inner_add_left, traceless_inner_add_right,
      Frame.centeredHilbert_inner, Frame.centeredPoint_gram]
    norm_num only [ite_true, ite_false,
      show (0 : Outcome) ≠ 1 by decide, show (1 : Outcome) ≠ 0 by decide]
    nlinarith [h2]

lemma Frame.planeOrtho_orthonormal (F : Frame) : Orthonormal ℝ F.planeOrtho :=
  orthonormal_iff_ite.mpr F.planeOrtho_gram

lemma Frame.planeOrtho_cross {F G : Frame} (hFG : F.MutuallyUnbiased G)
    (a b : Fin 2) : inner ℝ (F.planeOrtho a) (G.planeOrtho b) = 0 := by
  have hq := (F.mutuallyUnbiased_iff_centered_orthogonal G).mp hFG
  fin_cases a <;> fin_cases b
  · change inner ℝ (Real.sqrt (3 / 2 : ℝ) • F.centeredHilbert 0)
      (Real.sqrt (3 / 2 : ℝ) • G.centeredHilbert 0) = 0
    simp only [traceless_inner_smul_left, traceless_inner_smul_right,
      Frame.centeredHilbert_inner, hq, mul_zero]
  · change inner ℝ (Real.sqrt (3 / 2 : ℝ) • F.centeredHilbert 0)
      (Real.sqrt 2 • (G.centeredHilbert 1 + (1 / 2 : ℝ) • G.centeredHilbert 0)) = 0
    simp only [traceless_inner_smul_left, traceless_inner_smul_right,
      traceless_inner_add_left, traceless_inner_add_right,
      Frame.centeredHilbert_inner, hq, mul_zero, add_zero]
  · change inner ℝ
      (Real.sqrt 2 • (F.centeredHilbert 1 + (1 / 2 : ℝ) • F.centeredHilbert 0))
      (Real.sqrt (3 / 2 : ℝ) • G.centeredHilbert 0) = 0
    simp only [traceless_inner_smul_left, traceless_inner_smul_right,
      traceless_inner_add_left, traceless_inner_add_right,
      Frame.centeredHilbert_inner, hq, mul_zero, add_zero]
  · change inner ℝ
      (Real.sqrt 2 • (F.centeredHilbert 1 + (1 / 2 : ℝ) • F.centeredHilbert 0))
      (Real.sqrt 2 • (G.centeredHilbert 1 + (1 / 2 : ℝ) • G.centeredHilbert 0)) = 0
    simp only [traceless_inner_smul_left, traceless_inner_smul_right,
      traceless_inner_add_left, traceless_inner_add_right,
      Frame.centeredHilbert_inner, hq, mul_zero, add_zero]

lemma mub_planes_orthonormal {ι : Type*} (F : ι → Frame)
    (hF : IsMUBFrameFamily F) :
    Orthonormal ℝ (fun ia : ι × Fin 2 => (F ia.1).planeOrtho ia.2) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    simpa only [Prod.mk.injEq, true_and] using (F i).planeOrtho_gram a b
  · rw [Frame.planeOrtho_cross (hF hij)]
    simp [hij]

/-- Native dimension capacity alone: each unbiased frame contributes two
orthonormal vectors in the actual 14-dimensional trace-zero Hilbert space. -/
theorem card_frames_le_seven {ι : Type*} [Fintype ι]
    (F : ι → Frame) (hF : IsMUBFrameFamily F) : Fintype.card ι ≤ 7 := by
  have h := (mub_planes_orthonormal F hF).linearIndependent.fintype_card_le_finrank
  rw [finrank_TracelessHilbert, Fintype.card_prod, Fintype.card_fin] at h
  omega

lemma Frame.centered_parseval (F : Frame) (v : TracelessHilbert) :
    (∑ a, inner ℝ v (F.centeredHilbert a) ^ 2) =
      ∑ k, inner ℝ v (F.planeOrtho k) ^ 2 := by
  have hsum : ∑ a, inner ℝ v (F.centeredHilbert a) = 0 := by
    rw [← inner_sum, F.sum_centeredHilbert, inner_zero_right]
  rw [Fin.sum_univ_three] at hsum
  have hlast : inner ℝ v (F.centeredHilbert 2) =
      - inner ℝ v (F.centeredHilbert 0) - inner ℝ v (F.centeredHilbert 1) := by
    linarith
  have h3 : Real.sqrt (3 / 2 : ℝ) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Fin.sum_univ_three, Fin.sum_univ_two]
  change inner ℝ v (F.centeredHilbert 0) ^ 2 +
    inner ℝ v (F.centeredHilbert 1) ^ 2 + inner ℝ v (F.centeredHilbert 2) ^ 2 =
      inner ℝ v (Real.sqrt (3 / 2 : ℝ) • F.centeredHilbert 0) ^ 2 +
      inner ℝ v (Real.sqrt 2 •
        (F.centeredHilbert 1 + (1 / 2 : ℝ) • F.centeredHilbert 0)) ^ 2
  simp only [traceless_inner_smul_right, traceless_inner_add_right]
  simp only [mul_pow, h3, h2, hlast]
  ring

/-- Finite Bessel inequality for all actual centered points of a MUB family. -/
theorem centered_frame_bessel {ι : Type*} [Fintype ι]
    (F : ι → Frame) (hF : IsMUBFrameFamily F) (v : TracelessHilbert) :
    (∑ i, ∑ a, inner ℝ v ((F i).centeredHilbert a) ^ 2) ≤ inner ℝ v v := by
  calc
    (∑ i, ∑ a, inner ℝ v ((F i).centeredHilbert a) ^ 2) =
        ∑ i, ∑ k, inner ℝ v ((F i).planeOrtho k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (F i).centered_parseval v
    _ ≤ inner ℝ v v := by
      have h := (mub_planes_orthonormal F hF).sum_inner_products_le
        (s := Finset.univ) v
      simpa only [Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs,
        real_inner_comm, real_inner_self_eq_norm_sq] using h

end QuaternionicMUB
