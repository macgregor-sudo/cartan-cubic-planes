module

public import ThirteenPlanes.JordanFrames.Complex
public import ThirteenPlanes.Fields.RealFrames

@[expose] public section

set_option backward.privateInPublic true

/-! The real and complex cases of the correspondence between closed planes and frames. -/

open scoped BigOperators Matrix RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

open RoundCubics Peirce

noncomputable section

/-- A closed two-plane in the complex trace-zero space is the plane of a unique
complex Jordan frame up to reordering. -/
theorem complex_closedPlane_iff_frame (S : Submodule ℝ TracelessHermitian3)
    (dim : Module.finrank ℝ S = 2) :
    IsClosedPiece matrixEqualCubic S ↔
      ∃ F : ComplexTraceFrame3, S = F.plane ∧ ∀ G : ComplexTraceFrame3, S = G.plane →
        ∃ σ : Equiv.Perm (Fin 3), ∀ i, G.point i = F.point (σ i) := by
  constructor
  · intro hS
    obtain ⟨F, hF⟩ := complexClosedPlane_has_frame S dim hS
    exact ⟨F, hF, fun G hG => (complex_framePlane_eq_iff_relabel F G).mp (hF.symm.trans hG)⟩
  · rintro ⟨F, rfl, _⟩
    exact F.plane_closed

/-- Real symmetric frames represented by their entrywise inclusion into the
complex Hermitian carrier. -/
abbrev RealTraceFrame3 := {F : ComplexTraceFrame3 // ∀ a i j, (F.point a i j).im = 0}

/-- The actual real matrix of a real symmetric frame point. -/
def realFramePoint (F : RealTraceFrame3) (i : Fin 3) : RealMatrix3 :=
  (F.val.point i).map Complex.re

theorem realFramePoint_complex (F : RealTraceFrame3) (i : Fin 3) :
    (realFramePoint F i).map Complex.ofReal = F.val.point i := by
  ext a b
  exact Complex.ext rfl (by simpa using (F.property i a b).symm)

theorem realFramePoint_symmetric (F : RealTraceFrame3) (i : Fin 3) :
    (realFramePoint F i)ᵀ = realFramePoint F i := by
  ext a b
  have h := congrArg (fun A : ComplexMatrix3 => (A a b).re) (F.val.hermitian i).eq
  simpa [realFramePoint, Matrix.conjTranspose_apply, Complex.star_def] using h

theorem realFramePoint_trace (F : RealTraceFrame3) (i : Fin 3) :
    Matrix.trace (realFramePoint F i) = 1 := by
  have h := congrArg Complex.re (F.val.trace_one i)
  simpa [realFramePoint, Matrix.trace, Matrix.diag, Complex.re_sum] using h

private theorem realMatrixComplex_injective :
    Function.Injective (fun A : RealMatrix3 => A.map Complex.ofReal) := by
  intro A B h
  ext i j
  exact congrArg (fun C : ComplexMatrix3 => (C i j).re) h

theorem realFramePoint_jordan (F : RealTraceFrame3) (i j : Fin 3) :
    (1 / 2 : ℝ) • (realFramePoint F i * realFramePoint F j + realFramePoint F j * realFramePoint F i) =
      if i = j then realFramePoint F i else 0 := by
  apply realMatrixComplex_injective
  have h := F.val.jordan_point i j
  rw [← realFramePoint_complex F i, ← realFramePoint_complex F j] at h
  ext a b
  have ha := congrArg (fun A : ComplexMatrix3 => A a b) h
  split_ifs at ha ⊢
  · simpa [symmetricMatrixProduct, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
      Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div, mul_add] using ha
  · simp [symmetricMatrixProduct, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
      Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_add] at ha ⊢
    linear_combination (2 : ℂ)⁻¹ * ha

theorem realFramePoint_sum (F : RealTraceFrame3) : ∑ i, realFramePoint F i = 1 := by
  ext a b
  have h := congrArg (fun A : ComplexMatrix3 => (A a b).re) F.val.sum_unit
  simpa [realFramePoint, Matrix.sum_apply, Matrix.one_apply, Complex.re_sum, apply_ite] using h

private theorem realFramePlane_range (F : RealTraceFrame3) : F.val.plane ≤ realTraceSubmodule := by
  rw [complex_plane_eq_centered_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let X := complexCenterPoint F.val k
  have hx (i j : Fin 3) : (X.toMatrix i j).im = 0 := by
    rw [complexCenterPoint_matrix]
    by_cases hij : i = j <;>
      simp [Matrix.sub_apply, Matrix.smul_apply, hij, F.property]
  let A : RealMatrix3 := X.toMatrix.map Complex.re
  have hsym : Aᵀ = A := by
    ext i j
    have he := congrArg (fun M : ComplexMatrix3 => (M i j).re) X.isHermitian.eq
    simpa [A, Matrix.conjTranspose_apply, Complex.star_def] using he
  have ht : Matrix.trace A = 0 := by
    have he := congrArg Complex.re X.trace_eq_zero
    simpa [A, Matrix.trace, Matrix.diag, Complex.re_sum] using he
  obtain ⟨y, hy⟩ := (realTraceMatrix_range A).mpr ⟨hsym, ht⟩
  have hxy : realTraceIsometry y = X := by
    apply TracelessHermitian3.toMatrix_injective
    ext i j
    apply Complex.ext
    · exact congrArg (fun M : RealMatrix3 => M i j) hy
    · have hEntry := congrArg (fun M : ComplexMatrix3 => (M i j).im) (show
          (realTraceIsometry y).toMatrix = (realTraceMatrix y).map Complex.ofReal from by
            obtain ⟨⟨a, b, p, q, r⟩, rfl⟩ := realCartanEquiv.surjective y
            ext a' b'
            apply Complex.ext
            · rfl
            · change (complexCartanMatrix a b p q r a' b').im = _
              fin_cases a' <;> fin_cases b' <;>
                simp [complexCartanMatrix, complexSlotMatrix, Complex.real_smul])
      simp only [Matrix.map_apply, Complex.ofReal_im] at hEntry
      exact hEntry.trans (hx i j).symm
  change X ∈ realTraceSubmodule
  rw [← hxy]
  exact y.property

/-- The centered frame plane in the actual real trace-zero space. -/
def realFramePlane (F : RealTraceFrame3) : Submodule ℝ RealTracelessSymmetric3 :=
  F.val.plane.comap realTraceIsometry.toLinearMap

theorem realFramePlane_map (F : RealTraceFrame3) :
    (realFramePlane F).map realTraceIsometry.toLinearMap = F.val.plane := by
  rw [realFramePlane, Submodule.map_comap_eq]
  change realTraceSubmodule.subtype.range ⊓ F.val.plane = F.val.plane
  rw [Submodule.range_subtype]
  exact inf_eq_right.mpr (realFramePlane_range F)

/-- Real frame planes have the expected dimension. -/
theorem realFramePlane_dim (F : RealTraceFrame3) : Module.finrank ℝ (realFramePlane F) = 2 := by
  rw [← F.val.plane_dimension, ← realFramePlane_map F]
  exact (Submodule.equivMapOfInjective realTraceIsometry.toLinearMap realTraceIsometry.injective
    (realFramePlane F)).finrank_eq

/-- A closed real symmetric two-plane has a unique actual frame up to permutation. -/
theorem real_closedPlane_iff_frame (S : Submodule ℝ RealTracelessSymmetric3)
    (dim : Module.finrank ℝ S = 2) :
    IsClosedPiece realCartanCubic S ↔
      ∃ F : RealTraceFrame3, S = realFramePlane F ∧ ∀ G : RealTraceFrame3, S = realFramePlane G →
        ∃ σ : Equiv.Perm (Fin 3), ∀ i, realFramePoint G i = realFramePoint F (σ i) := by
  constructor
  · intro hS
    obtain ⟨F, hF, hFR⟩ := realClosedPlane_has_frame S dim hS
    let R : RealTraceFrame3 := ⟨F, hFR⟩
    have hR : S = realFramePlane R := by
      apply Submodule.map_injective_of_injective (f := realTraceIsometry.toLinearMap)
        realTraceIsometry.injective
      rw [realFramePlane_map R]
      exact hF
    refine ⟨R, hR, fun G hG => ?_⟩
    have h := congrArg (fun T : Submodule ℝ RealTracelessSymmetric3 =>
      T.map realTraceIsometry.toLinearMap) (hR.symm.trans hG)
    simp only [realFramePlane_map] at h
    obtain ⟨σ, hσ⟩ := (complex_framePlane_eq_iff_relabel R.val G.val).mp h
    exact ⟨σ, fun i => congrArg (fun M : ComplexMatrix3 => M.map Complex.re) (hσ i)⟩
  · rintro ⟨F, rfl, _⟩ x y hx hy
    change realTraceIsometry (realCartanCubic.L x y) ∈ F.val.plane
    rw [realTraceIsometry_product]
    exact F.val.plane.smul_mem _ (F.val.plane_closed hx hy)

/-- The original real trace overlap of two points equals their complex trace pairing. -/
theorem realFramePoint_tracePairing (F G : RealTraceFrame3) (i j : Fin 3) :
    Matrix.trace (realFramePoint F i * realFramePoint G j) =
      tracePairing (F.val.point i) (G.val.point j) := by
  rw [← realFramePoint_complex F i, ← realFramePoint_complex G j]
  simp [tracePairing, Matrix.trace, Matrix.mul_apply]

/-- Orthogonality of real symmetric frame planes is equivalent to their real trace overlaps. -/
theorem real_framePlane_orthogonal_iff (F G : RealTraceFrame3) :
    Submodule.IsOrtho (𝕜 := ℝ) (E := RealTracelessSymmetric3) (realFramePlane F) (realFramePlane G) ↔
      ∀ i j, Matrix.trace (realFramePoint F i * realFramePoint G j) = 1 / 3 := by
  simp only [realFramePoint_tracePairing, ← complex_framePlane_orthogonal_iff]
  constructor
  · intro h
    rw [Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    rw [← realFramePlane_map F] at hx
    rw [← realFramePlane_map G] at hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact h.inner_eq hx' hy'
  · intro h
    rw [Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    exact h.inner_eq hx hy

end
end ThirteenPlanes.JordanFrames
