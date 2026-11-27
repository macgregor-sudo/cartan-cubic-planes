module

public import ThirteenPlanes.Shares.TraceFrames
public import ThirteenPlanes.FourPlanes

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators Matrix RealInnerProductSpace

noncomputable section

private def hermitianEntries : Submodule ℝ MatrixEntries3 where
  carrier := {x | (matrixEntries3 x).IsHermitian}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (matrixEntries3 (x + y)).IsHermitian
    rw [map_add]
    exact hx.add hy
  smul_mem' := by
    intro r x hx
    change (matrixEntries3 (r • x)).IsHermitian
    rw [map_smul]
    exact hx.smul (show IsSelfAdjoint r from star_trivial r)

abbrev FullHermitian := ↥hermitianEntries

def fullMatrix : FullHermitian →ₗ[ℝ] ComplexMatrix3 :=
  matrixEntries3.comp hermitianEntries.subtype

theorem fullMatrix_hermitian (x : FullHermitian) : (fullMatrix x).IsHermitian := x.property

def ofFullMatrix (A : ComplexMatrix3) (hA : A.IsHermitian) : FullHermitian :=
  ⟨WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 => A ij.1 ij.2), hA⟩

@[simp] theorem fullMatrix_ofFullMatrix (A : ComplexMatrix3) (hA : A.IsHermitian) :
    fullMatrix (ofFullMatrix A hA) = A := rfl

theorem fullMatrix_injective : Function.Injective fullMatrix := by
  intro x y h
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℝ (Fin 3 × Fin 3 → ℂ)).injective
  funext ij
  exact congrFun (congrFun h ij.1) ij.2

def complexTraceInclusion : TracelessHermitian3 →ₗᵢ[ℝ] FullHermitian where
  toLinearMap := Submodule.inclusion (show tracelessHermitianSubspace ≤ hermitianEntries from
    fun _ h => h.1)
  norm_map' _ := rfl

theorem fullInner_eq_tracePairing (x y : FullHermitian) :
    inner ℝ x y = tracePairing (fullMatrix x) (fullMatrix y) := by
  have hx (ij : Fin 3 × Fin 3) : star (fullMatrix x ij.1 ij.2) = fullMatrix x ij.2 ij.1 :=
    congrFun (congrFun (fullMatrix_hermitian x).eq ij.2) ij.1
  change inner ℝ x.val y.val = _
  rw [PiLp.inner_apply]
  change (∑ ij : Fin 3 × Fin 3,
    Complex.reAddGroupHom (fullMatrix y ij.1 ij.2 * star (fullMatrix x ij.1 ij.2))) =
    Complex.reAddGroupHom (∑ i, ∑ j, fullMatrix x i j * fullMatrix y j i)
  rw [← map_sum, Fintype.sum_prod_type]
  apply congrArg Complex.re
  calc
    _ = ∑ i, ∑ j, fullMatrix y i j * fullMatrix x j i :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        congrArg (fullMatrix y i j * ·) (hx (i, j))
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

private def rawJordan : ComplexMatrix3 →ₗ[ℝ] ComplexMatrix3 →ₗ[ℝ] ComplexMatrix3 :=
  (1 / 2 : ℝ) • (LinearMap.mul ℝ ComplexMatrix3 + (LinearMap.mul ℝ ComplexMatrix3).flip)

private theorem rawJordan_apply (X Y : ComplexMatrix3) : rawJordan X Y = symmetricMatrixProduct X Y := by
  change ((1 / 2 : ℝ) : ℂ) • (X * Y + Y * X) = (1 / 2 : ℂ) • (X * Y + Y * X)
  push_cast
  rfl

private theorem rawJordan_mem_range (x y : FullHermitian) :
    (rawJordan.compl₁₂ fullMatrix fullMatrix) x y ∈ LinearMap.range fullMatrix := by
  refine ⟨ofFullMatrix _ (symmetricMatrixProduct_hermitian
    (fullMatrix_hermitian x) (fullMatrix_hermitian y)), ?_⟩
  rw [fullMatrix_ofFullMatrix, LinearMap.compl₁₂_apply, rawJordan_apply]

private def complexFullJordan : FullHermitian →ₗ[ℝ] FullHermitian →ₗ[ℝ] FullHermitian :=
  (rawJordan.compl₁₂ fullMatrix fullMatrix).codRestrict₂ fullMatrix fullMatrix_injective
    rawJordan_mem_range

private theorem complexFullJordan_matrix (x y : FullHermitian) :
    fullMatrix (complexFullJordan x y) = symmetricMatrixProduct (fullMatrix x) (fullMatrix y) := by
  exact (LinearMap.codRestrict₂_apply _ _ _ rawJordan_mem_range x y).trans (rawJordan_apply _ _)

private theorem tracePairing_jordan_pair (X Y Z : ComplexMatrix3) :
    tracePairing (symmetricMatrixProduct X Y) Z =
      ((Matrix.trace (X * Y * Z)).re + (Matrix.trace (Y * X * Z)).re) / 2 := by
  simp only [tracePairing, symmetricMatrixProduct, Matrix.smul_mul, add_mul,
    Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  norm_num [Complex.add_re, Complex.mul_re, Complex.div_re]
  ring

def complexFullCubic : SymmetricCubic FullHermitian :=
  SymmetricCubic.ofProduct complexFullJordan
    (fun x y => fullMatrix_injective (by
      rw [complexFullJordan_matrix, complexFullJordan_matrix]
      simp [symmetricMatrixProduct, add_comm]))
    (fun x y z => by
      rw [fullInner_eq_tracePairing, fullInner_eq_tracePairing, complexFullJordan_matrix,
        complexFullJordan_matrix, tracePairing_jordan_pair, tracePairing_jordan_pair,
        Matrix.trace_mul_cycle (fullMatrix x) (fullMatrix y) (fullMatrix z),
        Matrix.trace_mul_cycle (fullMatrix x) (fullMatrix z) (fullMatrix y)]
      ring)

def complexUnit : FullHermitian := ofFullMatrix 1 Matrix.isHermitian_one

theorem complexUnit_mul (x : FullHermitian) : complexFullCubic.L complexUnit x = x := by
  apply fullMatrix_injective
  change fullMatrix (complexFullJordan complexUnit x) = _
  rw [complexFullJordan_matrix]
  change symmetricMatrixProduct 1 (fullMatrix x) = _
  simp only [symmetricMatrixProduct, one_mul, mul_one, ← two_smul ℂ (fullMatrix x), smul_smul]
  norm_num

theorem tracePairing_eq_re_trace_jordan (X Y : ComplexMatrix3) :
    tracePairing X Y = (Matrix.trace (symmetricMatrixProduct X Y)).re := by
  simp only [tracePairing, symmetricMatrixProduct, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  rw [Matrix.trace_mul_comm Y X]
  norm_num [Complex.add_re, Complex.mul_re, Complex.div_re]
  ring

/-- Three ordered trace-one Hermitian Jordan idempotents forming a complex matrix frame. -/
structure ComplexTraceFrame3 where
  point : Fin 3 → ComplexMatrix3
  hermitian : ∀ a, (point a).IsHermitian
  trace_one : ∀ a, Matrix.trace (point a) = 1
  jordan_point : ∀ a b, symmetricMatrixProduct (point a) (point b) = if a = b then point a else 0
  sum_unit : ∑ a, point a = 1

def ComplexTraceFrame3.center (F : ComplexTraceFrame3) (a : Fin 3) : TracelessHermitian3 :=
  TracelessHermitian3.ofMatrix (traceFreePart (F.point a))
    (traceFreePart_hermitian (F.hermitian a)) (trace_traceFreePart _)

/-- The actual traceless span of the frame points. -/
def ComplexTraceFrame3.plane (F : ComplexTraceFrame3) : Submodule ℝ TracelessHermitian3 :=
  Submodule.span ℝ (Set.range F.center)

def complexFrameData (F : ComplexTraceFrame3) :
    CenteredTraceFrame (V := TracelessHermitian3) (E := FullHermitian)
      complexTraceInclusion complexUnit F.plane := by
  let q (a : Fin 3) : F.plane := ⟨F.center a, Submodule.subset_span ⟨a, rfl⟩⟩
  refine ⟨fun a => ofFullMatrix (F.point a) (F.hermitian a), ?_, ?_, q, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro a b
    rw [fullInner_eq_tracePairing, fullMatrix_ofFullMatrix, fullMatrix_ofFullMatrix,
      tracePairing_eq_re_trace_jordan, F.jordan_point]
    split_ifs <;> simp [F.trace_one]
  · apply fullMatrix_injective
    change fullMatrix (∑ a, ofFullMatrix (F.point a) (F.hermitian a)) = 1
    simp only [map_sum, fullMatrix_ofFullMatrix]
    exact F.sum_unit
  · intro a
    apply fullMatrix_injective
    rw [map_sub, map_smul, fullMatrix_ofFullMatrix]
    change traceFreePart (F.point a) = F.point a - (1 / 3 : ℝ) • (1 : ComplexMatrix3)
    rw [traceFreePart, F.trace_one]
    change F.point a - (1 / 3 : ℂ) • (1 : ComplexMatrix3) =
      F.point a - ((1 / 3 : ℝ) : ℂ) • (1 : ComplexMatrix3)
    push_cast
    rfl
  · apply Submodule.map_injective_of_injective (f := F.plane.subtype) Subtype.val_injective
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    rfl

private def rawCenter : ComplexMatrix3 →ₗ[ℂ] ComplexMatrix3 where
  toFun := traceFreePart
  map_add' := traceFreePart_add
  map_smul' := traceFreePart_smul

private theorem rawCenter_unit : rawCenter 1 = 0 := by
  change traceFreePart (1 : ComplexMatrix3) = 0
  simp [traceFreePart]

private theorem ComplexTraceFrame3.center_mem (F : ComplexTraceFrame3) (a : Fin 3) :
    F.center a ∈ F.plane :=
  Submodule.subset_span ⟨a, rfl⟩

private theorem ComplexTraceFrame3.centerProduct (F : ComplexTraceFrame3) (a b : Fin 3) :
    matrixEqualCubic.L (F.center a) (F.center b) =
      (if a = b then F.center a else 0) - (1 / 3 : ℝ) • (F.center a + F.center b) := by
  have hc (i : Fin 3) : TracelessHermitian3.toMatrix (F.center i) =
      F.point i - (1 / 3 : ℂ) • (1 : ComplexMatrix3) := by
    change traceFreePart (F.point i) = _
    rw [traceFreePart, F.trace_one]
  have hp : symmetricMatrixProduct (TracelessHermitian3.toMatrix (F.center a))
      (TracelessHermitian3.toMatrix (F.center b)) =
      symmetricMatrixProduct (F.point a) (F.point b) -
        (1 / 3 : ℂ) • (F.point a + F.point b) + (1 / 9 : ℂ) • (1 : ComplexMatrix3) := by
    rw [hc, hc]
    simp only [symmetricMatrixProduct, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      mul_one, one_mul, smul_sub, smul_add, smul_smul]
    module
  apply TracelessHermitian3.toMatrix_injective
  change rawCenter (symmetricMatrixProduct (TracelessHermitian3.toMatrix (F.center a))
    (TracelessHermitian3.toMatrix (F.center b))) = _
  rw [hp, F.jordan_point, map_add, map_sub, map_smul, map_smul, rawCenter_unit, smul_zero,
    add_zero, map_add]
  have hs : (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) := by push_cast; rfl
  rw [hs]
  split_ifs <;> simp only [map_sub, map_smul, map_add, map_zero] <;> rfl

/-- The span of the centered complex frame points is closed under the traceless Jordan product. -/
theorem ComplexTraceFrame3.plane_closed (F : ComplexTraceFrame3) :
    IsClosedPiece matrixEqualCubic F.plane := by
  let S := F.plane
  have hpoint (a b : Fin 3) : matrixEqualCubic.L (F.center a) (F.center b) ∈ S := by
    rw [F.centerProduct]
    refine S.sub_mem ?_ (S.smul_mem _ (S.add_mem (F.center_mem a) (F.center_mem b)))
    split <;> first | exact F.center_mem a | exact S.zero_mem
  have hx (a : Fin 3) : S ≤ S.comap (matrixEqualCubic.L (F.center a)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    exact hpoint a b
  intro u v hu hv
  have hy : S ≤ S.comap (matrixEqualCubic.L v) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    change matrixEqualCubic.L v (F.center a) ∈ S
    rw [matrixEqualCubic.L_comm]
    exact hx a hv
  rw [matrixEqualCubic.L_comm]
  exact hy hu

private theorem ComplexTraceFrame3.center_sum (F : ComplexTraceFrame3) :
    ∑ a, F.center a = 0 := by
  apply TracelessHermitian3.toMatrix_injective
  rw [map_sum, map_zero]
  change (∑ a, rawCenter (F.point a)) = 0
  rw [← map_sum, F.sum_unit, rawCenter_unit]

private theorem ComplexTraceFrame3.center_inner (F : ComplexTraceFrame3) (a b : Fin 3) :
    inner ℝ (F.center a).val (F.center b).val = (if a = b then (1 : ℝ) else 0) - 1 / 3 :=
  (complexFrameData F).centered_inner a b

/-- Every ordered complex matrix frame defines a genuinely two-dimensional centered span. -/
theorem ComplexTraceFrame3.plane_dimension (F : ComplexTraceFrame3) :
    Module.finrank ℝ F.plane = 2 := by
  let v : Fin 2 → TracelessHermitian3 := ![F.center 0, F.center 1]
  let S := Submodule.span ℝ (Set.range v)
  have h₀ : F.center 0 ∈ S := Submodule.subset_span ⟨0, rfl⟩
  have h₁ : F.center 1 ∈ S := Submodule.subset_span ⟨1, rfl⟩
  have h₂ : F.center 2 ∈ S := by
    have hs := F.center_sum
    rw [Fin.sum_univ_three] at hs
    have he : F.center 2 = -(F.center 0 + F.center 1) := by
      calc
        _ = (F.center 0 + F.center 1 + F.center 2) - (F.center 0 + F.center 1) := by abel
        _ = _ := by rw [hs, zero_sub]
    rw [he]
    exact S.neg_mem (S.add_mem h₀ h₁)
  have hS : F.plane = S := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> assumption
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact F.center_mem 0
      · exact F.center_mem 1
  have hli : LinearIndependent ℝ v := by
    change LinearIndependent ℝ ![F.center 0, F.center 1]
    rw [LinearIndependent.pair_iffₛ]
    intro a b a' b' h
    have test (i : Fin 3) :
        a * ((if i = 0 then (1 : ℝ) else 0) - 1 / 3) +
          b * ((if i = 1 then (1 : ℝ) else 0) - 1 / 3) =
        a' * ((if i = 0 then (1 : ℝ) else 0) - 1 / 3) +
          b' * ((if i = 1 then (1 : ℝ) else 0) - 1 / 3) := by
      have hi := congrArg (fun x : TracelessHermitian3 => inner ℝ (F.center i).val x.val) h
      simpa only [Submodule.coe_add, Submodule.coe_smul, inner_add_right, real_inner_smul_right,
        F.center_inner] using hi
    have h₀ := test 0
    have h₁ := test 1
    norm_num at h₀ h₁
    exact ⟨by linarith, by linarith⟩
  rw [hS]
  exact (finrank_span_eq_card hli).trans (Fintype.card_fin 2)

/-- The actual matrix Jordan product on the full complex trace Hilbert space. -/
theorem fullMatrix_complexFullCubic_product (x y : FullHermitian) :
    fullMatrix (complexFullCubic.L x y) = symmetricMatrixProduct (fullMatrix x) (fullMatrix y) :=
  complexFullJordan_matrix x y

private theorem fullCubic_apply_trace (x y z : FullHermitian) :
    complexFullCubic.apply x y z =
      (Matrix.trace (symmetricMatrixProduct (symmetricMatrixProduct (fullMatrix x) (fullMatrix y))
        (fullMatrix z))).re := by
  change inner ℝ (complexFullJordan x y) z = _
  rw [fullInner_eq_tracePairing, complexFullJordan_matrix, tracePairing_eq_re_trace_jordan]

/-- The literal trace-of-three-points formula for standalone complex Hermitian frame planes. -/
theorem complex_shareOfThreePlanes_eq_frame_trace
    (F G H : ComplexTraceFrame3)
    (orth : Submodule.IsOrtho (𝕜 := ℝ) (E := TracelessHermitian3) F.plane G.plane)
    (orthW : Submodule.IsOrtho (𝕜 := ℝ) (E := TracelessHermitian3) F.plane H.plane)
    (orth'W : Submodule.IsOrtho (𝕜 := ℝ) (E := TracelessHermitian3) G.plane H.plane) :
    shareOfThreePlanes matrixEqualCubic F.plane G.plane H.plane =
      6 * ∑ a, ∑ b, ∑ d,
        ((Matrix.trace (symmetricMatrixProduct (symmetricMatrixProduct (F.point a) (G.point b))
          (H.point d))).re - 1 / 9) ^ 2 := by
  have round : IsRound matrixEqualCubic (1 / 6) := by
    refine ⟨by norm_num, fun x => ?_⟩
    rw [matrixEqualCubic_squareMap, TracelessHermitian3.square_norm_sq]
    ring
  have metric (x y z : TracelessHermitian3) :
      matrixEqualCubic.apply x y z =
        complexFullCubic.apply (complexTraceInclusion x) (complexTraceInclusion y) (complexTraceInclusion z) := by
    change inner ℝ (TracelessHermitian3.jordan x y) z =
      inner ℝ (complexFullJordan (complexTraceInclusion x) (complexTraceInclusion y)) (complexTraceInclusion z)
    rw [TracelessHermitian3.inner_eq_tracePairing, fullInner_eq_tracePairing,
      TracelessHermitian3.toMatrix_jordan, complexFullJordan_matrix,
      tracePairing_traceFreePart_left _ _ z.trace_eq_zero]
    rfl
  rw [shareOfThreePlanes_eq_centered_frame_trace round orth orthW orth'W
    F.plane_closed G.plane_closed F.plane_dimension
    complexFullCubic complexUnit_mul metric (complexFrameData F) (complexFrameData G) (complexFrameData H)]
  simp only [fullCubic_apply_trace, complexFrameData, fullMatrix_ofFullMatrix]

end
end ThirteenPlanes.RoundCubics
