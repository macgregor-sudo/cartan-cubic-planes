module

public import ThirteenPlanes.Cartan.AlbertDerivationComplex
public import ThirteenPlanes.Cartan.AlbertDerivationComplexCoordinates

@[expose] public section

set_option backward.privateInPublic true

/-! Conjugation, trace skewness, and the compact trace metric of the native derivations. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading
open scoped RealInnerProductSpace

noncomputable section

/-- The compact conjugation of a complex derivation. -/
def conjAlbertDerivation (D : ComplexAlbertDerivations) : ComplexAlbertDerivations :=
  extendAlbertDerivation (complexDerivationRealPart D) -
    Complex.I • extendAlbertDerivation (complexDerivationImagPart D)

/-- Conjugation acts on the actual endomorphism by the real-structure involution on both sides. -/
theorem conjAlbertDerivation_apply (D : ComplexAlbertDerivations) (x : JC) :
    (conjAlbertDerivation D).val x = JC.conj (D.val (JC.conj x)) := by
  let A := (complexDerivationRealPart D).val
  let B := (complexDerivationImagPart D).val
  have hD (x : JC) : D.val x = JC.mapC A x + Complex.I • JC.mapC B x := by
    have h := congrArg (fun d : ComplexAlbertDerivations => d.val x)
      (complexAlbertDerivation_decompose D)
    exact h.symm
  change JC.mapC A x - Complex.I • JC.mapC B x = JC.conj (D.val (JC.conj x))
  rw [hD, JC.conj_add, JC.mapC_conj, JC.mapC_conj, JC.conj_smul, JC.conj_conj, JC.conj_conj,
    Complex.star_def, Complex.conj_I, neg_smul, sub_eq_add_neg]

@[simp] theorem conjAlbertDerivation_conj (D : ComplexAlbertDerivations) :
    conjAlbertDerivation (conjAlbertDerivation D) = D := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rw [conjAlbertDerivation_apply, conjAlbertDerivation_apply, JC.conj_conj, JC.conj_conj]

theorem albertDerivationComplexEquiv_conjugation (x : LieComplex NativeAlbertDerivations) :
    albertDerivationComplexEquiv (LieComplex.conjugation x) =
      conjAlbertDerivation (albertDerivationComplexEquiv x) := by
  change albertDerivationComplexMap (LieComplex.conjugation x) =
    conjAlbertDerivation (albertDerivationComplexMap x)
  rw [LieComplex.conjugation_decompose, map_sub, map_smul,
    albertDerivationComplexMap_ofReal, albertDerivationComplexMap_ofReal, conjAlbertDerivation,
    realPart_albertDerivationComplexMap, imagPart_albertDerivationComplexMap]

/-- A real-preserving complex derivation is the unique extension of its real part. -/
theorem extendAlbertDerivation_realPart_of_conj_fixed (D : ComplexAlbertDerivations)
    (h : conjAlbertDerivation D = D) :
    extendAlbertDerivation (complexDerivationRealPart D) = D := by
  apply Subtype.ext
  apply jc_endomorphism_ext
  intro x
  have hc := (conjAlbertDerivation_apply D (JC.of x)).symm
  rw [h, JC.conj_of] at hc
  rw [JC.conj_eq_self_iff] at hc
  rw [extendAlbertDerivation_val, JC.mapC_of, complexDerivationRealPart_apply]
  exact hc.symm

/-- Native real derivations act faithfully on the literal traceless representation. -/
def nativeAlbertDerivationTraceEquiv : NativeAlbertDerivations ≃ₗ[ℝ] albertDerivationOperators :=
  nativeAlbertDerivationSkewEquiv.trans
    (LinearEquiv.ofInjective albertJordan.restrictDerivation albertJordan.restrictDerivation_injective)

@[simp] theorem nativeAlbertDerivationTraceEquiv_apply (D : NativeAlbertDerivations)
    (x : albertJordan.traceFree) :
    ((nativeAlbertDerivationTraceEquiv D).val.val x).val = D.val x.val :=
  rfl

/-- The faithful traceless action carries the native bracket to the operator commutator. -/
theorem nativeAlbertDerivationTraceEquiv_bracket (D E : NativeAlbertDerivations) :
    (nativeAlbertDerivationTraceEquiv ⁅D, E⁆).val.val =
      operatorBracket (nativeAlbertDerivationTraceEquiv D).val.val
        (nativeAlbertDerivationTraceEquiv E).val.val := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

private theorem realAlbert_jc_ip_skew (D : NativeAlbertDerivations) (x y : JC) :
    JC.ip (JC.mapC D.val x) y = - JC.ip x (JC.mapC D.val y) := by
  have h (a b : Glennie.Albert) : Glennie.inner (D.val a) b = -Glennie.inner a (D.val b) := by
    simpa only [Glennie.hilbert_inner_eq_native] using nativeAlbertDerivation_skew D a b
  apply Complex.ext
  · simp only [JC.ip_re, JC.mapC_re, JC.mapC_im, Complex.neg_re, h]
    ring
  · simp only [JC.ip_im, JC.mapC_re, JC.mapC_im, Complex.neg_im, h]
    ring

/-- Every complex derivation is skew for the complex-bilinear trace form. -/
theorem complexAlbertDerivation_ip_skew (D : ComplexAlbertDerivations) (x y : JC) :
    JC.ip (D.val x) y = -JC.ip x (D.val y) := by
  have h := complexAlbertDerivation_decompose D
  rw [← h]
  change JC.ip (JC.mapC (complexDerivationRealPart D).val x +
    Complex.I • JC.mapC (complexDerivationImagPart D).val x) y =
    -JC.ip x (JC.mapC (complexDerivationRealPart D).val y +
    Complex.I • JC.mapC (complexDerivationImagPart D).val y)
  rw [JC.ip_add_left, JC.ip_smul_left, JC.ip_add_right, JC.ip_smul_right, realAlbert_jc_ip_skew,
    realAlbert_jc_ip_skew]
  ring

theorem complexAlbertDerivation_unit_zero (D : ComplexAlbertDerivations) : D.val JC.one = 0 := by
  have hh := (mem_complexAlbertDerivations.mp D.property) JC.one JC.one
  rw [JC.one_mul, JC.mul_one, JC.one_mul] at hh
  exact left_eq_add.mp hh

/-- The actual complex derivations preserve the trace kernel. -/
theorem complexAlbertDerivation_trace_zero (D : ComplexAlbertDerivations) (x : JC) :
    JC.tr (D.val x) = 0 := by
  have h := complexAlbertDerivation_ip_skew D JC.one x
  rw [complexAlbertDerivation_unit_zero, JC.ip_zero_left, JC.ip_one_left] at h
  exact (neg_eq_zero.mp h.symm)

private theorem jc_mapC_neg (A : Module.End ℝ Glennie.Albert) :
    JC.mapC (-A) = -JC.mapC A := by
  apply LinearMap.ext
  intro x
  apply JC.ext <;> rfl

private theorem complexAlbertDerivation_re_trace (D : ComplexAlbertDerivations) :
    (LinearMap.trace ℂ JC (D.val * (conjAlbertDerivation D).val)).re =
      LinearMap.trace ℝ Glennie.Albert ((complexDerivationRealPart D).val * (complexDerivationRealPart D).val) +
      LinearMap.trace ℝ Glennie.Albert ((complexDerivationImagPart D).val * (complexDerivationImagPart D).val) := by
  let A := (complexDerivationRealPart D).val
  let B := (complexDerivationImagPart D).val
  have hD : D.val = JC.mapC A + Complex.I • JC.mapC B := by
    exact (congrArg Subtype.val (complexAlbertDerivation_decompose D)).symm
  have hbar : (conjAlbertDerivation D).val = JC.mapC A + Complex.I • JC.mapC (-B) := by
    rw [jc_mapC_neg, smul_neg, ← sub_eq_add_neg]
    rfl
  have h := congrArg Complex.re (jcTraceForm_realImag A B A (-B))
  simp only [← hD, ← hbar, Complex.neg_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    mul_neg, map_neg] at h
  linarith only [h]

/-- The conjugate partner of any nonzero complex derivation gives a strictly negative
operator-trace pairing. In a character grade the partner lies in the opposite grade. -/
theorem complexAlbertDerivation_trace_conjugate_neg (D : ComplexAlbertDerivations) (hne : D ≠ 0) :
    (LinearMap.trace ℂ JC (D.val * (conjAlbertDerivation D).val)).re < 0 := by
  let A : SkewOperator Glennie.Albert :=
    ⟨(complexDerivationRealPart D).val, nativeAlbertDerivation_skew _⟩
  let B : SkewOperator Glennie.Albert :=
    ⟨(complexDerivationImagPart D).val, nativeAlbertDerivation_skew _⟩
  have hab : A ≠ 0 ∨ B ≠ 0 := by
    by_contra! h
    have hA : complexDerivationRealPart D = 0 := Subtype.ext (congrArg (fun u : SkewOperator Glennie.Albert => u.val) h.1)
    have hB : complexDerivationImagPart D = 0 := Subtype.ext (congrArg (fun u : SkewOperator Glennie.Albert => u.val) h.2)
    apply hne
    have hd := complexAlbertDerivation_decompose D
    rw [hA, hB, map_zero, smul_zero, add_zero] at hd
    exact hd.symm
  have hsum : 0 < ⟪A, A⟫ + ⟪B, B⟫ := by
    rcases hab with hA | hB
    · exact add_pos_of_pos_of_nonneg (real_inner_self_pos.mpr hA) real_inner_self_nonneg
    · exact add_pos_of_nonneg_of_pos real_inner_self_nonneg (real_inner_self_pos.mpr hB)
  rw [skewOperator_inner, skewOperator_inner] at hsum
  rw [complexAlbertDerivation_re_trace]
  change (LinearMap.trace ℝ Glennie.Albert) (A.val * A.val) +
    (LinearMap.trace ℝ Glennie.Albert) (B.val * B.val) < 0
  linarith only [hsum]

end
end ThirteenPlanes.Cartan
