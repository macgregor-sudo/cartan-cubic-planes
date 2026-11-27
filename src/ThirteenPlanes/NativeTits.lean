/- SPDX-License-Identifier: Apache-2.0
The compact coordinates specialize TitsS.titsOfNative from tight-39-code,
Proofs/TitsForm.lean at 46f01c135aacea9003435e7f1dc99b4a69568e83, in the
pinned native carrier. The third slot here is the conjugate transpose. -/
module

public import ThirteenPlanes.SignedTits
public import ThirteenPlanes.NativeFramesCarrier

@[expose] public section

set_option backward.privateInPublic true

open scoped Matrix RealInnerProductSpace BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes

noncomputable section

private def octHead (q : Glennie.Octonion) : ℂ := ⟨q.1.re, q.1.imI⟩

private def octTail (q : Glennie.Octonion) : Fin 3 → ℂ :=
  ![⟨-q.1.imJ, q.1.imK⟩, ⟨-q.2.re, q.2.imI⟩, ⟨-q.2.imJ, -q.2.imK⟩]

private def nativeTitsA (x : Glennie.Albert) : Mat3 ℂ :=
  ![![x.d0, octHead x.o01, octHead x.o02],
    ![star (octHead x.o01), x.d1, octHead x.o12],
    ![star (octHead x.o02), star (octHead x.o12), x.d2]]

private def nativeTitsB (x : Glennie.Albert) : Mat3 ℂ :=
  ![octTail x.o12, -octTail x.o02, octTail x.o01]

private theorem nativeTitsA_hermitian (x : Glennie.Albert) : (nativeTitsA x).IsHermitian := by
  change (nativeTitsA x)ᴴ = nativeTitsA x
  ext i j
  change star (nativeTitsA x j i) = nativeTitsA x i j
  fin_cases i <;> fin_cases j <;> simp [nativeTitsA]

private def nativeTitsValue (x : Glennie.Albert) : Tits.CompactTits :=
  Tits.CompactTits.ofMatrices (nativeTitsA x) (nativeTitsB x) (nativeTitsA_hermitian x)

private theorem nativeTitsValue_coordinates (x : Glennie.Albert) :
    Tits.CompactTits.coordinates (nativeTitsValue x) =
      (nativeTitsA x, nativeTitsB x, (nativeTitsB x)ᴴ) := rfl

private theorem nativeTitsA_add (x y : Glennie.Albert) :
    nativeTitsA (x+y) = nativeTitsA x + nativeTitsA y := by
  ext i j
  change nativeTitsA (x+y) i j = nativeTitsA x i j + nativeTitsA y i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [nativeTitsA, octHead, add_comm]

private theorem nativeTitsB_add (x y : Glennie.Albert) :
    nativeTitsB (x+y) = nativeTitsB x + nativeTitsB y := by
  ext i j
  change nativeTitsB (x+y) i j = nativeTitsB x i j + nativeTitsB y i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [nativeTitsB, octTail, add_comm]

private theorem nativeTitsA_smul (r : ℝ) (x : Glennie.Albert) :
    nativeTitsA (r • x) = r • nativeTitsA x := by
  ext i j
  change nativeTitsA (r • x) i j = r • nativeTitsA x i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [nativeTitsA, octHead]

private theorem nativeTitsB_smul (r : ℝ) (x : Glennie.Albert) :
    nativeTitsB (r • x) = r • nativeTitsB x := by
  ext i j
  change nativeTitsB (r • x) i j = r • nativeTitsB x i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [nativeTitsB, octTail]

/-- The explicit native Cayley–Dickson coordinates in the compact first Tits carrier. -/
def nativeToCompactTits : Glennie.Albert →ₗ[ℝ] Tits.CompactTits where
  toFun := nativeTitsValue
  map_add' x y := Tits.CompactTits.ext (by
    simp only [nativeTitsValue_coordinates, map_add, nativeTitsA_add, nativeTitsB_add,
      Matrix.conjTranspose_add, Prod.mk_add_mk])
  map_smul' r x := Tits.CompactTits.ext (by
    simp only [nativeTitsValue_coordinates, map_smul, nativeTitsA_smul, nativeTitsB_smul,
      Matrix.conjTranspose_smul, star_trivial, Prod.smul_mk, RingHom.id_apply])

theorem nativeToCompactTits_coordinates (x : Glennie.Albert) :
    Tits.CompactTits.coordinates (nativeToCompactTits x) =
      (nativeTitsA x, nativeTitsB x, (nativeTitsB x)ᴴ) := rfl

theorem nativeToCompactTits_trace (x : Glennie.Albert) :
    Tits.CompactTits.trace (nativeToCompactTits x) = Glennie.trace x := by
  rw [Tits.CompactTits.trace_apply, nativeToCompactTits_coordinates]
  simp [trace3, nativeTitsA, Glennie.trace]

private theorem nativeSquare_value (x : Glennie.Albert) :
    Glennie.jordan x x =
      Glennie.fromMatrix (Glennie.matrixMul (Glennie.toMatrix x) (Glennie.toMatrix x)) := by
  unfold Glennie.jordan
  rw [← two_smul ℝ, smul_smul]
  norm_num

private theorem firstTitsSquare_A_entry (A B C : Mat3 ℂ) (i j : Fin 3) :
    (firstTitsSquare (A, B, C)).1 i j =
      (∑ k, A i k * A k j) - (∑ k, B i k * C k j) +
        trace3 (B*C) * (1 : Mat3 ℂ) i j := by
  change (A*A - B*C + trace3 (B*C) • (1 : Mat3 ℂ)) i j = _
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]

private theorem firstTitsSquare_B_entry (A B C : Mat3 ℂ) (i j : Fin 3) :
    (firstTitsSquare (A, B, C)).2.1 i j =
      adjugate3 C i j - (∑ k, A i k * B k j) + trace3 A * B i j := by
  change (adjugate3 C - A*B + trace3 A • B) i j = _
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]

private theorem trace3_mul_entries (A B : Mat3 ℂ) :
    trace3 (A*B) = (∑ k, A 0 k * B k 0) + (∑ k, A 1 k * B k 1) +
      (∑ k, A 2 k * B k 2) := by
  simp only [trace3, Matrix.mul_apply]

private theorem nativeTitsB_adjoint_apply (x : Glennie.Albert) (i j : Fin 3) :
    (nativeTitsB x)ᴴ i j = star (nativeTitsB x j i) := rfl

set_option maxHeartbeats 3000000 in
private theorem nativeToCompactTits_square_A (x : Glennie.Albert) :
    nativeTitsA (Glennie.jordan x x) =
      (firstTitsSquare (nativeTitsA x, nativeTitsB x, (nativeTitsB x)ᴴ)).1 := by
  ext i j
  rw [firstTitsSquare_A_entry, trace3_mul_entries, nativeSquare_value]
  simp only [Fin.sum_univ_three, nativeTitsB_adjoint_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals
    simp [nativeTitsA, nativeTitsB, octHead, octTail, Glennie.fromMatrix, Glennie.toMatrix,
      Glennie.matrixMul, Glennie.octRe, Glennie.octMul, Glennie.octConj, Glennie.octScalar,
      Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  all_goals ring

set_option maxHeartbeats 3000000 in
private theorem nativeToCompactTits_square_B (x : Glennie.Albert) :
    nativeTitsB (Glennie.jordan x x) =
      (firstTitsSquare (nativeTitsA x, nativeTitsB x, (nativeTitsB x)ᴴ)).2.1 := by
  ext i j
  rw [firstTitsSquare_B_entry, nativeSquare_value]
  simp only [adjugate3, Fin.sum_univ_three, nativeTitsB_adjoint_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals
    simp [nativeTitsA, nativeTitsB, octHead, octTail, trace3, Glennie.fromMatrix,
      Glennie.toMatrix, Glennie.matrixMul, Glennie.octMul, Glennie.octConj, Glennie.octScalar,
      Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem nativeToCompactTits_square (x : Glennie.Albert) :
    nativeToCompactTits (Glennie.jordan x x) = Tits.CompactTits.square (nativeToCompactTits x) := by
  apply Tits.CompactTits.ext
  let Y := Tits.CompactTits.square (nativeToCompactTits x)
  have hY : Tits.CompactTits.coordinates Y =
      firstTitsSquare (nativeTitsA x, nativeTitsB x, (nativeTitsB x)ᴴ) := by
    rw [Tits.CompactTits.coordinates_square, nativeToCompactTits_coordinates]
  change Tits.CompactTits.coordinates (nativeToCompactTits (Glennie.jordan x x)) =
    Tits.CompactTits.coordinates Y
  rw [nativeToCompactTits_coordinates]
  have ha := (nativeToCompactTits_square_A x).trans (congrArg Prod.fst hY).symm
  have hb := (nativeToCompactTits_square_B x).trans (congrArg (fun t => t.2.1) hY).symm
  exact Prod.ext ha (Prod.ext hb ((congrArg Matrix.conjTranspose hb).trans
    (Tits.CompactTits.third_eq_adjoint Y).symm))

private theorem nativeProduct_polar (x y : Glennie.Albert) :
    (1 / 2 : ℝ) • (Glennie.jordan (x+y) (x+y) - Glennie.jordan x x - Glennie.jordan y y) =
      Glennie.jordan x y := by
  have hp : Glennie.jordan (x+y) (x+y) - Glennie.jordan x x - Glennie.jordan y y =
      Glennie.jordan x y + Glennie.jordan x y := by
    change Glennie.jordanLinear (x+y) (x+y) - Glennie.jordanLinear x x -
      Glennie.jordanLinear y y = _
    simp only [map_add, LinearMap.add_apply]
    simp only [Glennie.jordanLinear_apply]
    rw [Glennie.jordan_comm y x]
    abel
  rw [hp, ← two_smul ℝ, smul_smul]
  norm_num

/-- The explicit coordinate map preserves the full native Jordan product. -/
theorem nativeToCompactTits_product (x y : Glennie.Albert) :
    nativeToCompactTits (Glennie.jordan x y) =
      Tits.CompactTits.product (nativeToCompactTits x) (nativeToCompactTits y) := by
  rw [← nativeProduct_polar x y, map_smul, map_sub, map_sub, nativeToCompactTits_square,
    nativeToCompactTits_square, nativeToCompactTits_square, map_add]
  rfl

@[simp] theorem nativeToCompactTits_one :
    nativeToCompactTits (1 : Glennie.Albert) = Tits.CompactTits.one := by
  apply Tits.CompactTits.ext
  rw [nativeToCompactTits_coordinates, Tits.CompactTits.coordinates_one]
  have hA : nativeTitsA (1 : Glennie.Albert) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [nativeTitsA, octHead]
  have hB : nativeTitsB (1 : Glennie.Albert) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [nativeTitsB, octTail]
  simp [firstTitsOne, hA, hB]

private theorem nativeToCompactTits_norm (x : Glennie.Albert) :
    ‖nativeToCompactTits x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Tits.CompactTits.trace_square, ← nativeToCompactTits_square,
    nativeToCompactTits_trace, Glennie.native_norm_sq]
  rfl

theorem compactTits_finrank : Module.finrank ℝ Tits.CompactTits = 27 := by
  have hsurj : Function.Surjective Tits.CompactTits.trace := by
    intro r
    refine ⟨(r/3 : ℝ) • Tits.CompactTits.one, ?_⟩
    rw [map_smul, Tits.CompactTits.trace_one, smul_eq_mul]
    ring
  have hker : Module.finrank ℝ Tits.CompactTitsTraceless = 26 :=
    gradedTitsEquiv.toLinearEquiv.finrank_eq.symm.trans signedField_finrank
  have hd := Tits.CompactTits.trace.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hd
  change 1 + Module.finrank ℝ Tits.CompactTitsTraceless = _ at hd
  rw [hker] at hd
  omega

/-- The compact first-Tits real form is the actual native octonionic Albert algebra. -/
def nativeCompactTitsEquiv : Glennie.Albert ≃ₗᵢ[ℝ] Tits.CompactTits := by
  let f : Glennie.Albert →ₗᵢ[ℝ] Tits.CompactTits :=
    ⟨nativeToCompactTits, nativeToCompactTits_norm⟩
  have hdim : Module.finrank ℝ Glennie.Albert = Module.finrank ℝ Tits.CompactTits :=
    Glennie.albert_finrank.trans compactTits_finrank.symm
  let e := LinearEquiv.ofBijective nativeToCompactTits
    ⟨f.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp f.injective⟩
  exact ⟨e, nativeToCompactTits_norm⟩

/- This identifies the product on the native Albert algebra with Jacques Tits's first
construction in compact coordinates. See Yokota, Exceptional Lie Groups, §2.12
(arXiv:0902.0431), and the earlier AI-generated paper hexagon:2611.00340v2, §4.2, Eqs. (10)–(11),
and Appendix A.1. -/
theorem nativeCompactTitsEquiv_product (x y : Glennie.Albert) :
    nativeCompactTitsEquiv (Glennie.jordan x y) =
      Tits.CompactTits.product (nativeCompactTitsEquiv x) (nativeCompactTitsEquiv y) :=
  nativeToCompactTits_product x y

@[simp] theorem nativeCompactTitsEquiv_trace (x : Glennie.Albert) :
    Tits.CompactTits.trace (nativeCompactTitsEquiv x) = Glennie.trace x :=
  nativeToCompactTits_trace x

@[simp] theorem nativeCompactTitsEquiv_one :
    nativeCompactTitsEquiv (1 : Glennie.Albert) = Tits.CompactTits.one :=
  nativeToCompactTits_one

/-- The positive trace makes the compact fixed form formally real. -/
theorem compactTits_formallyReal {ι : Type*} [Fintype ι] {x : ι → Tits.CompactTits}
    (h : ∑ i, Tits.CompactTits.square (x i) = 0) : ∀ i, x i = 0 := by
  have ht := congrArg Tits.CompactTits.trace h
  simp only [map_sum, map_zero, Tits.CompactTits.trace_square] at ht
  intro i
  have hnorm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖x j‖)).mp ht i
    (Finset.mem_univ i)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

end

end ThirteenPlanes
