module

public import ThirteenPlanes.Cartan.ClassicalQuaternionicLie
public import Mathlib.Algebra.Lie.Classical
public import SubalgebraCoordsAndLine

@[expose] public section

set_option backward.privateInPublic true

/-! The standard compact real form in the literal complex symplectic matrix algebra. -/

namespace ThirteenPlanes.Cartan

open Matrix
open scoped Matrix

noncomputable section

abbrev Sp6Matrix := Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ

/-- The complex symplectic Lie algebra for Mathlib's standard symplectic matrix. -/
abbrev complexSp6 := LieAlgebra.Symplectic.sp (Fin 3) ℂ

private abbrev Block := Matrix (Fin 3) (Fin 3) ℂ

private theorem mem_sp6_blocks (A B C D : Block) :
    fromBlocks A B C D ∈ complexSp6 ↔ Bᵀ = B ∧ Cᵀ = C ∧ D = -Aᵀ := by
  change fromBlocks A B C D ∈ skewAdjointMatricesLieSubalgebra (Matrix.J (Fin 3) ℂ) ↔ _
  rw [mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  rw [Matrix.J, fromBlocks_transpose, fromBlocks_neg, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, zero_add, add_zero, neg_neg, neg_zero, fromBlocks_inj, neg_inj]
  constructor
  · rintro ⟨hC, hDA, _, hB⟩
    exact ⟨hB, hC, hDA.symm⟩
  · rintro ⟨hB, hC, rfl⟩
    simp [hB, hC]

/-- The usual compact conjugation sends a complex symplectic matrix to its negative adjoint. -/
def standardSp6Conjugation (X : complexSp6) : complexSp6 := by
  refine ⟨-X.valᴴ, ?_⟩
  have hX := X.property
  nth_rw 1 [← fromBlocks_toBlocks X.val] at hX
  obtain ⟨hB,hC,hD⟩ := (mem_sp6_blocks _ _ _ _).mp hX
  rw [← fromBlocks_toBlocks X.val, fromBlocks_conjTranspose, fromBlocks_neg, mem_sp6_blocks]
  refine ⟨?_, ?_, ?_⟩
  · simp only [transpose_neg, neg_inj, conjTranspose]
    exact congrArg (fun v : Block => v.map star) hC.symm
  · simp only [transpose_neg, neg_inj, conjTranspose]
    exact congrArg (fun v : Block => v.map star) hB.symm
  · rw [hD]
    apply Matrix.ext
    intro i j
    simp [Matrix.conjTranspose_apply]

@[simp] theorem standardSp6Conjugation_val (X : complexSp6) :
    (standardSp6Conjugation X).val = -X.valᴴ := rfl

@[simp] theorem standardSp6Conjugation_involutive (X : complexSp6) :
    standardSp6Conjugation (standardSp6Conjugation X) = X := by
  apply Subtype.ext
  simp

@[simp] theorem standardSp6Conjugation_add (X Y : complexSp6) :
    standardSp6Conjugation (X + Y) = standardSp6Conjugation X + standardSp6Conjugation Y := by
  apply Subtype.ext
  simp [add_comm]

@[simp] theorem standardSp6Conjugation_smul (z : ℂ) (X : complexSp6) :
    standardSp6Conjugation (z • X) = star z • standardSp6Conjugation X := by
  apply Subtype.ext
  simp

@[simp] theorem standardSp6Conjugation_lie (X Y : complexSp6) :
    standardSp6Conjugation ⁅X,Y⁆ = ⁅standardSp6Conjugation X, standardSp6Conjugation Y⁆ := by
  apply Subtype.ext
  change -(X.val * Y.val - Y.val * X.val)ᴴ =
    -X.valᴴ * -Y.valᴴ - -Y.valᴴ * -X.valᴴ
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, neg_sub,
    neg_mul_neg, neg_mul_neg]

open AlbertSequential in
private def quaternionMatrixIndex : (Fin 3 ⊕ Fin 3) ≃ Fin 6 :=
  (show (Fin 3 ⊕ Fin 3) ≃ Fin 3 × Fin 2 from
    { toFun := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
      invFun := fun p => if p.2 = 0 then .inl p.1 else .inr p.1
      left_inv := by intro x; cases x <;> simp
      right_inv := by rintro ⟨i,j⟩; fin_cases j <;> simp }).trans fin3ProdFin2Equiv6

private def qMatrixComplex (X : QuaternionicMUB.QMat) : Sp6Matrix :=
  Matrix.reindex quaternionMatrixIndex.symm quaternionMatrixIndex.symm
    (AlbertSequential.symplecticQuatMat6 X)

private def qMatrixFront (X : QuaternionicMUB.QMat) : Block :=
  fun i j => ⟨(X i j).re, (X i j).imI⟩

private def qMatrixCross (X : QuaternionicMUB.QMat) : Block :=
  fun i j => ⟨(X i j).imJ, (X i j).imK⟩

private theorem qMatrixComplex_blocks (X : QuaternionicMUB.QMat) :
    qMatrixComplex X = fromBlocks (qMatrixFront X) (qMatrixCross X)
      (-(qMatrixCross X).map star) ((qMatrixFront X).map star) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [qMatrixComplex, Matrix.reindex_apply, quaternionMatrixIndex, AlbertSequential.symplecticQuatMat6,
      AlbertSequential.quatMat2, qMatrixFront, qMatrixCross] <;> apply Complex.ext <;> simp

private theorem qMatrixComplex_add (A B : QuaternionicMUB.QMat) :
    qMatrixComplex (A + B) = qMatrixComplex A + qMatrixComplex B := by
  rw [qMatrixComplex, AlbertSequential.symplecticQuatMat6_add]
  rfl

private theorem qMatrixComplex_smul (r : ℝ) (A : QuaternionicMUB.QMat) :
    qMatrixComplex (r • A) = r • qMatrixComplex A := by
  rw [qMatrixComplex, AlbertSequential.symplecticQuatMat6_smul]
  rfl

private theorem qMatrixComplex_mul (A B : QuaternionicMUB.QMat) :
    qMatrixComplex (A * B) = qMatrixComplex A * qMatrixComplex B := by
  simp only [qMatrixComplex, AlbertSequential.symplecticQuatMat6_mul]
  exact map_mul (Matrix.reindexAlgEquiv ℂ ℂ quaternionMatrixIndex.symm) _ _

private theorem qMatrixComplex_star (A : QuaternionicMUB.QMat) :
    qMatrixComplex Aᴴ = (qMatrixComplex A)ᴴ := by
  change (Matrix.reindex quaternionMatrixIndex.symm quaternionMatrixIndex.symm)
      (AlbertSequential.symplecticQuatMat6 (star A)) = _
  rw [AlbertSequential.symplecticQuatMat6_star]
  rfl

private theorem qMatrixComplex_injective : Function.Injective qMatrixComplex :=
  fun _ _ h => AlbertSequential.symplecticQuatMat6_injective
    ((Matrix.reindex quaternionMatrixIndex.symm quaternionMatrixIndex.symm).injective h)

private theorem qMatrixComplex_neg (A : QuaternionicMUB.QMat) :
    qMatrixComplex (-A) = -qMatrixComplex A := by
  simpa only [neg_one_smul] using qMatrixComplex_smul (-1) A

private theorem qMatrixComplex_sub (A B : QuaternionicMUB.QMat) :
    qMatrixComplex (A - B) = qMatrixComplex A - qMatrixComplex B := by
  simp only [sub_eq_add_neg, qMatrixComplex_add, qMatrixComplex_neg]

private theorem qMatrixComplex_symplectic (A : compactSp3) : qMatrixComplex A.val ∈ complexSp6 := by
  rw [qMatrixComplex_blocks, mem_sp6_blocks]
  have h (i j : Fin 3) : star (A.val j i) = -A.val i j :=
    congrFun (congrFun A.property i) j
  have hB : (qMatrixCross A.val)ᵀ = qMatrixCross A.val := by
    apply Matrix.ext
    intro i j
    apply Complex.ext
    · simpa [qMatrixCross] using congrArg (fun q : QuaternionicMUB.Q => -q.imJ) (h i j)
    · simpa [qMatrixCross] using congrArg (fun q : QuaternionicMUB.Q => -q.imK) (h i j)
  refine ⟨hB, ?_, ?_⟩
  · rw [Matrix.transpose_neg, neg_inj]
    exact congrArg (fun X : Block => X.map star) hB
  · apply Matrix.ext
    intro i j
    apply Complex.ext
    · simpa [qMatrixFront] using congrArg (fun q : QuaternionicMUB.Q => q.re) (h j i)
    · simpa [qMatrixFront] using congrArg (fun q : QuaternionicMUB.Q => q.imI) (h j i)

/-- The native quaternionic skew-Hermitian model in the complex symplectic algebra. -/
def compactSp3ComplexEmbed (X : compactSp3) : complexSp6 :=
  ⟨qMatrixComplex X.val, qMatrixComplex_symplectic X⟩

theorem compactSp3ComplexEmbed_injective : Function.Injective compactSp3ComplexEmbed :=
  fun _ _ h => Subtype.ext (qMatrixComplex_injective (congrArg Subtype.val h))

@[simp] theorem compactSp3ComplexEmbed_add (A B : compactSp3) :
    compactSp3ComplexEmbed (A + B) = compactSp3ComplexEmbed A + compactSp3ComplexEmbed B :=
  Subtype.ext (qMatrixComplex_add _ _)

@[simp] theorem compactSp3ComplexEmbed_smul (r : ℝ) (A : compactSp3) :
    compactSp3ComplexEmbed (r • A) = (r : ℂ) • compactSp3ComplexEmbed A :=
  Subtype.ext (qMatrixComplex_smul _ _)

@[simp] theorem compactSp3ComplexEmbed_lie (A B : compactSp3) :
    compactSp3ComplexEmbed ⁅A,B⁆ = ⁅compactSp3ComplexEmbed A, compactSp3ComplexEmbed B⁆ := by
  apply Subtype.ext
  change qMatrixComplex (A.val * B.val - B.val * A.val) =
    qMatrixComplex A.val * qMatrixComplex B.val - qMatrixComplex B.val * qMatrixComplex A.val
  rw [qMatrixComplex_sub, qMatrixComplex_mul, qMatrixComplex_mul]

@[simp] theorem standardSp6Conjugation_embed (A : compactSp3) :
    standardSp6Conjugation (compactSp3ComplexEmbed A) = compactSp3ComplexEmbed A := by
  apply Subtype.ext
  change -(qMatrixComplex A.val)ᴴ = qMatrixComplex A.val
  rw [← qMatrixComplex_star, A.property, qMatrixComplex_neg, neg_neg]

/-- The fixed algebra of the standard compact conjugation is precisely compact sp(3). -/
theorem standardSp6Conjugation_fixed_iff (X : complexSp6) :
    standardSp6Conjugation X = X ↔ ∃ A : compactSp3, compactSp3ComplexEmbed A = X := by
  constructor
  · intro hX
    let P := X.val.toBlocks₁₁
    let Q := X.val.toBlocks₁₂
    let R := X.val.toBlocks₂₁
    let S := X.val.toBlocks₂₂
    have he : fromBlocks P Q R S = X.val := fromBlocks_toBlocks X.val
    have h := X.property
    rw [← he, mem_sp6_blocks] at h
    obtain ⟨hQ, _, hS⟩ := h
    have hh := congrArg Subtype.val hX
    change -X.valᴴ = X.val at hh
    rw [← he, fromBlocks_conjTranspose, fromBlocks_neg, fromBlocks_inj] at hh
    obtain ⟨hP, _, hR, _⟩ := hh
    let A : QuaternionicMUB.QMat := fun i j => ⟨(P i j).re, (P i j).im, (Q i j).re, (Q i j).im⟩
    have h' : qMatrixComplex A = X.val := by
      rw [← he, qMatrixComplex_blocks A, fromBlocks_inj]
      have hP' : P.map star = -Pᵀ := by
        apply Matrix.ext
        intro i j
        have he := congrFun (congrFun hP j) i
        exact neg_eq_iff_eq_neg.mp he
      have heQ : Qᴴ = Q.map star := congrArg (fun M : Block => M.map star) hQ
      rw [heQ] at hR
      exact ⟨rfl, rfl, hR, hP'.trans hS.symm⟩
    have hA : Aᴴ = -A := by
      apply qMatrixComplex_injective
      rw [qMatrixComplex_star, qMatrixComplex_neg, h']
      exact neg_eq_iff_eq_neg.mp (congrArg Subtype.val hX)
    exact ⟨⟨A, hA⟩, Subtype.ext h'⟩
  · rintro ⟨A, rfl⟩
    exact standardSp6Conjugation_embed A

end
end ThirteenPlanes.Cartan
