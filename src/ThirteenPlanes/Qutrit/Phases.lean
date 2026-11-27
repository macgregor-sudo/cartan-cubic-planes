module

public import AcceptedRootAtomAdapter
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

@[expose] public section

set_option backward.privateInPublic true

/-! Diagonal quaternionic unitary extensions by conjugacy of marked quaternionic windows. -/

namespace ThirteenPlanes.JordanFrames

open AlbertSequential
open scoped Matrix

noncomputable section

private def quatDiagonal (d : Fin 3 → Quaternion ℝ)
    (hd : ∀ i, d i * star (d i) = 1 ∧ star (d i) * d i = 1) :
    unitary QuatMatrix3 :=
  ⟨Matrix.diagonal d, Unitary.mem_iff.mpr (by
    change star (Matrix.diagonal d) * Matrix.diagonal d = 1 ∧
      Matrix.diagonal d * star (Matrix.diagonal d) = 1
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    constructor
    · rw [← Matrix.diagonal_one]
      exact congrArg Matrix.diagonal (funext fun i => (hd i).2)
    · rw [← Matrix.diagonal_one]
      exact congrArg Matrix.diagonal (funext fun i => (hd i).1))⟩

private def conjugateHermitian (C : QuatMatrix3 ≃⋆ₐ[ℝ] QuatMatrix3) :
    QuatHermitian3 →ₗ[ℝ] QuatHermitian3 where
  toFun x := ⟨C x.val, by
    rw [selfAdjoint.mem_iff, ← map_star, (show star x.val = x.val from x.prop)]⟩
  map_add' x y := Subtype.ext (map_add C x.val y.val)
  map_smul' r x := Subtype.ext (map_smul C r x.val)

private theorem conjugateHermitian_injective (C : QuatMatrix3 ≃⋆ₐ[ℝ] QuatMatrix3) :
    Function.Injective (conjugateHermitian C) := by
  intro x y h
  exact Subtype.ext (C.injective (congrArg Subtype.val h))

private theorem conjugateHermitian_surjective (C : QuatMatrix3 ≃⋆ₐ[ℝ] QuatMatrix3) :
    Function.Surjective (conjugateHermitian C) := by
  intro y
  refine ⟨conjugateHermitian C.symm y, Subtype.ext ?_⟩
  exact C.apply_symm_apply y.val

private theorem quatDiagonal_apply (d : Fin 3 → Quaternion ℝ)
    (hd : ∀ i, d i * star (d i) = 1 ∧ star (d i) * d i = 1)
    (M : QuatMatrix3) (i j : Fin 3) :
    Unitary.conjStarAlgAut ℝ QuatMatrix3 (quatDiagonal d hd) M i j =
      d i * M i j * star (d j) := by
  rw [Unitary.conjStarAlgAut_apply]
  change (Matrix.diagonal d * M * star (Matrix.diagonal d)) i j = _
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

/-- Conjugation by the diagonal quaternionic unitary with entries `d`. -/
def quaternionicDiagonalConjugation (d : Fin 3 → Quaternion ℝ)
    (hd : ∀ i, d i * star (d i) = 1 ∧ star (d i) * d i = 1) :
    QuatHermitian3 →ₗ[ℝ] QuatHermitian3 :=
  conjugateHermitian (Unitary.conjStarAlgAut ℝ QuatMatrix3 (quatDiagonal d hd))

theorem quaternionicDiagonalConjugation_apply (d : Fin 3 → Quaternion ℝ)
    (hd : ∀ i, d i * star (d i) = 1 ∧ star (d i) * d i = 1) (X : QuatHermitian3) :
    (quaternionicDiagonalConjugation d hd X).val =
      Matrix.diagonal d * X.val * star (Matrix.diagonal d) := by
  change Unitary.conjStarAlgAut ℝ QuatMatrix3 (quatDiagonal d hd) X.val = _
  rw [Unitary.conjStarAlgAut_apply]
  rfl

private theorem quatDiagonal_apply_diag (d : Fin 3 → Quaternion ℝ)
    (hd : ∀ i, d i * star (d i) = 1 ∧ star (d i) * d i = 1)
    (M : QuatHermitian3) (i : Fin 3) :
    Unitary.conjStarAlgAut ℝ QuatMatrix3 (quatDiagonal d hd) M.val i i = M.val i i := by
  have h : star (M.val i i) = M.val i i := congrArg (fun A : QuatMatrix3 => A i i) M.prop
  rw [quatDiagonal_apply,
    show d i * M.val i i * star (d i) = (M.val i i).re • (d i * star (d i)) by
      conv_lhs => rw [quat_eq_re_smul_one h]
      rw [mul_smul_comm, mul_one, smul_mul_assoc],
    (hd i).1, ← quat_eq_re_smul_one h]

private def transportQuaternionicWindow (Q : QuaternionicWindow) (d : Fin 3 → Quaternion ℝ)
    (hd : ∀ i, d i * star (d i) = 1 ∧ star (d i) * d i = 1) : QuaternionicWindow :=
  let C := Unitary.conjStarAlgAut ℝ QuatMatrix3 (quatDiagonal d hd)
  let f := conjugateHermitian C
  { subalgebra := Q.subalgebra
    embedding := Q.embedding.comp f
    injective := Q.injective.comp (conjugateHermitian_injective C)
    range_eq := by
      rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr (conjugateHermitian_surjective C),
        Submodule.map_top, Q.range_eq]
    unit := by
      rw [LinearMap.comp_apply, show f 1 = 1 from Subtype.ext (map_one C), Q.unit]
    preserves_product := by
      intro x y z hz
      apply Q.preserves_product
      change C z.val = (1 / 2 : ℝ) • (C x.val * C y.val + C y.val * C x.val)
      rw [hz, map_smul, map_add, map_mul, map_mul]
    preserves_trace := by
      intro x
      rw [LinearMap.comp_apply, Q.preserves_trace]
      change (C x.val 0 0).re + (C x.val 1 1).re + (C x.val 2 2).re = _
      simp only [C, quatDiagonal_apply_diag] }

private def quatDiagonalAtom (i : Fin 3) : QuatHermitian3 :=
  ⟨Matrix.diagonal fun j => if j = i then 1 else 0, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    by_cases h : j = i <;> simp [h]⟩

private theorem quaternionicWindow_diagAtom (φ : Quaternion ℝ →ₗ[ℝ] Octonion)
    (hφ : IsQuatEmbedding φ) (i : Fin 3) :
    (quaternionicWindowOfQuatEmbedding φ hφ).embedding (quatDiagonalAtom i) = diagAtom i := by
  rw [quaternionicWindowOfQuatEmbedding_apply]
  apply Prod.ext
  · funext j
    by_cases h : j = i <;> simp [quatMatrixToAlbert, quatDiagonalAtom, diagAtom, h]
  · funext j
    fin_cases j <;> simp [quatMatrixToAlbert, quatDiagonalAtom, diagAtom]

private theorem conjugateHermitian_diagAtom (d : Fin 3 → Quaternion ℝ)
    (hd : ∀ i, d i * star (d i) = 1 ∧ star (d i) * d i = 1) (i : Fin 3) :
    conjugateHermitian (Unitary.conjStarAlgAut ℝ QuatMatrix3 (quatDiagonal d hd)) (quatDiagonalAtom i) =
      quatDiagonalAtom i := by
  apply Subtype.ext
  apply Matrix.ext
  intro j k
  by_cases e : j = k
  · subst k
    exact quatDiagonal_apply_diag d hd (quatDiagonalAtom i) j
  · change Unitary.conjStarAlgAut ℝ QuatMatrix3 (quatDiagonal d hd) (quatDiagonalAtom i).val j k = _
    rw [quatDiagonal_apply]
    simp [quatDiagonalAtom, Matrix.diagonal_apply_ne _ e]

/-- Quaternionic diagonal phases extend to an Albert automorphism fixing the three diagonal atoms. -/
theorem extendQuaternionicDiagonal (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (d : Fin 3 → Quaternion ℝ)
    (hd : ∀ i, d i * star (d i) = 1 ∧ star (d i) * d i = 1) :
    ∃ g : NativeAlbertAutomorphism,
      (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      ∀ X : QuatHermitian3, g.linearEquiv ((quaternionicWindowOfQuatEmbedding φ hφ).embedding X) =
        (quaternionicWindowOfQuatEmbedding φ hφ).embedding
          (quaternionicDiagonalConjugation d hd X) := by
  let Q := quaternionicWindowOfQuatEmbedding φ hφ
  obtain ⟨a, ha⟩ := native_quaternionicWindow_conjugate_standard_embedding Q
  obtain ⟨b, hb⟩ := native_quaternionicWindow_conjugate_standard_embedding
    (transportQuaternionicWindow Q d hd)
  let g : NativeAlbertAutomorphism :=
    { linearEquiv := a.linearEquiv.trans b.linearEquiv.symm
      preserves_product := by
        intro x y
        apply b.linearEquiv.injective
        simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
          b.preserves_product, a.preserves_product]
      preserves_unit := by
        apply b.linearEquiv.injective
        simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
          a.preserves_unit, b.preserves_unit]
      preserves_trace := by
        intro x
        simp only [LinearEquiv.trans_apply]
        rw [← a.preserves_trace x, ← b.preserves_trace (b.linearEquiv.symm (a.linearEquiv x)),
          LinearEquiv.apply_symm_apply] }
  have hg (X : QuatHermitian3) :
      g.linearEquiv (Q.embedding X) =
        Q.embedding (quaternionicDiagonalConjugation d hd X) := by
    apply b.linearEquiv.injective
    change b.linearEquiv (b.linearEquiv.symm (a.linearEquiv (Q.embedding X))) =
      b.linearEquiv ((transportQuaternionicWindow Q d hd).embedding X)
    rw [LinearEquiv.apply_symm_apply, ha, hb]
  refine ⟨g, fun i => ?_, hg⟩
  rw [← quaternionicWindow_diagAtom φ hφ i, hg]
  rw [quaternionicDiagonalConjugation, conjugateHermitian_diagAtom]

end

end ThirteenPlanes.JordanFrames
