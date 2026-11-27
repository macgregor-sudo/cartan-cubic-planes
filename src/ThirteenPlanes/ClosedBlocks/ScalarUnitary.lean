module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.ClosedBlocks

open Matrix
open scoped ComplexOrder

private abbrev ComplexMatrix3 := Matrix (Fin 3) (Fin 3) ℂ

private def ScalarUnitaryProperty (S : Submodule ℝ ComplexMatrix3) : Prop :=
  ∀ A ∈ S, ∃ t : ℝ, Aᴴ * A = t • (1 : ComplexMatrix3)

private theorem det_ne_zero_of_scalarGram {A : ComplexMatrix3} (hA : A ≠ 0)
    {t : ℝ} (ht : Aᴴ * A = t • (1 : ComplexMatrix3)) : A.det ≠ 0 := by
  have htn : t ≠ 0 := by
    intro ht0
    exact hA (Matrix.conjTranspose_mul_self_eq_zero.mp (by simpa [ht0] using ht))
  have he : t • (1 : ComplexMatrix3) = (t : ℂ) • (1 : ComplexMatrix3) := by
    ext; simp [Algebra.smul_def]
  intro hz
  have h := congrArg Matrix.det ht
  rw [Matrix.det_mul, hz, mul_zero, he, Matrix.det_smul, Matrix.det_one, mul_one] at h
  exact (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr htn)) h.symm

private theorem realKernel_dim {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] ℝ) :
    Module.finrank ℝ E ≤ 1 + Module.finrank ℝ f.ker := by
  have h := f.finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le f.range
  rw [Module.finrank_self] at hr
  omega

private theorem polarizedGram {S : Submodule ℝ ComplexMatrix3} (hS : ScalarUnitaryProperty S)
    {A B : ComplexMatrix3} (hA : A ∈ S) (hB : B ∈ S) :
    ∃ t : ℝ, Aᴴ * B + Bᴴ * A = t • (1 : ComplexMatrix3) := by
  obtain ⟨a, ha⟩ := hS A hA
  obtain ⟨b, hb⟩ := hS B hB
  obtain ⟨s, hs⟩ := hS (A + B) (S.add_mem hA hB)
  refine ⟨s - a - b, ?_⟩
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, ha, hb] at hs
  rw [sub_smul, sub_smul, ← hs]
  abel

private noncomputable def realTrace : ComplexMatrix3 →ₗ[ℝ] ℝ :=
  Complex.reLm.comp (Matrix.traceLinearMap (Fin 3) ℝ ℂ)

private theorem scalar_eq_zero_of_realTrace_eq_zero {s : ℝ}
    (ht : realTrace (s • (1 : ComplexMatrix3)) = 0) : s = 0 := by
  rw [map_smul] at ht
  have h : realTrace (1 : ComplexMatrix3) = 3 := by
    change (Matrix.trace (1 : ComplexMatrix3)).re = 3
    simp
  rw [h, smul_eq_mul] at ht
  linarith

private theorem finrank_le_two_of_one_mem {S : Submodule ℝ ComplexMatrix3}
    (hS : ScalarUnitaryProperty S) (hI : (1 : ComplexMatrix3) ∈ S) :
    Module.finrank ℝ S ≤ 2 := by
  by_contra! hd
  let f := realTrace.comp S.subtype
  have hfd := realKernel_dim f
  have hfpos : 0 < Module.finrank ℝ f.ker := by omega
  let : Nontrivial f.ker := Module.nontrivial_of_finrank_pos hfpos
  obtain ⟨a, ha⟩ := exists_ne (0 : f.ker)
  let A : ComplexMatrix3 := a.1.1
  have hA : A ∈ S := a.1.2
  have hA0 : A ≠ 0 := by
    intro hz
    exact ha (Subtype.ext (Subtype.ext hz))
  have skew {X : ComplexMatrix3} (hX : X ∈ S) (hXtr : realTrace X = 0) :
      Xᴴ = -X := by
    obtain ⟨t, ht⟩ := polarizedGram hS hI hX
    rw [Matrix.conjTranspose_one, one_mul, mul_one] at ht
    have hct : realTrace Xᴴ = realTrace X := by
      change (Matrix.trace Xᴴ).re = (Matrix.trace X).re
      simp
    have ht0 : t = 0 := scalar_eq_zero_of_realTrace_eq_zero (by rw [← ht, map_add, hct, hXtr, add_zero])
    rw [ht0, zero_smul] at ht
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using ht)
  have hAstar : Aᴴ = -A := skew hA a.2
  let g := realTrace.comp
    ((mulLeftLinearMap (Fin 3) ℝ Aᴴ).comp (S.subtype.comp f.ker.subtype))
  have hgd := realKernel_dim (E := ↥f.ker) g
  have hgpos : 0 < Module.finrank ℝ g.ker := by omega
  let : Nontrivial g.ker := Module.nontrivial_of_finrank_pos hgpos
  obtain ⟨b, hb⟩ := exists_ne (0 : g.ker)
  let B : ComplexMatrix3 := b.1.1.1
  have hB : B ∈ S := b.1.1.2
  have hB0 : B ≠ 0 := by
    intro hz
    exact hb (Subtype.ext (Subtype.ext (Subtype.ext hz)))
  have hBstar : Bᴴ = -B := skew hB b.1.2
  obtain ⟨t, ht⟩ := polarizedGram hS hA hB
  have h1 : realTrace (Aᴴ * B) = 0 := b.2
  have h2 : realTrace (Bᴴ * A) = 0 := by
    change (Matrix.trace (Bᴴ * A)).re = 0
    rw [← Matrix.conjTranspose_conjTranspose A, ← Matrix.conjTranspose_mul,
      Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
    exact h1
  have ht0 : t = 0 := scalar_eq_zero_of_realTrace_eq_zero
    (by rw [← ht, map_add, h1, h2, add_zero])
  rw [ht0, zero_smul, hAstar, hBstar, neg_mul, neg_mul, ← neg_add,
    neg_eq_zero] at ht
  have hanti : A * B = -(B * A) := eq_neg_of_add_eq_zero_left ht
  obtain ⟨α, hα⟩ := hS A hA
  obtain ⟨β, hβ⟩ := hS B hB
  have hdet := congrArg Matrix.det hanti
  rw [Matrix.det_mul, Matrix.det_neg, Matrix.det_mul, Fintype.card_fin, mul_comm B.det A.det] at hdet
  have hd0 : A.det * B.det = 0 := by linear_combination hdet / 2
  exact (mul_ne_zero (det_ne_zero_of_scalarGram hA0 hα) (det_ne_zero_of_scalarGram hB0 hβ)) hd0

/-- A real space of complex three-by-three matrices whose Hermitian Gram
matrix is always a real scalar matrix has real dimension at most two. -/
theorem scalarUnitarySubspace_finrank_le_two (S : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℂ))
    (hS : ∀ A ∈ S, ∃ t : ℝ, Aᴴ * A = t • (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    Module.finrank ℝ S ≤ 2 := by
  by_contra! hd
  have hdpos : 0 < Module.finrank ℝ S := by omega
  let : Nontrivial S := Module.nontrivial_of_finrank_pos hdpos
  obtain ⟨a, ha⟩ := exists_ne (0 : S)
  let A : ComplexMatrix3 := a
  have hA : A ≠ 0 := fun e => ha (Subtype.ext e)
  obtain ⟨t, ht⟩ := hS A a.2
  have hdet : IsUnit A.det := (det_ne_zero_of_scalarGram hA ht).isUnit
  have ht0 : t ≠ 0 := by
    intro hz
    exact hA (Matrix.conjTranspose_mul_self_eq_zero.mp (by simpa [hz] using ht))
  let F := mulRightLinearMap (Fin 3) ℝ A⁻¹
  let U := S.map F
  have hF : Function.Injective F := by
    intro B C h
    change B * A⁻¹ = C * A⁻¹ at h
    have hh := congrArg (· * A) h
    simpa only [Matrix.nonsing_inv_mul_cancel_right A _ hdet] using hh
  have hUdim : Module.finrank ℝ U = Module.finrank ℝ S :=
    (S.equivMapOfInjective F hF).finrank_eq.symm
  have hUone : (1 : ComplexMatrix3) ∈ U :=
    Submodule.mem_map.mpr ⟨A, a.2, Matrix.mul_nonsing_inv A hdet⟩
  have hnorm : ScalarUnitaryProperty U := by
    intro Z hZ
    obtain ⟨B, hB, rfl⟩ := Submodule.mem_map.mp hZ
    obtain ⟨s, hs⟩ := hS B hB
    refine ⟨s * t⁻¹, ?_⟩
    change (B * A⁻¹)ᴴ * (B * A⁻¹) = (s * t⁻¹) • (1 : ComplexMatrix3)
    have hconj : (A⁻¹)ᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv A hdet, Matrix.conjTranspose_one]
    have he : (A⁻¹)ᴴ * (t • (1 : ComplexMatrix3)) * A⁻¹ = 1 := by
      rw [← ht, ← Matrix.mul_assoc, hconj, one_mul, Matrix.mul_nonsing_inv A hdet]
    have he' : (A⁻¹)ᴴ * A⁻¹ = t⁻¹ • (1 : ComplexMatrix3) := by
      rw [Matrix.mul_smul, mul_one, Matrix.smul_mul] at he
      have hh := congrArg (t⁻¹ • ·) he
      rwa [smul_smul, inv_mul_cancel₀ ht0, one_smul] at hh
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ,
      hs, Matrix.smul_mul, one_mul, Matrix.mul_smul, he', smul_smul]
  have hfin := finrank_le_two_of_one_mem hnorm hUone
  rw [hUdim] at hfin
  exact (not_le_of_gt hd) hfin

end ThirteenPlanes.ClosedBlocks
