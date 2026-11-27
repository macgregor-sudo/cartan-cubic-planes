module

public import ThirteenPlanes.Cartan.ClassicalSymplecticMatrices
public import ThirteenPlanes.Cartan.LieOrthogonalDecomposition

@[expose] public section

set_option backward.privateInPublic true

/-! The tensor-product complexification is the standard complex symplectic matrix Lie algebra. -/

namespace ThirteenPlanes.Cartan

open scoped TensorProduct Matrix

noncomputable section

private def spEmbedReal : compactSp3 →ₗ[ℝ] complexSp6 where
  toFun := compactSp3ComplexEmbed
  map_add' := compactSp3ComplexEmbed_add
  map_smul' := compactSp3ComplexEmbed_smul

private def spExtendLinear : LieComplex compactSp3 →ₗ[ℂ] complexSp6 :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun c => c • spEmbedReal
      map_add' := fun a b => add_smul a b spEmbedReal
      map_smul' := fun a b => mul_smul a b spEmbedReal }

/-- The complex-linear extension of the quaternionic matrix embedding. -/
def compactSp3ComplexHom : LieComplex compactSp3 →ₗ⁅ℂ⁆ complexSp6 :=
  { spExtendLinear with
    map_lie' := by
      intro x y
      change spExtendLinear ⁅x,y⁆ = ⁅spExtendLinear x,spExtendLinear y⁆
      induction x using TensorProduct.inductionOn with
      | add a b ha hb => simp [add_lie, map_add, ha, hb]
      | tmul z A =>
        induction y using TensorProduct.inductionOn with
        | add a b ha hb =>
          rw [show ⁅(z ⊗ₜ[ℝ] A : LieComplex compactSp3),a + b⁆ =
              ⁅(z ⊗ₜ[ℝ] A : LieComplex compactSp3),a⁆ +
                ⁅(z ⊗ₜ[ℝ] A : LieComplex compactSp3),b⁆ from
                lie_add (L := LieComplex compactSp3) (M := LieComplex compactSp3)
                  (z ⊗ₜ[ℝ] A) a b,
              map_add, map_add, lie_add, ha, hb]
        | tmul w B =>
          change spExtendLinear ⁅z ⊗ₜ[ℝ] A, w ⊗ₜ[ℝ] B⁆ =
            ⁅spExtendLinear (z ⊗ₜ[ℝ] A), spExtendLinear (w ⊗ₜ[ℝ] B)⁆
          simp only [spExtendLinear, LieAlgebra.ExtendScalars.bracket_tmul,
            TensorProduct.AlgebraTensorModule.lift_tmul, LinearMap.coe_mk, AddHom.coe_mk,
            LinearMap.smul_apply, spEmbedReal, compactSp3ComplexEmbed_lie,
            smul_lie, lie_smul, mul_smul, smul_comm z w] }

@[simp] theorem compactSp3ComplexHom_tmul (z : ℂ) (A : compactSp3) :
    compactSp3ComplexHom (z ⊗ₜ[ℝ] A) = z • compactSp3ComplexEmbed A := rfl

@[simp] theorem compactSp3ComplexHom_ofReal (A : compactSp3) :
    compactSp3ComplexHom (LieComplex.ofReal A) = compactSp3ComplexEmbed A := by simp

theorem compactSp3ComplexHom_conjugation (x : LieComplex compactSp3) :
    compactSp3ComplexHom (LieComplex.conjugation x) =
      standardSp6Conjugation (compactSp3ComplexHom x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z A => simp
  | add x y hx hy => simp only [map_add, standardSp6Conjugation_add, hx, hy]

private theorem compactSp3ComplexHom_injective : Function.Injective compactSp3ComplexHom := by
  have hz (x : LieComplex compactSp3) (h : compactSp3ComplexHom x = 0) : x = 0 := by
    let u := compactSp3ComplexEmbed (LieComplex.realPart x)
    let v := Complex.I • compactSp3ComplexEmbed (LieComplex.imagPart x)
    have h₁ : u + v = 0 := by
      nth_rw 1 [← LieComplex.decompose_smul x] at h
      simpa only [map_add, map_smul, compactSp3ComplexHom_ofReal] using h
    have h₂ := congrArg standardSp6Conjugation h₁
    have hs : standardSp6Conjugation (0 : complexSp6) = 0 := Subtype.ext (by simp)
    change standardSp6Conjugation
      (compactSp3ComplexEmbed (LieComplex.realPart x) +
        Complex.I • compactSp3ComplexEmbed (LieComplex.imagPart x)) = _ at h₂
    rw [standardSp6Conjugation_add, standardSp6Conjugation_smul, standardSp6Conjugation_embed,
      standardSp6Conjugation_embed, hs, show star Complex.I = -Complex.I from Complex.conj_I,
      neg_smul, ← sub_eq_add_neg] at h₂
    change u - v = 0 at h₂
    have hu : u = 0 := by
      have he : (2 : ℂ) • u = 0 := by
        rw [two_smul]
        calc
          _ = (u + v) + (u - v) := by abel
          _ = 0 := by rw [h₁, h₂, zero_add]
      exact (smul_eq_zero.mp he).resolve_left (by norm_num)
    have hv : v = 0 := by rwa [hu, zero_add] at h₁
    have hzero : compactSp3ComplexEmbed (0 : compactSp3) = 0 := map_zero spEmbedReal
    have hr : LieComplex.realPart x = 0 :=
      compactSp3ComplexEmbed_injective (hu.trans hzero.symm)
    have hi : LieComplex.imagPart x = 0 := compactSp3ComplexEmbed_injective
      (((smul_eq_zero.mp hv).resolve_left Complex.I_ne_zero).trans hzero.symm)
    rw [← LieComplex.decompose_smul x, hr, hi]
    simp
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

private theorem compactSp3ComplexHom_surjective : Function.Surjective compactSp3ComplexHom := by
  intro x
  let τ := standardSp6Conjugation
  let u := (1 / 2 : ℂ) • (x + τ x)
  let v := (-Complex.I / 2 : ℂ) • (x - τ x)
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ _
  have hu : τ u = u := by
    dsimp only [u, τ]
    rw [standardSp6Conjugation_smul, standardSp6Conjugation_add, standardSp6Conjugation_involutive]
    have h : (starRingEnd ℂ) (1 / 2) = 1 / 2 := by simp [h2]
    rw [show star (1 / 2 : ℂ) = 1 / 2 from h, add_comm]
  have hv : τ v = v := by
    have hsub (a b : complexSp6) : standardSp6Conjugation (a - b) =
        standardSp6Conjugation a - standardSp6Conjugation b := by
      apply Subtype.ext
      change -(a.val - b.val)ᴴ = -a.valᴴ - -b.valᴴ
      simp only [Matrix.conjTranspose_sub, neg_sub, sub_neg_eq_add]
      abel
    change standardSp6Conjugation ((-Complex.I / 2 : ℂ) • (x - standardSp6Conjugation x)) =
      (-Complex.I / 2 : ℂ) • (x - standardSp6Conjugation x)
    rw [standardSp6Conjugation_smul, hsub, standardSp6Conjugation_involutive]
    show (star (-Complex.I / 2) : ℂ) • (τ x - x) = (-Complex.I / 2) • (x - τ x)
    have h : (starRingEnd ℂ) (-Complex.I / 2) = -(-Complex.I / 2 : ℂ) := by
      simp [map_div₀, Complex.conj_I, h2, neg_div]
    rw [show star (-Complex.I / 2) = -(-Complex.I / 2 : ℂ) from h,
      neg_smul, ← smul_neg, neg_sub]
  obtain ⟨a, ha⟩ := (standardSp6Conjugation_fixed_iff u).mp hu
  obtain ⟨b, hb⟩ := (standardSp6Conjugation_fixed_iff v).mp hv
  refine ⟨LieComplex.ofReal a + Complex.I • LieComplex.ofReal b, ?_⟩
  rw [map_add, map_smul, compactSp3ComplexHom_ofReal, compactSp3ComplexHom_ofReal, ha, hb]
  change (1 / 2 : ℂ) • (x + τ x) + Complex.I • ((-Complex.I / 2 : ℂ) • (x - τ x)) = x
  rw [smul_smul, show Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) by
    rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg], ← smul_add]
  rw [show x + τ x + (x - τ x) = x + x by abel, ← two_smul ℂ, smul_smul]
  norm_num

/-- The actual complex symplectic matrices have the stated quaternionic compact real form. -/
def compactSp3ComplexEquiv : LieComplex compactSp3 ≃ₗ⁅ℂ⁆ complexSp6 :=
  { LinearEquiv.ofBijective compactSp3ComplexHom.toLinearMap
      ⟨compactSp3ComplexHom_injective, compactSp3ComplexHom_surjective⟩ with
    map_lie' := fun {x y} => compactSp3ComplexHom.map_lie x y }

@[simp] theorem compactSp3ComplexEquiv_conjugation (x : LieComplex compactSp3) :
    compactSp3ComplexEquiv (LieComplex.conjugation x) =
      standardSp6Conjugation (compactSp3ComplexEquiv x) :=
  compactSp3ComplexHom_conjugation x

end
end ThirteenPlanes.Cartan
