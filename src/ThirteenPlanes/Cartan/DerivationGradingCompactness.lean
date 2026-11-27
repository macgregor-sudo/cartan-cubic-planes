module

public import ThirteenPlanes.Cartan.Casimir
public import ThirteenPlanes.Cartan.LieOrthogonalDecomposition
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

/-! The invariant trace form of skew operators and its Killing consequence. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.Cartan

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Minus the trace of operator composition on a represented real Lie algebra. -/
def endTracePairing (K : LieSubalgebra ℝ (Module.End ℝ V)) : LinearMap.BilinForm ℝ K where
  toFun X :=
    { toFun := fun Y => -LinearMap.trace ℝ V (X.val * Y.val)
      map_add' Y Z := by
        change -LinearMap.trace ℝ V (X.val * (Y.val + Z.val)) =
          -LinearMap.trace ℝ V (X.val * Y.val) + -LinearMap.trace ℝ V (X.val * Z.val)
        simp [mul_add, map_add, add_comm]
      map_smul' r Y := by
        change -LinearMap.trace ℝ V (X.val * (r • Y.val)) =
          r • (-LinearMap.trace ℝ V (X.val * Y.val))
        rw [mul_smul_comm, map_smul, smul_neg] }
  map_add' X Y := by
    apply LinearMap.ext
    intro Z
    change -LinearMap.trace ℝ V ((X.val + Y.val) * Z.val) =
      -LinearMap.trace ℝ V (X.val * Z.val) + -LinearMap.trace ℝ V (Y.val * Z.val)
    simp [add_mul, map_add, add_comm]
  map_smul' r X := by
    apply LinearMap.ext
    intro Y
    change -LinearMap.trace ℝ V ((r • X.val) * Y.val) =
      r • (-LinearMap.trace ℝ V (X.val * Y.val))
    rw [smul_mul_assoc, map_smul, smul_neg]

theorem endTracePairing_apply (K : LieSubalgebra ℝ (Module.End ℝ V)) (X Y : K) :
    endTracePairing K X Y = -LinearMap.trace ℝ V (X.val * Y.val) := rfl

theorem endTracePairing_symmetric (K : LieSubalgebra ℝ (Module.End ℝ V)) (X Y : K) :
    endTracePairing K X Y = endTracePairing K Y X := by
  rw [endTracePairing_apply, endTracePairing_apply, LinearMap.trace_mul_comm]

theorem endTracePairing_invariant (K : LieSubalgebra ℝ (Module.End ℝ V)) (X Y Z : K) :
    endTracePairing K ⁅X, Y⁆ Z = endTracePairing K X ⁅Y, Z⁆ := by
  change -LinearMap.trace ℝ V (⁅X.val, Y.val⁆ * Z.val) =
    -LinearMap.trace ℝ V (X.val * ⁅Y.val, Z.val⁆)
  rw [LinearMap.trace_lie_mul_eq]

section Skew

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- A nonzero skew-adjoint real operator has strictly negative trace of its square. -/
theorem neg_trace_square_pos_of_skew {D : Module.End ℝ W} (hD : IsSkew D) (h0 : D ≠ 0) :
    0 < -LinearMap.trace ℝ W (D * D) := by
  let X : SkewOperator W := ⟨D, hD⟩
  have hX : X ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  change 0 < -LinearMap.trace ℝ W (X.val * X.val)
  rw [← skewOperator_inner]
  exact real_inner_self_pos.mpr hX

theorem endTracePairing_positive (K : LieSubalgebra ℝ (Module.End ℝ W))
    (hSkew : ∀ X : K, IsSkew X.val) (X : K) (h0 : X ≠ 0) :
    0 < endTracePairing K X X :=
  neg_trace_square_pos_of_skew (hSkew X) (fun h => h0 (Subtype.ext h))

end Skew

section CompactKilling

variable {K : Type*} [LieRing K] [LieAlgebra ℝ K] [Module.Finite ℝ K]

/-- An invariant positive form makes the adjoint operators skew. If the centre
is zero, their squared traces give a negative definite Killing form. -/
theorem compactKilling_of_invariantPositive (B : LinearMap.BilinForm ℝ K)
    (hsym : ∀ x y, B x y = B y x) (hpos : ∀ x ≠ 0, 0 < B x x)
    (hinv : ∀ x y z, B ⁅x, y⁆ z = B x ⁅y, z⁆)
    (hCenter : ∀ x : K, (∀ y : K, ⁅x, y⁆ = 0) → x = 0) :
    CompactKilling K := by
  let : InnerProductSpace.Core ℝ K :=
    { inner := fun a b => B a b
      conj_inner_symm := fun a b => by simpa only [RCLike.conj_to_real] using hsym b a
      re_inner_nonneg := fun a => by
        change 0 ≤ B a a
        by_cases ha : a = 0
        · subst a
          simp
        · exact (hpos a ha).le
      add_left := fun a b c => by simp
      smul_left := fun a b r => by simp
      definite := fun a ha => by
        by_contra hn
        have h := hpos a hn
        exact h.ne' ha }
  let : NormedAddCommGroup K := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ K := InnerProductSpace.ofCore (𝕜 := ℝ) (F := K) inferInstance
  intro X hX
  let D : Module.End ℝ K := LieAlgebra.ad ℝ K X
  have hSkew : IsSkew D := by
    intro Y Z
    change B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆
    rw [← hinv Y X Z]
    have h := congrArg (fun W => B W Z) (lie_skew X Y)
    simpa only [map_neg, LinearMap.neg_apply] using h.symm
  have hD : D ≠ 0 := by
    intro h
    apply hX
    apply hCenter X
    intro Y
    exact LinearMap.congr_fun h Y
  rw [killingForm_apply_apply, ← Module.End.mul_eq_comp]
  change LinearMap.trace ℝ K (D * D) < 0
  exact neg_pos.mp (neg_trace_square_pos_of_skew hSkew hD)

end CompactKilling

end
end ThirteenPlanes.Cartan
