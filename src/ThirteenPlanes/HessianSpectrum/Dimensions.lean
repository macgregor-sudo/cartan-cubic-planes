module

public import ThirteenPlanes.HessianSpectrum.Basic
public import ThirteenPlanes.HessianSpectrum.SymArrays
public import ThirteenPlanes.HessianSpectrum.SkewArrays

@[expose] public section

/-! Dimensions: symmetric cubics `(n+2).choose 3`, skew endomorphisms `n.choose 2`, trace space `n`. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Coefficients in the standard orthonormal basis, as a linear map to symmetric arrays. -/
def coeffLin : SymmetricCubic V →ₗ[ℝ] symArrays (Module.finrank ℝ V) where
  toFun h := ⟨h.coefficient (stdOrthonormalBasis ℝ V), coefficient_symm _ h⟩
  map_add' g h := Subtype.ext (funext fun i => funext fun j => funext fun k => by
    simp [coefficient])
  map_smul' a h := Subtype.ext (funext fun i => funext fun j => funext fun k => by
    simp [coefficient])

theorem coeffLin_bijective : Function.Bijective (coeffLin (V := V)) := by
  set e := stdOrthonormalBasis ℝ V
  constructor
  · intro g h hgh
    have hc : g.coefficient e = h.coefficient e := congrArg Subtype.val hgh
    exact eq_of_tensorPairing g h fun k => by
      rw [tensorPairing_eq_sum e, tensorPairing_eq_sum e, hc]
  · rintro ⟨c, hc⟩
    refine ⟨ofCoefficients e c hc.s12 hc.s23, Subtype.ext ?_⟩
    funext i j k
    exact ofCoefficients_apply_basis e c hc.s12 hc.s23 i j k

/-- **Dimension of the space of symmetric cubics:** `(n+2).choose 3`. -/
theorem finrank_symmetricCubic :
    Module.finrank ℝ (SymmetricCubic V) = (Module.finrank ℝ V + 2).choose 3 := by
  rw [(LinearEquiv.ofBijective _ coeffLin_bijective).finrank_eq, finrank_symArrays]

/-- `6 · dim Sym³(V) = n(n+1)(n+2)`. -/
theorem six_mul_finrank_symmetricCubic :
    6 * Module.finrank ℝ (SymmetricCubic V) =
      Module.finrank ℝ V * (Module.finrank ℝ V + 1) * (Module.finrank ℝ V + 2) := by
  rw [finrank_symmetricCubic, six_mul_choose_three]

/-- Matrices of skew-adjoint endomorphisms in the standard orthonormal basis. -/
def skewMatLin : skewEnd V →ₗ[ℝ] skewArrays (Module.finrank ℝ V) where
  toFun A := ⟨matOf (stdOrthonormalBasis ℝ V) (A : V →ₗ[ℝ] V), fun a i => matOf_skew _ A.2 a i⟩
  map_add' A B := Subtype.ext (funext fun a => funext fun i => by
    simp [matOf, inner_add_right])
  map_smul' r A := Subtype.ext (funext fun a => funext fun i => by
    simp [matOf, real_inner_smul_right])

theorem skewMatLin_bijective : Function.Bijective (skewMatLin (V := V)) := by
  set e := stdOrthonormalBasis ℝ V
  constructor
  · rintro ⟨A, hA⟩ ⟨B, hB⟩ h
    have hm : ∀ a i, matOf e A a i = matOf e B a i := fun a i =>
      congrFun (congrFun (congrArg Subtype.val h) a) i
    apply Subtype.ext
    apply e.toBasis.ext
    intro i
    rw [OrthonormalBasis.coe_toBasis, ← e.sum_repr' (A (e i)), ← e.sum_repr' (B (e i))]
    exact Finset.sum_congr rfl fun a _ => by rw [show ⟪e a, A (e i)⟫ = ⟪e a, B (e i)⟫ from hm a i]
  · rintro ⟨Ω, hΩ⟩
    refine ⟨⟨skewOp e Ω, isSkew_skewOp e hΩ⟩, Subtype.ext ?_⟩
    funext a i
    exact matOf_skewOp e Ω a i

/-- **Dimension of the skew-adjoint endomorphisms:** `n.choose 2`. -/
theorem finrank_skewEnd : Module.finrank ℝ (skewEnd V) = (Module.finrank ℝ V).choose 2 := by
  rw [(LinearEquiv.ofBijective _ skewMatLin_bijective).finrank_eq, finrank_skewArrays]

/-- `2 · dim so(V) = n(n-1)`. -/
theorem two_mul_finrank_skewEnd :
    2 * Module.finrank ℝ (skewEnd V) = Module.finrank ℝ V * (Module.finrank ℝ V - 1) := by
  rw [finrank_skewEnd, two_mul_choose_two]

/-- **Dimension of the trace space:** `n`. -/
theorem finrank_traceSpace : Module.finrank ℝ (traceSpace V) = Module.finrank ℝ V :=
  LinearMap.finrank_range_of_inj (f := traceAdjointLin) traceAdjoint_injective

end

end ThirteenPlanes
