module

public import ThirteenPlanes.Cartan.AlbertOperators
public import ThirteenPlanes.Cartan.ExponentialNormalizer
public import ThirteenPlanes.Cartan.UnitaryLogarithm
public import ThirteenPlanes.Graded.FullLineModel

@[expose] public section

set_option backward.privateInPublic true

/-! Lifting special unitary conjugation through restriction of compact Albert derivations. -/

namespace ThirteenPlanes.Cartan

open scoped Matrix Matrix.Norms.Operator
open NormedSpace

noncomputable section

/-- An isometric automorphism of the Albert trace Jordan algebra as an actual native automorphism. -/
def nativeAlbertAutomorphism (g : albertJordan.Automorphism) : Glennie.CompactAutomorphism where
  equiv := g.action.toLinearEquiv
  map_jordan := g.product_map
  map_trace x := by
    change Glennie.trace (g.action x) = Glennie.trace x
    simpa only [albertJordan_trace] using g.trace_map albertJordan x

/-- Conjugation on the literal full Hermitian matrix model. -/
def hermitianUnitaryConjugation (U : ComplexSpecialUnitary3) (x : Graded.FullHermitian3) :
    Graded.FullHermitian3 :=
  ⟨U.val * x.val * U.valᴴ, by
    change (U.val * x.val * U.valᴴ)ᴴ = U.val * x.val * U.valᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      x.property.eq, mul_assoc]⟩

private def hermitianCommutator (A : complexSkewTracelessMatrices) :
    Module.End ℝ Graded.FullHermitian3 :=
  (((LinearMap.mulLeft ℝ A.val - LinearMap.mulRight ℝ A.val).comp
    Graded.fullHermitianSubspace.subtype)).codRestrict Graded.fullHermitianSubspace (by
      intro x
      change (A.val * x.val - x.val * A.val)ᴴ = A.val * x.val - x.val * A.val
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        A.property.1, x.property.eq, mul_neg, neg_mul]
      abel)

private theorem hermitianCommutator_product (A : complexSkewTracelessMatrices)
    (x y : Graded.FullHermitian3) :
    hermitianCommutator A (Graded.fullHermitianProduct x y) =
      Graded.fullHermitianProduct (hermitianCommutator A x) y +
      Graded.fullHermitianProduct x (hermitianCommutator A y) := by
  apply Subtype.ext
  change A.val * symmetricMatrixProduct x.val y.val - symmetricMatrixProduct x.val y.val * A.val =
    symmetricMatrixProduct (A.val * x.val - x.val * A.val) y.val +
    symmetricMatrixProduct x.val (A.val * y.val - y.val * A.val)
  simp only [symmetricMatrixProduct, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← smul_add]
  congr 1
  noncomm_ring

variable (Q : Submodule ℝ Glennie.Albert)

/-- The line product on a Jordan-closed subspace, with its literal Albert value. -/
def lineProduct (closed : ∀ x y : Q, Glennie.jordan x.val y.val ∈ Q) (x y : Q) : Q :=
  ⟨Glennie.jordan x.val y.val, closed x y⟩

/-- Surjectivity of the restriction of a space of compact derivations lifts each individual
special unitary matrix, in the specified Jordan coordinates of the line. -/
theorem lift_specialUnitary_on_line (K : Submodule ℝ (Module.End ℝ Glennie.Albert))
    (closed : ∀ x y : Q, Glennie.jordan x.val y.val ∈ Q)
    (I : Graded.FullHermitian3 ≃ₗ[ℝ] Q)
    (product : ∀ x y, (I (Graded.fullHermitianProduct x y)).val =
      Glennie.jordan (I x).val (I y).val)
    (restrict_surjective : ∀ B : Module.End ℝ Q,
      (∀ x y : Q, (B (lineProduct Q closed x y)).val =
        Glennie.jordan (B x).val y.val + Glennie.jordan x.val (B y).val) →
      ∃ D : albertJordan.skewDerivations, D.val.val ∈ K ∧ ∀ x : Q, (B x).val = D.val.val x.val)
    (U : ComplexSpecialUnitary3) :
    ∃ D : albertJordan.skewDerivations, D.val.val ∈ K ∧
      let k := nativeAlbertAutomorphism (albertJordan.expAutomorphism D)
      Q.map k.equiv.toLinearMap = Q ∧ ∀ x : Graded.FullHermitian3,
        k.equiv (I x).val = (I (hermitianUnitaryConjugation U x)).val := by
  let : CompleteSpace Q := FiniteDimensional.completeSpace ℝ Q
  obtain ⟨A, hA⟩ := suThree_exists_traceless_skew_log U
  let B := I.conj (hermitianCommutator A)
  have action (x : Graded.FullHermitian3) : B (I x) = I (hermitianCommutator A x) := by
    change I (hermitianCommutator A (I.symm (I x))) = _
    rw [I.symm_apply_apply]
  have coordProduct (x y : Graded.FullHermitian3) :
      lineProduct Q closed (I x) (I y) = I (Graded.fullHermitianProduct x y) :=
    Subtype.ext (product x y).symm
  obtain ⟨D, hD, lift⟩ := restrict_surjective B (by
    intro x y
    obtain ⟨x, rfl⟩ := I.surjective x
    obtain ⟨y, rfl⟩ := I.surjective y
    rw [coordProduct, action, action, action, hermitianCommutator_product, map_add,
      Submodule.coe_add, product, product])
  let i : Q →L[ℝ] Glennie.Albert := LinearMap.toContinuousLinearMap Q.subtype
  let ψ : Q →L[ℝ] ComplexMatrix3 := LinearMap.toContinuousLinearMap
    (Graded.fullHermitianSubspace.subtype.comp I.symm.toLinearMap)
  let b : Q →L[ℝ] Q := LinearMap.toContinuousLinearMap B
  have innerAction (x : Q) : ψ (b x) = A.val * ψ x - ψ x * A.val := by
    obtain ⟨x, rfl⟩ := I.surjective x
    change (I.symm (B (I x))).val = A.val * (I.symm (I x)).val - (I.symm (I x)).val * A.val
    rw [action, I.symm_apply_apply, I.symm_apply_apply]
    rfl
  let g := albertJordan.expAutomorphism D
  have expAction (x : Q) := albertJordan.expAutomorphism_on_inner_action D i ψ b A.val lift innerAction x
  have inv : exp (-A.val) = U.valᴴ := by
    rw [← A.property.1, Matrix.exp_conjTranspose, hA]
  have acts (x : Q) : ∃ y : Q, g.action x.val = y.val ∧
      (I.symm y).val = U.val * (I.symm x).val * U.valᴴ := by
    obtain ⟨hv, hm⟩ := expAction x
    have hc := congrArg₂ (fun a c : ComplexMatrix3 => a * ψ x * c) hA inv
    exact ⟨_, hv, hm.trans hc⟩
  refine ⟨D, hD, ?_, ?_⟩
  · apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, h, _⟩ := acts ⟨x, hx⟩
      change g.action x ∈ Q
      rw [h]
      exact y.property
    · exact ((nativeAlbertAutomorphism g).equiv.submoduleMap Q).finrank_eq.symm
  · intro x
    obtain ⟨y, hv, hm⟩ := acts (I x)
    rw [I.symm_apply_apply] at hm
    have h := congrArg I (show I.symm y = hermitianUnitaryConjugation U x from Subtype.ext hm)
    rw [I.apply_symm_apply] at h
    exact hv.trans (congrArg Subtype.val h)

end

end ThirteenPlanes.Cartan
