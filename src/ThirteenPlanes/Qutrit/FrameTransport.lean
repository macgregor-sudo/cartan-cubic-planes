module

public import ThirteenPlanes.Qutrit.Generated
public import ThirteenPlanes.Peirce.FrameFormula
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

@[expose] public section

set_option backward.privateInPublic true

/-! The frame markings of a generated qutrit transport as actual matrix idempotents. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

noncomputable section

open RoundCubics Peirce AlbertSequential
open scoped Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {g : SymmetricCubic E} {e : E} {A : Submodule ℝ E}

theorem framePairGenerated_point_left (p q : Fin 3 → E) (i : Fin 3) :
    p i ∈ framePairGenerated g e p q :=
  Submodule.mem_sInf.mpr fun _ h => h.2.2.1 i

theorem framePairGenerated_point_right (p q : Fin 3 → E) (i : Fin 3) :
    q i ∈ framePairGenerated g e p q :=
  Submodule.mem_sInf.mpr fun _ h => h.2.2.2 i

/-- Transport a frame by a unital, trace-preserving Jordan isomorphism. -/
def transportedComplexFrame {p : Fin 3 → E} (F : TraceJordanFrame g e p)
    (hp : ∀ i, p i ∈ A) (he : e ∈ A) (hc : IsClosedPiece g A)
    (I : A ≃ₗ[ℝ] Hermitian3) (Iunit : (I ⟨e, he⟩).val = 1)
    (Itrace : ∀ x : A, (Matrix.trace (I x).val).re = ⟪e, (x : E)⟫)
    (Iprod : ∀ x y : A, (I ⟨g.L (x : E) (y : E), hc x.property y.property⟩).val =
      symmetricMatrixProduct (I x).val (I y).val) : ComplexTraceFrame3 where
  point i := (I ⟨p i, hp i⟩).val
  hermitian i := (I ⟨p i, hp i⟩).property
  trace_one i := by
    have hi : (I ⟨p i, hp i⟩).val.IsHermitian := (I ⟨p i, hp i⟩).property
    rw [hermitian_trace_eq_real hi, Itrace, F.trace_one, Complex.ofReal_one]
  jordan_point i j := by
    rw [← Iprod]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      congr 2
      exact Subtype.ext (F.idempotent i)
    · rw [ite_eq_right hij]
      have hz : (⟨g.L (p i) (p j), hc (hp i) (hp j)⟩ : A) = 0 := Subtype.ext (F.orthogonal i j hij)
      rw [hz, map_zero]
      rfl
  sum_unit := by
    have hsum : (∑ i, (⟨p i, hp i⟩ : A)) = ⟨e, he⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact F.sum_unit
    have hi := congrArg (fun x : A => (I x).val) hsum
    rw [map_sum] at hi
    change (selfAdjoint ComplexMatrix3).subtype (∑ i, I ⟨p i, hp i⟩) = _ at hi
    rw [map_sum, Iunit] at hi
    exact hi

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J : V →ₗᵢ[ℝ] E} {U Y : Submodule ℝ V}

theorem traceFrame_inner_of_orthogonal (orthUnit : ∀ x, ⟪e, J x⟫ = 0)
    (F : CenteredTraceFrame J e U) (G : CenteredTraceFrame J e Y)
    (orth : U.IsOrtho Y) (i j : Fin 3) :
    ⟪F.point i, G.point j⟫ = 1 / 3 := by
  have fp : F.point i = J (F.centered i : V) + (1 / 3 : ℝ) • e := by
    rw [F.centered_eq, sub_add_cancel]
  have gp : G.point j = J (G.centered j : V) + (1 / 3 : ℝ) • e := by
    rw [G.centered_eq, sub_add_cancel]
  have oh : ⟪(F.centered i : V), (G.centered j : V)⟫ = 0 :=
    orth.inner_eq (F.centered i).property (G.centered j).property
  have ho (x : V) : ⟪J x, e⟫ = 0 := (real_inner_comm _ _).trans (orthUnit x)
  rw [fp, gp]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    J.inner_map_map, ho, oh, orthUnit, F.unit_inner_self]
  ring

private def hermitianUnitaryAut (U : unitary ComplexMatrix3) : ComplexMatrix3 ≃⋆ₐ[ℝ] ComplexMatrix3 :=
  Unitary.conjStarAlgAut ℝ ComplexMatrix3 U

/-- Conjugation acts on the actual space of Hermitian matrices by a real linear equivalence. -/
def complexQutritConjugation (U : unitary ComplexMatrix3) : Hermitian3 ≃ₗ[ℝ] Hermitian3 where
  toFun x := ⟨hermitianUnitaryAut U x.val, by
    rw [selfAdjoint.mem_iff, ← map_star, (show star x.val = x.val from x.property)]⟩
  invFun x := ⟨(hermitianUnitaryAut U).symm x.val, by
    rw [selfAdjoint.mem_iff, ← map_star, (show star x.val = x.val from x.property)]⟩
  left_inv x := Subtype.ext ((hermitianUnitaryAut U).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((hermitianUnitaryAut U).apply_symm_apply x.val)
  map_add' x y := Subtype.ext ((hermitianUnitaryAut U).map_add x.val y.val)
  map_smul' r x := Subtype.ext (map_smul (hermitianUnitaryAut U) r x.val)

theorem complexQutritConjugation_coe (U : unitary ComplexMatrix3) (x : Hermitian3) :
    (complexQutritConjugation U x).val = U.val * x.val * star U.val := by
  exact Unitary.conjStarAlgAut_apply U x.val

theorem complexQutritConjugation_trace (U : unitary ComplexMatrix3) (x : Hermitian3) :
    Matrix.trace (complexQutritConjugation U x).val = Matrix.trace x.val := by
  rw [complexQutritConjugation_coe, Matrix.trace_mul_comm, ← mul_assoc,
    (Unitary.mem_iff.mp U.property).1, one_mul]

theorem complexQutritConjugation_unit (U : unitary ComplexMatrix3) (x : Hermitian3) (hx : x.val = 1) :
    (complexQutritConjugation U x).val = 1 := by
  change hermitianUnitaryAut U x.val = 1
  rw [hx, map_one]

theorem complexQutritConjugation_product (U : unitary ComplexMatrix3) (x y z : Hermitian3)
    (hz : z.val = symmetricMatrixProduct x.val y.val) :
    (complexQutritConjugation U z).val =
      symmetricMatrixProduct (complexQutritConjugation U x).val (complexQutritConjugation U y).val := by
  let C := hermitianUnitaryAut U
  have hs (r : ℝ) (M : ComplexMatrix3) : r • M = (r : ℂ) • M := by
    ext i j
    rfl
  have hhalf : (1 / 2 : ℂ) • (x.val * y.val + y.val * x.val) =
      (1 / 2 : ℝ) • (x.val * y.val + y.val * x.val) := by
    rw [hs]
    push_cast
    rfl
  change C z.val = symmetricMatrixProduct (C x.val) (C y.val)
  rw [hz, symmetricMatrixProduct, hhalf, map_smul, map_add, map_mul, map_mul,
    symmetricMatrixProduct, hs]
  push_cast
  rfl

end

end ThirteenPlanes.JordanFrames
