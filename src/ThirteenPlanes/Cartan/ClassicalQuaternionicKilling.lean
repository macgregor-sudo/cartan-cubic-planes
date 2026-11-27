module

public import ThirteenPlanes.Cartan.ClassicalQuaternionicCoordinates
public import ThirteenPlanes.Cartan.DiagonalWeights
public import ThirteenPlanes.Cartan.QuaternionRepresentation

@[expose] public section

set_option backward.privateInPublic true

/-! The Killing and representation trace metrics of compact sp(3). -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB LieAlgebra
open scoped Matrix BigOperators RealInnerProductSpace

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Every compact Cartan is conjugate under an actual quaternionic unitary matrix
to the standard diagonal torus, with no rank assumption. -/
theorem compactSp3_cartan_conjugateStandard (T : LieSubalgebra ℝ compactSp3)
    (hT : IsCompactCartan T) :
    ∃ U : QBasis,
      (T.toSubmodule.map compactSp3.toSubmodule.subtype).map (quaternionicPullback U).toLinearMap =
        quaternionicStandardDiagonal.range := by
  let S := T.toSubmodule.map compactSp3.toSubmodule.subtype
  have hs : ∀ A ∈ S, Aᴴ = -A := by
    rintro A ⟨A', _, rfl⟩
    exact A'.property
  have hc : ∀ A ∈ S, ∀ B ∈ S, Commute A B := by
    rintro A ⟨A', hA, rfl⟩ B ⟨B', hB, rfl⟩
    have he := (hT A').2 hA B' hB
    exact sub_eq_zero.mp (congrArg Subtype.val he)
  have hmax (A : QMat) (hA : Aᴴ = -A) (h : ∀ B ∈ S, Commute A B) : A ∈ S := by
    let X : compactSp3 := ⟨A, hA⟩
    refine ⟨X, (hT X).1 ?_, rfl⟩
    intro Y hY
    apply Subtype.ext
    change A * Y.val - Y.val * A = 0
    exact sub_eq_zero.mpr (h Y.val ⟨Y, hY, rfl⟩).eq
  exact quaternionicCartan_conjugateStandard S hs hc hmax

theorem compactSp3_cartan_finrank (T : LieSubalgebra ℝ compactSp3)
    (hT : IsCompactCartan T) : Module.finrank ℝ T = 3 := by
  obtain ⟨U, hU⟩ := compactSp3_cartan_conjugateStandard T hT
  let S := T.toSubmodule.map compactSp3.toSubmodule.subtype
  change S.map (quaternionicPullback U).toLinearMap = quaternionicStandardDiagonal.range at hU
  have h₁ : Module.finrank ℝ T = Module.finrank ℝ S :=
    (Submodule.equivMapOfInjective compactSp3.toSubmodule.subtype
      (Submodule.subtype_injective compactSp3.toSubmodule) T.toSubmodule).finrank_eq
  have h₂ := ((quaternionicPullback U).submoduleMap S).finrank_eq
  change Module.finrank ℝ S = Module.finrank ℝ (S.map (quaternionicPullback U).toLinearMap) at h₂
  rw [h₁, h₂, hU, quaternionicStandardDiagonal_dim]

/-- The represented action of the compact Lie algebra on the actual traceless carrier. -/
abbrev compactSp3TraceRepresentation : compactSp3 →ₗ[ℝ]
    SkewOperator quaternionJordan.traceFree := quaternionTraceRepresentation

private theorem compactSp3_killing_trace_self (A : compactSp3) :
    killingForm ℝ compactSp3 A A =
      -2 * ⟪compactSp3TraceRepresentation A, compactSp3TraceRepresentation A⟫ := by
  obtain ⟨U, hU⟩ := quaternionicSkew_simultaneousDiagonalization (fun _ : Unit => A.val)
    (fun _ => A.property) (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
  obtain ⟨a, ha⟩ := hU ()
  have he : compactSp3Conjugate U A = compactSp3Diagonal a := Subtype.ext ha
  have hr : conjugateSkew ((quaternionJordanAction U).traceAction quaternionJordan)
      (compactSp3TraceRepresentation A) = quaternionStandardRestricted a := by
    change conjugateSkew ((quaternionJordanAction U).traceAction quaternionJordan)
      (quaternionTraceRepresentation (⟨A.val, A.property⟩ : quaternionSkewMatrices)) = _
    rw [quaternionTraceRepresentation_conjugate]
    have ha' : quaternionSkewPullback U (⟨A.val, A.property⟩ : quaternionSkewMatrices) = quaternionSkewDiagonal a := Subtype.ext ha
    rw [ha']
    rfl
  let g := conjugateSkew (V := quaternionJordan.traceFree)
    ((quaternionJordanAction U).traceAction quaternionJordan)
  let D := compactSp3TraceRepresentation A
  have hinner : ⟪D, D⟫ = ⟪quaternionStandardRestricted a, quaternionStandardRestricted a⟫ := by
    calc
      _ = ⟪g D,g D⟫ := (g.inner_map_map D D).symm
      _ = _ := congrArg (fun X : SkewOperator quaternionJordan.traceFree => ⟪X,X⟫) hr
  calc
    killingForm ℝ compactSp3 A A =
        killingForm ℝ compactSp3 (compactSp3Conjugate U A) (compactSp3Conjugate U A) :=
      (killingForm_of_equiv_apply (compactSp3Conjugate U) A A).symm
    _ = killingForm ℝ compactSp3 (compactSp3Diagonal a) (compactSp3Diagonal a) :=
      congrArg (fun x : compactSp3 => killingForm ℝ compactSp3 x x) he
    _ = -16 * ∑ i, a i * a i := compactSp3_killing_diagonal a a
    _ = -2 * (8 * ∑ i, a i * a i) := by ring
    _ = -2 * ⟪quaternionStandardRestricted a, quaternionStandardRestricted a⟫ :=
      congrArg ((-2 : ℝ) * ·) (quaternionStandardRestricted_inner a a).symm
    _ = -2 * ⟪D,D⟫ := congrArg ((-2 : ℝ) * ·) hinner.symm

/-- The negative Killing form is twice the negative trace form of the
fourteen-dimensional real traceless Hermitian representation. -/
theorem compactSp3_killing_trace_ratio (A B : compactSp3) :
    killingForm ℝ compactSp3 A B =
      -2 * ⟪compactSp3TraceRepresentation A, compactSp3TraceRepresentation B⟫ := by
  let Bk := killingForm ℝ compactSp3
  let D := compactSp3TraceRepresentation
  have hBk : Bk (A+B) (A+B) = Bk A A + Bk B B + 2 * Bk A B := by
    have hs : Bk B A = Bk A B := LieModule.traceForm_comm ℝ compactSp3 compactSp3 B A
    simp only [map_add, LinearMap.add_apply, hs]
    ring
  have hD : ⟪D (A+B),D (A+B)⟫ =
      ⟪D A,D A⟫ + ⟪D B,D B⟫ + 2 * ⟪D A,D B⟫ := by
    have hs : ⟪D B,D A⟫ = ⟪D A,D B⟫ := real_inner_comm _ _
    simp only [map_add, inner_add_left, inner_add_right, hs]
    ring
  change Bk A B = -2 * ⟪D A,D B⟫
  have h : Bk (A+B) (A+B) = -2 * ⟪D (A+B),D (A+B)⟫ := compactSp3_killing_trace_self (A+B)
  rw [hBk, hD] at h
  have hA : Bk A A = -2 * ⟪D A,D A⟫ := compactSp3_killing_trace_self A
  have hB : Bk B B = -2 * ⟪D B,D B⟫ := compactSp3_killing_trace_self B
  linarith

theorem compactSp3_compactKilling : CompactKilling compactSp3 := by
  intro A hA
  have hinj : Function.Injective compactSp3TraceRepresentation := by
    change Function.Injective (quaternionRestrictOperators ∘ quaternionCommutatorEquiv)
    exact quaternionRestrictOperators.injective.comp quaternionCommutatorEquiv.injective
  have hne : compactSp3TraceRepresentation A ≠ 0 := by
    intro h
    exact hA (hinj (h.trans (map_zero compactSp3TraceRepresentation).symm))
  rw [compactSp3_killing_trace_ratio]
  exact mul_neg_of_neg_of_pos (by norm_num) (real_inner_self_pos.mpr hne)

/-- The number of summands in a compact sp(3) Cartan decomposition is forced by the ranks. -/
theorem compactSp3_cartanOD_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → LieSubalgebra ℝ compactSp3) (hT : IsKillingCartanOD T) :
    Fintype.card ι = 7 := by
  let E := LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun i => (T i).toSubmodule)) hT.2.2
  have h := E.finrank_eq
  rw [Module.finrank_directSum, compactSp3_finrank] at h
  have hi (i : ι) : Module.finrank ℝ (T i).toSubmodule = 3 :=
    compactSp3_cartan_finrank _ ((compactCartan_iff_cartan compactSp3_compactKilling _).mpr (hT.1 i))
  simp only [hi, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  omega

end
end ThirteenPlanes.Cartan
