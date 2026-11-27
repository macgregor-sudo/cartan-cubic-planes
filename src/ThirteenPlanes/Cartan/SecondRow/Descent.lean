/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.SecondRowSplitting
public import Mathlib.Data.Nat.Find
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option backward.privateInPublic true

/-! Intersecting a conjugation-stable second-row splitting with its real operator algebra. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J))

/-- Intersection with the fixed real part, expressed in its original operator coordinates. -/
def secondRowRealIntersection (C : Submodule ℝ (secondRowSpace M K)) : Submodule ℝ K :=
  C.comap ((secondRowCoordinates M K).toLinearMap.comp (LinearMap.inl ℝ K M.traceFree))

theorem secondRowRealIntersection_piece (T : Submodule ℝ K) :
    secondRowRealIntersection M K (secondRowPieceInSpace M T) = T := by
  ext k
  change secondRowCoordinates M K (k, 0) ∈
    (T.prod (representedFixedPlane M T)).map (secondRowCoordinates M K).toLinearMap ↔ k ∈ T
  constructor
  · rintro ⟨p, hp, he⟩
    have eq : p = (k, 0) := (secondRowCoordinates M K).injective he
    subst p
    exact hp.1
  · intro hk
    exact ⟨(k, 0), ⟨hk, (representedFixedPlane M T).zero_mem⟩, rfl⟩

private theorem realPart_mem (C : Submodule ℝ (secondRowSpace M K))
    (stable : C.map (secondRowTheta M K).toLinearMap = C)
    (p : K × M.traceFree) (hp : secondRowCoordinates M K p ∈ C) :
    secondRowCoordinates M K (p.1, 0) ∈ C := by
  let e := secondRowCoordinates M K
  have ht : e (p.1, -p.2) ∈ C := by
    change secondRowCoordinates M K (p.1, -p.2) ∈ C
    rw [← secondRowTheta_coordinates M K p, ← stable]
    exact Submodule.mem_map_of_mem hp
  have split : (1 / 2 : ℝ) • (p + (p.1, -p.2)) = (p.1, 0) := by
    apply Prod.ext
    · change (1 / 2 : ℝ) • (p.1 + p.1) = p.1
      rw [← two_smul ℝ, smul_smul]
      norm_num
    · change (1 / 2 : ℝ) • (p.2 + -p.2) = 0
      simp
  have h := C.smul_mem (1 / 2 : ℝ) (C.add_mem hp ht)
  change (1 / 2 : ℝ) • (e p + e (p.1, -p.2)) ∈ C at h
  rw [← e.map_add, ← e.map_smul, split] at h
  exact h

/-- The real intersections of conjugation-stable summands span the fixed algebra. -/
theorem secondRowRealIntersection_spans {ι : Type*} (C : ι → Submodule ℝ (secondRowSpace M K))
    (stable : ∀ i, (C i).map (secondRowTheta M K).toLinearMap = C i) (spans : iSup C = ⊤) :
    (⨆ i, secondRowRealIntersection M K (C i)) = ⊤ := by
  let e := secondRowCoordinates M K
  let projection := (LinearMap.fst ℝ K M.traceFree).comp e.symm.toLinearMap
  have projected : (iSup C).map projection ≤ ⨆ i, secondRowRealIntersection M K (C i) := by
    rw [Submodule.map_iSup]
    refine iSup_le fun i k hk => ?_
    obtain ⟨x, hx, rfl⟩ := hk
    obtain ⟨p, rfl⟩ := e.surjective x
    apply le_iSup (fun j => secondRowRealIntersection M K (C j)) i
    change e ((e.symm (e p)).1, 0) ∈ C i
    rw [e.symm_apply_apply]
    exact realPart_mem M K (C i) (stable i) p hx
  have onto : Function.Surjective projection := by
    intro k
    refine ⟨e (k, 0), ?_⟩
    change (e.symm (e (k, 0))).1 = k
    rw [e.symm_apply_apply]
  rw [spans, Submodule.map_top, LinearMap.range_eq_top.mpr onto] at projected
  exact eq_top_iff.mpr projected

variable [FiniteDimensional ℝ J]

/-- A trace-orthogonal splitting by stable summands restricts to an orthogonal direct sum in
the real algebra. A rank bound on these intersections is an equality in each summand. -/
theorem secondRowRealIntersection_splitting {m rank : ℕ}
    (C : Fin m → Submodule ℝ (secondRowSpace M K))
    (stable : ∀ i, (C i).map (secondRowTheta M K).toLinearMap = C i) (spans : iSup C = ⊤)
    (orth : ∀ i j, i ≠ j → ∀ X ∈ C i, ∀ Y ∈ C j, complexTraceForm X.val Y.val = 0)
    (rankBound : ∀ i, Module.finrank ℝ (secondRowRealIntersection M K (C i)) ≤ rank)
    (dimension : Module.finrank ℝ K = m * rank) :
    OrthogonalSplit (fun i => secondRowRealIntersection M K (C i)) ∧
      ∀ i, Module.finrank ℝ (secondRowRealIntersection M K (C i)) = rank := by
  let T i := secondRowRealIntersection M K (C i)
  have horth : Pairwise fun i j => (T i).IsOrtho (T j) := by
    intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    intro x hx y hy
    have hz := orth i j hij (secondRowCoordinates M K (x, 0)) hx
      (secondRowCoordinates M K (y, 0)) hy
    change complexTraceForm (secondRowEmbed M K (x, 0)) (secondRowEmbed M K (y, 0)) = 0 at hz
    rw [secondRow_traceForm] at hz
    simpa using congrArg Complex.re hz
  have internal : DirectSum.IsInternal T :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top T).mpr
      ⟨(OrthogonalFamily.of_pairwise horth).independent, secondRowRealIntersection_spans M K C stable spans⟩
  refine ⟨⟨horth, internal⟩, ?_⟩
  have (i : Fin m) : Module.Free ℝ (T i) := Module.Free.of_basis (stdOrthonormalBasis ℝ (T i)).toBasis
  have (i : Fin m) : Module.Finite ℝ (T i) := inferInstance
  have sumEq := (LinearEquiv.ofBijective (DirectSum.coeLinearMap T) internal).finrank_eq
  rw [Module.finrank_directSum ℝ (fun i => ↥(T i)), dimension] at sumEq
  have same : (∑ i, Module.finrank ℝ (T i)) = ∑ _ : Fin m, rank := by simpa using sumEq
  exact fun i => (Finset.sum_eq_sum_iff_of_le fun j _ => rankBound j).mp same i (Finset.mem_univ i)

/-- Any given subspace with a property is contained in a maximal subspace with that property,
by maximizing its dimension. Applied to commutativity it extends an abelian subspace. -/
theorem exists_maximal_subspace_with {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (P : Submodule ℝ V → Prop) (T : Submodule ℝ V) (hT : P T) :
    ∃ S, T ≤ S ∧ P S ∧ ∀ U, S ≤ U → P U → S = U := by
  classical
  let ranks n := ∃ S : Submodule ℝ V, T ≤ S ∧ P S ∧ Module.finrank ℝ S = n
  have first : ranks (Module.finrank ℝ T) := ⟨T, le_rfl, hT, rfl⟩
  obtain ⟨S, hTS, hS, hdim⟩ := Nat.findGreatest_spec (P := ranks) T.finrank_le first
  refine ⟨S, hTS, hS, fun U hSU hU => Submodule.eq_of_le_of_finrank_le hSU ?_⟩
  rw [hdim]
  exact Nat.le_findGreatest U.finrank_le ⟨U, hTS.trans hSU, hU, rfl⟩

/-- If all maximal subspaces with a property have dimension r, every such subspace has
dimension at most r and attaining r makes the subspace maximal. -/
theorem subspace_rank_of_maximal_rank {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (P : Submodule ℝ V → Prop) (rank : ℕ)
    (maxRank : ∀ S, P S → (∀ U, S ≤ U → P U → S = U) → Module.finrank ℝ S = rank)
    (T : Submodule ℝ V) (hT : P T) :
    Module.finrank ℝ T ≤ rank ∧
      (Module.finrank ℝ T = rank → ∀ U, T ≤ U → P U → T = U) := by
  have bound (U : Submodule ℝ V) (hU : P U) : Module.finrank ℝ U ≤ rank := by
    obtain ⟨S, hUS, hS, hMax⟩ := exists_maximal_subspace_with P U hU
    exact (Submodule.finrank_mono hUS).trans_eq (maxRank S hS hMax)
  exact ⟨bound T hT, fun eq U hTU hU => Submodule.eq_of_le_of_finrank_le hTU (eq ▸ bound U hU)⟩

omit [FiniteDimensional ℝ J] in
/-- Commutativity of a second-row summand restricts to commutativity of its real operators. -/
theorem secondRowRealIntersection_commutes (C : Submodule ℝ (secondRowSpace M K))
    (comm : ∀ X Y : C, Commute X.val.val Y.val.val)
    (x y : secondRowRealIntersection M K C) : Commute x.val.val.val y.val.val.val := by
  let e := secondRowCoordinates M K
  have hx : e (x.val, 0) ∈ C := x.property
  have hy : e (y.val, 0) ∈ C := y.property
  have he (k : K) : (e (k, 0)).val = k.val.val.baseChange ℂ := by
    change realImagOperator k.val.val (M.L (0 : J)) = _
    simp [realImagOperator]
  have hc := (comm ⟨_, hx⟩ ⟨_, hy⟩).eq
  change (e (x.val, 0)).val * (e (y.val, 0)).val = (e (y.val, 0)).val * (e (x.val, 0)).val at hc
  rw [he, he, ← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul] at hc
  have pair : (x.val.val.val * y.val.val.val, (0 : Module.End ℝ J)) =
      (y.val.val.val * x.val.val.val, (0 : Module.End ℝ J)) :=
    realImagOperator_injective (by simpa [realImagOperator] using hc)
  exact congrArg Prod.fst pair

omit [FiniteDimensional ℝ J] in
/-- Every maximal abelian stable summand is the lift of its real intersection if the
centralizer of that real Cartan is precisely the abelian second-row piece. -/
theorem secondRowRealIntersection_lift (C : Submodule ℝ (secondRowSpace M K))
    (comm : ∀ X Y : C, Commute X.val.val Y.val.val)
    (maximal : ∀ B : Submodule ℝ (secondRowSpace M K), C ≤ B →
      (∀ X Y : B, Commute X.val.val Y.val.val) → C = B)
    (T : Submodule ℝ K) (intersection : secondRowRealIntersection M K C = T)
    (pieceComm : ∀ X Y : secondRowPieceInSpace M T, Commute X.val.val Y.val.val)
    (centralizes : ∀ B : Submodule ℝ (secondRowSpace M K),
      (∀ X Y : B, Commute X.val.val Y.val.val) →
      (∀ H : T, secondRowCoordinates M K (H.val, 0) ∈ B) → B ≤ secondRowPieceInSpace M T) :
    C = secondRowPieceInSpace M T := by
  apply maximal _ (centralizes C comm ?_) pieceComm
  subst T
  exact fun H => H.property

/-- Maximality among commutative real subspaces is the compact Cartan criterion. -/
def MaximalCommutativeSubspace {α : Type*} [LE α] (comm : α → Prop) (S : α) : Prop :=
  comm S ∧ ∀ U, S ≤ U → comm U → S = U

def RealOperatorCommutative (T : Submodule ℝ K) : Prop :=
  ∀ X Y : T, Commute X.val.val.val Y.val.val.val

def SecondRowOperatorCommutative (C : Submodule ℝ (secondRowSpace M K)) : Prop :=
  ∀ X Y : C, Commute X.val.val Y.val.val

/-- A splitting of the real algebra by represented compact Cartans. -/
structure RealOperatorCartanOD {ι : Type*} [DecidableEq ι] (T : ι → Submodule ℝ K) : Prop where
  orthogonalSplit : OrthogonalSplit T
  cartan : ∀ i, MaximalCommutativeSubspace (RealOperatorCommutative K) (T i)

/-- Trace-orthogonal decomposition of the full second row by individually invariant Cartans. -/
structure StableSecondRowCartanOD {ι : Type*} (C : ι → Submodule ℝ (secondRowSpace M K)) : Prop where
  cartan : ∀ i, MaximalCommutativeSubspace (SecondRowOperatorCommutative M K) (C i)
  stable : ∀ i, (C i).map (secondRowTheta M K).toLinearMap = C i
  independent : iSupIndep C
  spans : iSup C = ⊤
  orthogonal : ∀ i j, i ≠ j → ∀ X ∈ C i, ∀ Y ∈ C j, complexTraceForm X.val Y.val = 0

set_option maxHeartbeats 800000 in
/-- The extension and its inverse on the actual second-row coordinates. The inputs are
the rank of the real Cartans, their computed centralizers, and the forward trace splitting. -/
theorem secondRowCartanOD_equivalence {m rank : ℕ} (dimension : Module.finrank ℝ K = m * rank)
    (realRank : ∀ T, MaximalCommutativeSubspace (RealOperatorCommutative K) T →
      Module.finrank ℝ T = rank)
    (extend : ∀ T, MaximalCommutativeSubspace (RealOperatorCommutative K) T →
      MaximalCommutativeSubspace (SecondRowOperatorCommutative M K) (secondRowPieceInSpace M T) ∧
      (secondRowPieceInSpace M T).map (secondRowTheta M K).toLinearMap = secondRowPieceInSpace M T ∧
      ∀ C, MaximalCommutativeSubspace (SecondRowOperatorCommutative M K) C →
        (∀ H : T, secondRowCoordinates M K (H.val, 0) ∈ C) → C = secondRowPieceInSpace M T)
    (split : ∀ T : Fin m → Submodule ℝ K, RealOperatorCartanOD K T → SecondRowSplitting M T rank) :
    ∃ e : {T : Fin m → Submodule ℝ K // RealOperatorCartanOD K T} ≃
        {C : Fin m → Submodule ℝ (secondRowSpace M K) // StableSecondRowCartanOD M K C},
      (∀ T i, (e T).val i = secondRowPieceInSpace M (T.val i)) ∧
      (∀ C i, (e.symm C).val i = secondRowRealIntersection M K (C.val i)) := by
  let up (T : Fin m → Submodule ℝ K) := fun i => secondRowPieceInSpace M (T i)
  let down (C : Fin m → Submodule ℝ (secondRowSpace M K)) := fun i => secondRowRealIntersection M K (C i)
  have forward (T : Fin m → Submodule ℝ K) (h : RealOperatorCartanOD K T) :
      StableSecondRowCartanOD M K (up T) := by
    have lifted := split T h
    refine ⟨fun i => (extend _ (h.cartan i)).1, fun i => (extend _ (h.cartan i)).2.1,
      lifted.independent, lifted.spans, ?_⟩
    intro i j hij x hx y hy
    apply lifted.orthogonal i j hij x.val y.val
    · obtain ⟨p, hp, he⟩ := hx
      exact ⟨p, hp, congrArg Subtype.val he⟩
    · obtain ⟨p, hp, he⟩ := hy
      exact ⟨p, hp, congrArg Subtype.val he⟩
  have backward (C : Fin m → Submodule ℝ (secondRowSpace M K)) (h : StableSecondRowCartanOD M K C) :
      RealOperatorCartanOD K (down C) := by
    have comm (i) : RealOperatorCommutative K (down C i) :=
      secondRowRealIntersection_commutes M K (C i) (h.cartan i).1
    have bounds (i : Fin m) := subspace_rank_of_maximal_rank (RealOperatorCommutative K) rank
      (fun U a b => realRank U ⟨a, b⟩) (down C i) (comm i)
    have R := secondRowRealIntersection_splitting M K C h.stable h.spans
      h.orthogonal (fun i => (bounds i).1) dimension
    exact ⟨R.1, fun i => ⟨comm i, (bounds i).2 (R.2 i)⟩⟩
  let e : {T : Fin m → Submodule ℝ K // RealOperatorCartanOD K T} ≃
      {C : Fin m → Submodule ℝ (secondRowSpace M K) // StableSecondRowCartanOD M K C} :=
    { toFun := fun T => ⟨up T.val, forward _ T.property⟩
      invFun := fun C => ⟨down C.val, backward _ C.property⟩
      left_inv := fun T => Subtype.ext (funext fun i => secondRowRealIntersection_piece M K (T.val i))
      right_inv := by
        intro C
        apply Subtype.ext
        funext i
        have lifted := extend (down C.val i) ((backward C.val C.property).cartan i)
        exact (lifted.2.2 (C.val i) (C.property.cartan i) (fun H => H.property)).symm }
  exact ⟨e, fun _ _ => rfl, fun _ _ => rfl⟩

end

end ThirteenPlanes.Cartan
