module

public import ThirteenPlanes.Cartan.SecondRowCentralizer
public import ThirteenPlanes.Cartan.SecondRowMetric

@[expose] public section

set_option backward.privateInPublic true

/-! The centralizer and orthogonal splitting in the actual second-row operator space. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]

private theorem prod_independent_span {ι K V : Type*}
    [AddCommGroup K] [Module ℝ K] [AddCommGroup V] [Module ℝ V]
    (T : ι → Submodule ℝ K) (U : ι → Submodule ℝ V)
    (hiT : iSupIndep T) (hiU : iSupIndep U) (hsT : iSup T = ⊤) (hsU : iSup U = ⊤) :
    iSupIndep (fun i => (T i).prod (U i)) ∧ (⨆ i, (T i).prod (U i)) = ⊤ := by
  constructor
  · intro i
    apply Submodule.disjoint_def.mpr
    intro p hp hrest
    have hfst :
        (⨆ j, ⨆ _ : j ≠ i, (T j).prod (U j)) ≤
          (⨆ j, ⨆ _ : j ≠ i, T j).comap (LinearMap.fst ℝ K V) := by
      refine iSup_le fun j => iSup_le fun hji p hp => ?_
      have hm : T j ≤ (⨆ j, ⨆ _ : j ≠ i, T j) :=
        le_iSup₂ (f := fun j (_ : j ≠ i) => T j) j hji
      exact hm hp.1
    have hsnd :
        (⨆ j, ⨆ _ : j ≠ i, (T j).prod (U j)) ≤
          (⨆ j, ⨆ _ : j ≠ i, U j).comap (LinearMap.snd ℝ K V) := by
      refine iSup_le fun j => iSup_le fun hji p hp => ?_
      have hm : U j ≤ (⨆ j, ⨆ _ : j ≠ i, U j) :=
        le_iSup₂ (f := fun j (_ : j ≠ i) => U j) j hji
      exact hm hp.2
    exact Prod.ext ((Submodule.disjoint_def.mp (hiT i)) p.1 hp.1 (hfst hrest))
      ((Submodule.disjoint_def.mp (hiU i)) p.2 hp.2 (hsnd hrest))
  · apply eq_top_iff.mpr
    intro p _
    let P := ⨆ i, (T i).prod (U i)
    have hl : ∀ x : K, (x, (0 : V)) ∈ P := by
      have h : (⨆ i, T i) ≤ P.comap (LinearMap.inl ℝ K V) := by
        refine iSup_le fun i x hx => ?_
        exact (le_iSup (fun i => (T i).prod (U i)) i) ⟨hx, (U i).zero_mem⟩
      rw [hsT] at h
      exact fun x => h (Submodule.mem_top (R := ℝ) (x := x))
    have hr : ∀ y : V, ((0 : K), y) ∈ P := by
      have h : (⨆ i, U i) ≤ P.comap (LinearMap.inr ℝ K V) := by
        refine iSup_le fun i y hy => ?_
        exact (le_iSup (fun i => (T i).prod (U i)) i) ⟨(T i).zero_mem, hy⟩
      rw [hsU] at h
      exact fun y => h (Submodule.mem_top (R := ℝ) (x := y))
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using P.add_mem (hl p.1) (hr p.2)

theorem secondRow_piece_dim (M : TraceJordanData J)
    {K : Submodule ℝ (SkewOperator J)} (T : Submodule ℝ K) :
    Module.finrank ℝ (secondRowPieceInSpace M T) =
      Module.finrank ℝ T + Module.finrank ℝ (representedFixedPlane M T) := by
  let P := T.prod (representedFixedPlane M T)
  let e := (secondRowCoordinates M K).submoduleMap P
  let b := (stdOrthonormalBasis ℝ T).toBasis.prod
    (stdOrthonormalBasis ℝ (representedFixedPlane M T)).toBasis
  have h := Module.finrank_eq_card_basis b
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  exact e.finrank_eq.symm.trans ((T.prodEquiv (representedFixedPlane M T)).finrank_eq.trans h)

private theorem secondRow_pieces_trace_orthogonal (M : TraceJordanData J)
    {K : Submodule ℝ (SkewOperator J)} (T S : Submodule ℝ K)
    (hT : T.IsOrtho S) (hP : (representedFixedPlane M T).IsOrtho (representedFixedPlane M S))
    (c : ℝ) (hPair : ∀ x y : M.traceFree,
      LinearMap.trace ℝ J (M.L x.val * M.L y.val) = c * ⟪x, y⟫)
    (X Y : Module.End ℂ (Complexified J)) (hx : X ∈ secondRowPiece M T)
    (hy : Y ∈ secondRowPiece M S) : complexTraceForm X Y = 0 := by
  change X ∈ (T.prod (representedFixedPlane M T)).map (secondRowEmbed M K) at hx
  change Y ∈ (S.prod (representedFixedPlane M S)).map (secondRowEmbed M K) at hy
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
  have hh : ⟪p.1.val, q.1.val⟫ = 0 := hT.inner_eq hp.1 hq.1
  have hv : ⟪p.2, q.2⟫ = 0 := hP.inner_eq hp.2 hq.2
  rw [secondRow_traceForm, hh, hPair, hv, mul_zero, add_zero, Complex.ofReal_zero]

omit [FiniteDimensional ℝ J] in
theorem secondRow_pieces_independent_span {ι : Type*} [DecidableEq ι]
    (M : TraceJordanData J) {K : Submodule ℝ (SkewOperator J)} (T : ι → Submodule ℝ K)
    (hT : DirectSum.IsInternal T) (hU : DirectSum.IsInternal (representedFixedPlane M ∘ T)) :
    iSupIndep (secondRowPieceInSpace M ∘ T) ∧ (⨆ i, secondRowPieceInSpace M (T i)) = ⊤ := by
  let U : ι → Submodule ℝ M.traceFree := representedFixedPlane M ∘ T
  let P : ι → Submodule ℝ (K × M.traceFree) := fun i => (T i).prod (U i)
  let e : (K × M.traceFree) ≃ₗ[ℝ] secondRowSpace M K := secondRowCoordinates M K
  have hiT : iSupIndep T := hT.submodule_iSupIndep
  have hiU : iSupIndep U := hU.submodule_iSupIndep
  have hsT : iSup T = ⊤ := hT.submodule_iSup_eq_top
  have hsU : iSup U = ⊤ := hU.submodule_iSup_eq_top
  have hP : iSupIndep P ∧ iSup P = ⊤ :=
    @prod_independent_span ι (↥K) (↥M.traceFree) _ _ _ _ T U hiT hiU hsT hsU
  change iSupIndep (fun i => (P i).map e.toLinearMap) ∧ (⨆ i, (P i).map e.toLinearMap) = ⊤
  refine ⟨e.toLinearMap.iSupIndep_map e.injective hP.1, ?_⟩
  rw [← Submodule.map_iSup, hP.2, Submodule.map_top,
    LinearMap.range_eq_top.mpr e.surjective]

/-- The four structural clauses of the lifted second-row splitting and positivity of its form. -/
structure SecondRowSplitting {ι : Type*} [DecidableEq ι]
    (M : TraceJordanData J) {K : Submodule ℝ (SkewOperator J)} (T : ι → Submodule ℝ K)
    (rank : ℕ) : Prop where
  positive : ∀ X : secondRowSpace M K, X ≠ 0 →
    (complexTraceForm X.val X.val).im = 0 ∧ 0 < (complexTraceForm X.val X.val).re
  independent : iSupIndep (secondRowPieceInSpace M ∘ T)
  spans : (⨆ i, secondRowPieceInSpace M (T i)) = ⊤
  dimension : ∀ i, Module.finrank ℝ (secondRowPieceInSpace M (T i)) = rank + 2
  commutative : ∀ i, ∀ X Y, X ∈ secondRowPiece M (T i) → Y ∈ secondRowPiece M (T i) → Commute X Y
  orthogonal : ∀ i j, i ≠ j → ∀ X Y, X ∈ secondRowPiece M (T i) → Y ∈ secondRowPiece M (T j) →
    complexTraceForm X Y = 0

/-- Proposition 7.9(b) after the native invariant pairing and frame-space conclusions. -/
theorem secondRow_operatorOD {ι : Type*} [DecidableEq ι]
    (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J)) (hK : K ≤ M.skewDerivations)
    (T : ι → Submodule ℝ K) (hT : OrthogonalSplit T)
    (hU : OrthogonalSplit (representedFixedPlane M ∘ T)) (rank : ℕ)
    (hRank : ∀ i, Module.finrank ℝ (T i) = rank)
    (hDim : ∀ i, Module.finrank ℝ (representedFixedPlane M (T i)) = 2)
    (hComm : ∀ i, ∀ A B : T i, Commute A.val.val.val B.val.val.val)
    (F : ι → M.Frame) (hF : ∀ i, representedFixedPlane M (T i) = (F i).plane M)
    (c : ℝ) (hPair : ∀ x y : M.traceFree, LinearMap.trace ℝ J (M.L x.val * M.L y.val) = c * ⟪x, y⟫) :
    SecondRowSplitting M T rank where
  positive X := secondRow_traceForm_pos M K (X := X)
  independent := (secondRow_pieces_independent_span M T hT.2 hU.2).1
  spans := (secondRow_pieces_independent_span M T hT.2 hU.2).2
  dimension i := by rw [secondRow_piece_dim M (T i), hRank i, hDim i]
  commutative i := secondRow_algebra_commutes M K hK (T i) (hComm i) (F i) (hF i)
  orthogonal i j hij := secondRow_pieces_trace_orthogonal M (T i) (T j)
    (hT.1 hij) (hU.1 hij) c hPair

end

end ThirteenPlanes.Cartan
