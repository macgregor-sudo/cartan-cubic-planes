module

public import ThirteenPlanes.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators InnerProductSpace RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {h : SymmetricCubic V} {c : ℝ}

/-- The product of the restricted cubic on a closed subspace is the original product. -/
theorem closedSubspace_restriction_product {U : Submodule ℝ V}
    (closed : IsClosedPiece h U) (x y : U) :
    ((h.pullback U.subtype).L x y : V) = h.L (x : V) (y : V) := by
  let z : U := ⟨h.L (x : V) (y : V), closed x.property y.property⟩
  suffices (h.pullback U.subtype).L x y = z from congrArg Subtype.val this
  apply ext_inner_right ℝ
  intro w
  change (h.pullback U.subtype).apply x y w = h.apply (x : V) (y : V) (w : V)
  exact h.pullback_apply U.subtype x y w

/-- A closed subspace inherits the round identity at the ambient strength. -/
theorem closedSubspace_restriction_isRound {U : Submodule ℝ V}
    (round : IsRound h c) (closed : IsClosedPiece h U) :
    IsRound (h.pullback U.subtype) c := by
  refine ⟨round.positive, fun x => ?_⟩
  change ‖((h.pullback U.subtype).L x x : V)‖ ^ 2 = c * ‖(x : V)‖ ^ 4
  rw [closedSubspace_restriction_product closed]
  exact round.square_norm (x : V)

omit [FiniteDimensional ℝ V] in
private theorem inner_mul_diag (g : SymmetricCubic V) (x e : V) :
    ⟪e, g.L x e⟫ = ⟪x, g.L e e⟫ := by
  calc
    _ = g.apply x e e := real_inner_comm _ _
    _ = g.apply e e x := (g.apply_swap₁₂ x e e).trans (g.apply_swap₂₃ e x e)
    _ = _ := real_inner_comm _ _

section OrthogonalDecomposition

variable {ι : Type*} [Fintype ι] {U : ι → Submodule ℝ V}

/-- Each block contributes the trace of its restricted cubic at the corresponding projection. -/
theorem trace_eq_sum_restriction_traces
    (orth : Pairwise fun i j => (U i).IsOrtho (U j)) (exhaustive : ⨆ i, U i = ⊤)
    (closed : ∀ i, IsClosedPiece h (U i)) (x : V) :
    LinearMap.trace ℝ V (h.L x) =
      ∑ i, LinearMap.trace ℝ (U i)
        ((h.pullback (U i).subtype).L ((U i).orthogonalProjectionOnto x)) := by
  classical
  let family : OrthogonalFamily ℝ (fun i => U i) (fun i => (U i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise orth
  have internal : DirectSum.IsInternal U := family.isInternal_iff.mpr (by simp [exhaustive])
  let basis (i : ι) := stdOrthonormalBasis ℝ (U i)
  let ambient := internal.collectedOrthonormalBasis family basis
  have ambient_apply (i : ι) (j : Fin (Module.finrank ℝ (U i))) :
      ambient ⟨i, j⟩ = (basis i j : V) := by
    simp [ambient, DirectSum.IsInternal.collectedOrthonormalBasis]
  rw [SymmetricCubic.trace_eq_sum_inner ambient, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SymmetricCubic.trace_eq_sum_inner (basis i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ambient_apply, inner_mul_diag, inner_mul_diag,
    (U i).inner_orthogonalProjectionOnto_eq_of_mem_right,
    closedSubspace_restriction_product (closed i)]

/-- A cubic is trace free exactly when each member of an exhaustive orthogonal
family of closed subspaces has trace-free restriction. -/
theorem closedPieces_traceFree_iff
    (orth : Pairwise fun i j => (U i).IsOrtho (U j)) (exhaustive : ⨆ i, U i = ⊤)
    (closed : ∀ i, IsClosedPiece h (U i)) :
    h.TraceFree ↔ ∀ i, (h.pullback (U i).subtype).TraceFree := by
  classical
  constructor
  · intro global i x
    have ht := global (x : V)
    rw [trace_eq_sum_restriction_traces orth exhaustive closed, Finset.sum_eq_single i] at ht
    · simpa only [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using ht
    · intro j _ hji
      have hx : (x : V) ∈ (U j)ᗮ :=
        Submodule.isOrtho_iff_le.mp (orth hji.symm) x.property
      simp [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hx]
    · simp
  · intro blocks x
    rw [trace_eq_sum_restriction_traces orth exhaustive closed]
    exact Finset.sum_eq_zero fun i _ => blocks i _

end OrthogonalDecomposition

/-- A round trace-free cubic cannot have a one-dimensional domain. -/
theorem finrank_ne_one_of_round_traceFree (round : IsRound h c) (tf : h.TraceFree) :
    Module.finrank ℝ V ≠ 1 := by
  intro hdim
  let e := (stdOrthonormalBasis ℝ V).reindex (finCongr hdim)
  let x := e 0
  have hx : ‖x‖ = 1 := e.orthonormal.norm_eq_one 0
  have ht := tf x
  rw [SymmetricCubic.trace_eq_sum_inner e, Fin.sum_univ_one] at ht
  have hzero : h.squareMap x = 0 := by
    rw [← e.sum_repr' (h.squareMap x), Fin.sum_univ_one]
    change ⟪x, h.squareMap x⟫ • x = 0
    change ⟪x, h.squareMap x⟫ = 0 at ht
    rw [ht, zero_smul]
  have hn := round.square_norm x
  rw [hzero, norm_zero, hx] at hn
  exact round.positive.ne' (by simpa using hn.symm)

/-- The roundness on closed subspaces for closed subspaces of arbitrary dimensions. -/
theorem closedPieces_round (round : IsRound h c) :
    (∀ U : Submodule ℝ V, IsClosedPiece h U →
      (∀ x y : U, ((h.pullback U.subtype).L x y : V) = h.L (x : V) (y : V)) ∧
        IsRound (h.pullback U.subtype) c) ∧
    (∀ {ι : Type*} [Fintype ι] (U : ι → Submodule ℝ V),
      (Pairwise fun i j => (U i).IsOrtho (U j)) → (⨆ i, U i = ⊤) →
      (∀ i, IsClosedPiece h (U i)) →
        (h.TraceFree ↔ ∀ i, (h.pullback (U i).subtype).TraceFree) ∧
          (h.TraceFree → ∀ i, Module.finrank ℝ (U i) ≠ 1)) := by
  refine ⟨fun U closed =>
    ⟨closedSubspace_restriction_product closed, closedSubspace_restriction_isRound round closed⟩,
    ?_⟩
  intro ι _ U orth exhaustive closed
  have ht := closedPieces_traceFree_iff orth exhaustive closed
  exact ⟨ht, fun global i => finrank_ne_one_of_round_traceFree
    (closedSubspace_restriction_isRound round (closed i)) (ht.mp global i)⟩

end ThirteenPlanes.RoundCubics
