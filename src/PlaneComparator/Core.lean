/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CubicPlaneDefs
public import ThirteenPlanes.PlaneShares
public import ThirteenPlanes.Shares.PlaneTransport
public import ThirteenPlanes.PlanePencilEnergy
public import ThirteenPlanes.ClosedBlocks.Dimensions

@[expose] public section

/-! Representation, projection and normalization adapters shared by the headline proofs. -/

open scoped BigOperators RealInnerProductSpace

namespace Challenge.Bridge

open ThirteenPlanes ThirteenPlanes.RoundCubics

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def toSymmetric (d : Cubic V) : SymmetricCubic V :=
  SymmetricCubic.ofProduct d.mul d.comm d.symm

def fromSymmetric (h : SymmetricCubic V) : Cubic V :=
  ⟨h.L, h.L_comm, h.apply_swap₂₃⟩

@[simp] theorem toSymmetric_fromSymmetric (h : SymmetricCubic V) :
    toSymmetric (fromSymmetric h) = h := Subtype.ext rfl

@[simp] theorem eval_toSymmetric (d : Cubic V) (x : V) :
    (toSymmetric d).apply x x x = d.eval x := rfl

theorem eikonal_iff (d : Cubic V) (c : ℝ) : Eikonal d c ↔ IsRound (toSymmetric d) c :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.positive, h.square_norm⟩⟩

theorem harmonic_iff (d : Cubic V) : Harmonic d ↔ (toSymmetric d).TraceFree := Iff.rfl

variable {ι : Type*} {d : Cubic V} {U : ι → Submodule ℝ V}

def planeDecomp (h : Planes d U) : PlaneDecomposition V ι :=
  ⟨U, fun i => (h.2 i).1, h.1.1, h.1.2⟩

theorem planeDecomp_closed (h : Planes d U) :
    IsClosedPlaneSystem (toSymmetric d) (planeDecomp h) :=
  fun i => (h.2 i).2

theorem mixed_space_eq (d : Cubic V) (U W : Submodule ℝ V) :
    mixedProductSpace (toSymmetric d) U W = mixedSpace d U W :=
  mixedProductSpace_eq_span (toSymmetric d) U W

variable [FiniteDimensional ℝ V]

def blockDecomp (orth : OrthogonalDecomposition U)
    (hn : ∀ i, U i ≠ ⊥) (hc : ∀ i, Closed d (U i)) :
    ClosedBlocks.Decomposition (toSymmetric d) ι :=
  ⟨U, hn, orth.1, orth.2, hc⟩

theorem share_eq (h : Planes d U) (i j k : ι) :
    planeShare (toSymmetric d) (planeDecomp h) i j k = share d U i j k := by
  unfold planeShare
  rw [mixed_space_eq]
  rfl

variable [Fintype ι]

theorem pencil_square_eq (h : Planes d U) (t : ℝ) (x : V) :
    (interactionCubic (planePencil (toSymmetric d) (planeDecomp h)) t).squareMap x =
      pencilSquare d U t x := by
  have hd := planePencil_diagonal_sq (planeDecomp_closed h) x
  have hterm (i : ι) :
      (U i).starProjection (d.mul ((U i).starProjection x) ((U i).starProjection x)) =
      d.mul ((U i).starProjection x) ((U i).starProjection x) :=
    (U i).starProjection_eq_self_iff.mpr
      ((h.2 i).2 ((U i).starProjection_apply_mem x) ((U i).starProjection_apply_mem x))
  have hsum :
      (planePencil (toSymmetric d) (planeDecomp h)).diagonalCubic.squareMap x =
        ∑ i, (U i).starProjection
          (d.mul ((U i).starProjection x) ((U i).starProjection x)) := by
    simp only [hterm]
    exact hd
  rw [interactionCubic, coupling_apply, one_smul, SymmetricCubic.squareMap_add,
    SymmetricCubic.squareMap_smul]
  change (planePencil (toSymmetric d) (planeDecomp h)).diagonalCubic.squareMap x +
    t • ((toSymmetric d) - (planePencil (toSymmetric d) (planeDecomp h)).diagonalCubic).L x x = _
  rw [map_sub (SymmetricCubic.L (V := V)), LinearMap.sub_apply, LinearMap.sub_apply]
  change (planePencil (toSymmetric d) (planeDecomp h)).diagonalCubic.squareMap x +
    t • (d.mul x x - (planePencil (toSymmetric d) (planeDecomp h)).diagonalCubic.squareMap x) = _
  rw [hsum]
  rfl

theorem pencil_eval_eq (h : Planes d U) (t : ℝ) (x : V) :
    (interactionCubic (planePencil (toSymmetric d) (planeDecomp h)) t).apply x x x =
      pencil d U t x := by
  change ⟪(interactionCubic (planePencil (toSymmetric d) (planeDecomp h)) t).squareMap x, x⟫ = _
  rw [pencil_square_eq h]
  rfl

theorem pencil_energy_eq (h : Planes d U) (c t : ℝ) (x : V) :
    normalizedPencilEnergy (toSymmetric d) (planeDecomp h) c t x = pencilEnergy d U c t x := by
  unfold normalizedPencilEnergy
  rw [pencil_square_eq h]
  rfl

omit [FiniteDimensional ℝ V] in
theorem eval_neg (h : SymmetricCubic V) (x : V) :
    (-h).apply x x x = -h.apply x x x := by
  rw [← neg_one_smul ℝ h, SymmetricCubic.apply_smul, neg_one_mul]

theorem pencil_eq_of_cubic_eq {g : Cubic V} {κ : Type*} [Fintype κ] {W : κ → Submodule ℝ V}
    (h : Planes d U) (j : Planes g W) {t s : ℝ}
    (he : interactionCubic (planePencil (toSymmetric g) (planeDecomp j)) s =
      interactionCubic (planePencil (toSymmetric d) (planeDecomp h)) t) :
    pencil g W s = pencil d U t := by
  funext x
  rw [← pencil_eval_eq j, ← pencil_eval_eq h, he]

theorem pencil_eq_neg_of_cubic_eq {g : Cubic V} {κ : Type*} [Fintype κ] {W : κ → Submodule ℝ V}
    (h : Planes d U) (j : Planes g W) {t s : ℝ}
    (he : interactionCubic (planePencil (toSymmetric g) (planeDecomp j)) s =
      -interactionCubic (planePencil (toSymmetric d) (planeDecomp h)) t) :
    pencil g W s = fun x => -(pencil d U t x) := by
  funext x
  rw [← pencil_eval_eq j, ← pencil_eval_eq h, he, eval_neg]

end

end Challenge.Bridge
