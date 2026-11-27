module

public import ThirteenPlanes.Contracts

@[expose] public section

/-! Geometric inputs for the closed-plane results. The strength is arbitrary and positive. -/

open scoped BigOperators

namespace ThirteenPlanes

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The squared norm of the metric product of a field with itself is radial with strength `c`. -/
structure IsRound (h : SymmetricCubic V) (c : ℝ) : Prop where
  positive : 0 < c
  square_norm : ∀ x : V, ‖h.squareMap x‖ ^ 2 = c * ‖x‖ ^ 4

/-- A real subspace closed under multiplication by the cubic. -/
def IsClosedPiece (h : SymmetricCubic V) (U : Submodule ℝ V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ U → y ∈ U → h.L x y ∈ U

/-- Each member of an exhaustive orthogonal decomposition into two-planes is closed. -/
def IsClosedPlaneSystem {ι : Type*} (h : SymmetricCubic V)
    (planes : PlaneDecomposition V ι) : Prop :=
  ∀ i, IsClosedPiece h (planes.plane i)

variable [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]

/-- The intrinsic pencil. Its diagonal part is the sum of the projected plane restrictions. -/
noncomputable def planePencil (h : SymmetricCubic V) (planes : PlaneDecomposition V ι) :
    CubicPair V :=
  let diagonal := ∑ i, h.pullback (planes.proj i)
  ⟨diagonal, h - diagonal⟩

@[simp] theorem planePencil_at_one (h : SymmetricCubic V) (planes : PlaneDecomposition V ι) :
    interactionCubic (planePencil h planes) 1 = h := by
  rw [interactionCubic_one]
  dsimp [planePencil]
  abel

end ThirteenPlanes
