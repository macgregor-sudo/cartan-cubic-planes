module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! Coordinate arrays for quartic tensors.

In an orthonormal basis indexed by a finite type `ι`, a cubic is an array `ι → ι → ι → ℝ`, a quartic
tensor an array `ι → ι → ι → ι → ℝ` and a matrix an array `ι → ι → ℝ`. This file defines the
Kronecker delta, the coefficient inner products, full symmetry of a quartic array, the symmetrized
`δδ` tensor `Π`, the symmetrization `δ ⊙ B` of `δ_ij B_kl` (sum of its six placements), the
contraction of the last two indices, the traceless part of a matrix and the quartic and quadratic
forms. -/

open BigOperators

namespace ThirteenPlanes

noncomputable section

namespace Quartic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Kronecker delta. -/
def dlt (i j : ι) : ℝ := if i = j then 1 else 0

variable (ι) in
/-- The dimension `n` as a real number. -/
def dim : ℝ := Fintype.card ι

/-- Coefficient inner product of quartic arrays. -/
def qinner (A B : ι → ι → ι → ι → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, ∑ l, A i j k l * B i j k l

/-- Coefficient inner product of matrices. -/
def minner (A B : ι → ι → ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- Coefficient inner product of cubic arrays. -/
def cinner (a b : ι → ι → ι → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, a i j k * b i j k

/-- Euclidean inner product of coordinate vectors. -/
def vinner (u w : ι → ℝ) : ℝ := ∑ i, u i * w i

/-- A fully symmetric quartic array (the three adjacent transpositions generate `S₄`). -/
structure QSymm (T : ι → ι → ι → ι → ℝ) : Prop where
  s12 : ∀ i j k l, T i j k l = T j i k l
  s23 : ∀ i j k l, T i j k l = T i k j l
  s34 : ∀ i j k l, T i j k l = T i j l k

/-- A symmetric matrix. -/
def MSymm (B : ι → ι → ℝ) : Prop := ∀ i j, B i j = B j i

/-- The symmetrized `δδ` tensor `Π_ijkl = δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk`. -/
def piT (i j k l : ι) : ℝ := dlt i j * dlt k l + dlt i k * dlt j l + dlt i l * dlt j k

/-- `δ ⊙ B`, the sum of the six placements of `δ_ij B_kl`. -/
def dsym (B : ι → ι → ℝ) (i j k l : ι) : ℝ :=
  dlt i j * B k l + dlt i k * B j l + dlt i l * B j k + dlt j k * B i l + dlt j l * B i k +
    dlt k l * B i j

/-- Contraction of the last two indices, `(contr T)_ij = T_ijkk`. -/
def contr (T : ι → ι → ι → ι → ℝ) (i j : ι) : ℝ := ∑ k, T i j k k

/-- Trace of a matrix. -/
def mtrace (B : ι → ι → ℝ) : ℝ := ∑ i, B i i

/-- The traceless part `B - (tr B / n) δ`. -/
def traceless (B : ι → ι → ℝ) (i j : ι) : ℝ := B i j - mtrace B / dim ι * dlt i j

/-- The quartic form `T(φ,φ,φ,φ)`. -/
def form4 (T : ι → ι → ι → ι → ℝ) (φ : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, T i j k l * (φ i * φ j * φ k * φ l)

/-- The quadratic form `B(φ,φ)`. -/
def form2 (B : ι → ι → ℝ) (φ : ι → ℝ) : ℝ := ∑ i, ∑ j, B i j * (φ i * φ j)

/-! Arrays attached to a cubic array `c`. -/

/-- The symmetrized quartic tensor of a cubic,
`S_ijkl = c_ijm c_klm + c_ikm c_jlm + c_ilm c_jkm`. -/
def sq4 (c : ι → ι → ι → ℝ) (i j k l : ι) : ℝ :=
  ∑ m, (c i j m * c k l m + c i k m * c j l m + c i l m * c j k m)

/-- The strength `x = Σ c_ijk²`. -/
def strength (c : ι → ι → ι → ℝ) : ℝ := cinner c c

/-- The trace vector `v_i = c_iaa`. -/
def trVec (c : ι → ι → ι → ℝ) (i : ι) : ℝ := ∑ a, c i a a

/-- The double contraction `M_ij = c_ikl c_jkl`. -/
def mMat (c : ι → ι → ι → ℝ) (i j : ι) : ℝ := ∑ k, ∑ l, c i k l * c j k l

/-- The mixed contraction `K(d)_ij = c_iab d_jab` of a cubic `c` with a second array `d`. -/
def kMat (c d : ι → ι → ι → ℝ) (i j : ι) : ℝ := ∑ a, ∑ b, c i a b * d j a b

end Quartic

end

end ThirteenPlanes
