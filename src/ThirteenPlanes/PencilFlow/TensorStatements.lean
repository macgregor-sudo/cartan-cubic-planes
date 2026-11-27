module

public import ThirteenPlanes.Basic
public import ThirteenPlanes.FamilyVariance.Formula
public import ThirteenPlanes.Basins.Existence
public import ThirteenPlanes.CubicMetric

@[expose] public section

/-! Section 9 in physical units, for an arbitrary round cubic with a complete closed system
of at least two planes. The proposition types below are the interface for the flow proofs. -/

open Filter Set
open scoped Topology

namespace ThirteenPlanes.PencilFlow.Statements

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def pencilLambda (V : Type*) [AddCommGroup V] [Module ℝ V] : ℝ :=
  ((Module.finrank ℝ V : ℝ) - 2) / 12

/-- Coefficients of the infrared vector field at physical strength `c`. -/
def physicalCoefficientField (c lam ε : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  let a := u.1
  let b := u.2
  let k := 2 * c * (a ^ 2 + 3 * lam * b ^ 2)
  (((8 * Real.pi ^ 2 * ε - 3 * k / 2) * a + 6 * c * lam * b ^ 3) / flowScale,
   ((8 * Real.pi ^ 2 * ε - 3 * k / 2) * b +
     6 * c * b ^ 2 * (a - b + lam * b)) / flowScale)

def ratioRate (c lam g t : ℝ) : ℝ :=
  6 * c * g ^ 2 * t ^ 2 * (lam * t + 1) * (1 - t) / flowScale

def strengthRate (c lam ε g t : ℝ) : ℝ :=
  (8 * Real.pi ^ 2 * ε * g - 3 * c * g ^ 3 * (1 + 3 * lam * t ^ 2 -
    2 * lam * t ^ 3)) / flowScale

/-- An assertion about the actual pencil constructed from the planes. -/
abbrev OnClosedPencils (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (assertion : ℝ → CubicPair V → Prop) : Prop :=
  ∀ {m : ℕ}, 2 ≤ m → ∀ (h : SymmetricCubic V) (c : ℝ)
    (planes : PlaneDecomposition V (Fin m)), IsRound h c → IsClosedPlaneSystem h planes →
    assertion c (planePencil h planes)

/-- The two contractions in Proposition pencil-invariant, in the paper's normalization. -/
abbrev PencilContractions (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop := OnClosedPencils V fun c P =>
  ∀ a b : ℝ, let lam := pencilLambda V
    let f := coupling P (a, b)
    f.doubleContraction =
        (2 * c * (a ^ 2 + 3 * lam * b ^ 2)) • (LinearMap.id : V →ₗ[ℝ] V) ∧
      f.triangleContraction = (-3 * c * lam * b ^ 3) • P.diagonalCubic +
        (-3 * c * b ^ 2 * (a - b + lam * b)) • P.mixingCubic

/-- Tangency and invariance under the ambient tensor ODE on any forward interval. -/
abbrev PencilInvariant (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop := OnClosedPencils V fun c P =>
  ∀ ε : ℝ, (∀ u : ℝ × ℝ, oneLoopBeta ε (coupling P u) =
    coupling P (physicalCoefficientField c (pencilLambda V) ε u)) ∧
    ∀ (T : ℝ) (_ : 0 ≤ T) (h : ℝ → SymmetricCubic V),
      IsIntegralCurveOn h (fun _ => oneLoopBeta ε) (Icc 0 T) →
      h 0 ∈ (coupling P).range → ∀ s ∈ Icc 0 T, h s ∈ (coupling P).range

/-- The physical tensor equation gives both coordinate derivatives, including at `a = 0`. -/
abbrev FlowCoordinates (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop := OnClosedPencils V fun c P =>
  ∀ ε : ℝ, 0 < ε → ∀ (u : ℝ → ℝ × ℝ) (s : ℝ),
    HasDerivAt (fun r => coupling P (u r)) (oneLoopBeta ε (coupling P (u s))) s →
    let lam := pencilLambda V
    let g := (u s).1
    let b := (u s).2
    let t := b / g
    let v := physicalCoefficientField c lam ε (u s)
    HasDerivAt u v s ∧
      flowScale * (g * v.2 - b * v.1) = 6 * c * b ^ 2 * (g - b) * (g + lam * b) ∧
      (g ≠ 0 → HasDerivAt (fun r => (u r).2 / (u r).1) (ratioRate c lam g t) s ∧
        HasDerivAt (fun r => (u r).1) (strengthRate c lam ε g t) s) ∧
      (g = 0 → b ≠ 0 → flowScale * v.1 = 6 * c * lam * b ^ 3 ∧ v.1 ≠ 0)

/-- Roots of the ratio velocity. The factor left after dividing out the double root is
nonzero there. -/
abbrev FixedRatios (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop := OnClosedPencils V fun c _ =>
  ∀ g : ℝ, g ≠ 0 → let lam := pencilLambda V
    0 < lam ∧ (∀ t : ℝ, ratioRate c lam g t = 0 ↔ t = 0 ∨ t = 1 ∨ t = -1 / lam) ∧
      ∃ q : ℝ → ℝ, Continuous q ∧ q 0 ≠ 0 ∧ ∀ t, ratioRate c lam g t = t ^ 2 * q t

/-- Global existence for every positive ratio. Monotonicity and the tensor limit refer to
every forward solution with the specified initial coupling. -/
abbrev PositiveMixingLimit (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop := OnClosedPencils V fun c P =>
  ∀ ε g₀ t₀ : ℝ, 0 < ε → g₀ ≠ 0 → 0 < t₀ →
    let initial := (g₀, g₀ * t₀)
    let n : ℝ := Module.finrank ℝ V
    let curve := fun u : ℝ → ℝ × ℝ => IsIntegralCurveOn (fun s => coupling P (u s))
      (fun _ => oneLoopBeta ε) (Ici 0)
    (∃ u : ℝ → ℝ × ℝ, u 0 = initial ∧ curve u) ∧
    ∀ u : ℝ → ℝ × ℝ, u 0 = initial → curve u →
      let t := fun s => (u s).2 / (u s).1
      (∀ s ∈ Ici (0 : ℝ), (u s).1 ≠ 0 ∧ 0 < t s) ∧
      (t₀ ≤ 1 → MonotoneOn t (Ici 0)) ∧ (1 ≤ t₀ → AntitoneOn t (Ici 0)) ∧
      Tendsto t atTop (𝓝 1) ∧
      Tendsto (fun s => coupling P (u s)) atTop
        (𝓝 (((if 0 < g₀ then (1 : ℝ) else -1) * 4 * Real.pi * Real.sqrt ε *
          Real.sqrt (2 / (c * (n + 10)))) • interactionCubic P 1)) ∧
      Tendsto (fun s => (1 + (t s) ^ 2) / 2) atTop (𝓝 1)

/-- The normalized energy in the last limit is the actual energy of every equal split. -/
abbrev EqualSplitEnergy (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop :=
  ∀ {m : ℕ}, 2 ≤ m → ∀ (h : SymmetricCubic V) (c : ℝ)
    (planes : PlaneDecomposition V (Fin m)), IsRound h c → IsClosedPlaneSystem h planes →
    ∀ (i j : Fin m), i ≠ j → ∀ x ∈ planes.plane i, ∀ y ∈ planes.plane j,
      ‖x‖ = 1 → ‖y‖ = 1 → ∀ t : ℝ, let P := planePencil h planes
        ‖(interactionCubic P t).squareMap ((Real.sqrt 2)⁻¹ • (x + y))‖ ^ 2 / c =
          (1 + t ^ 2) / 2

/-- The two first derivatives of the ratio field at its physical fixed strength. -/
abbrev InfraredExponent (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop := OnClosedPencils V fun c _ =>
  ∀ ε g : ℝ, 0 < ε → g ^ 2 / flowScale = 2 * ε / (c * ((Module.finrank ℝ V : ℝ) + 10)) →
    HasDerivAt (ratioRate c (pencilLambda V) g) (-ε) 1 ∧
    HasDerivAt (fun r => ratioRate c (pencilLambda V) r 1) 0 g

/-- The harmonic and isotropic hypotheses of the two-term floor hold on the entire pencil. -/
abbrev PencilFloorConditions (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop := OnClosedPencils V fun _ P =>
  ∀ u : ℝ × ℝ, (coupling P u).TraceFree ∧
    ∃ k : ℝ, (coupling P u).doubleContraction = k • (LinearMap.id : V →ₗ[ℝ] V)

/-- The relative spherical variance is invariant under physical rescaling; its derivative
is strictly negative at each time at which the mixing ratio moves. -/
abbrev VarianceC (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop := OnClosedPencils V fun c P =>
  ∀ ε : ℝ, 0 < ε → ∀ (u : ℝ → ℝ × ℝ) (s : ℝ), (u s).1 ≠ 0 →
    HasDerivAt (fun r => coupling P (u r)) (oneLoopBeta ε (coupling P (u s))) s →
    let t := (u s).2 / (u s).1
    let κ := fun r => (4 * Real.pi * Real.sqrt ε)⁻¹ • coupling P (u r)
    relativeVariance (κ s) = relativeVariance (interactionCubic P t) ∧
      (ratioRate c (pencilLambda V) (u s).1 t ≠ 0 →
        ∃ z : ℝ, z < 0 ∧ HasDerivAt (fun r => relativeVariance (κ r)) z s)

end

end ThirteenPlanes.PencilFlow.Statements
