module

public import ThirteenPlanes.Basic
public import ThirteenPlanes.Energy
public import ThirteenPlanes.HarmonicVariances
public import ThirteenPlanes.HessianSpectrum
public import ThirteenPlanes.CubicRotation
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

/-! Proposition types for the unrestricted analytic results in Section 9. -/

open Filter Set
open scoped BigOperators RealInnerProductSpace Topology

namespace ThirteenPlanes.PencilFlow.Statements

noncomputable section

open SymmetricCubic Quartic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The vector field in the time `s = εℓ`, after writing `h = 4π√ε • κ`. -/
def rescaledField (κ : SymmetricCubic V) : SymmetricCubic V :=
  (1 / 2 : ℝ) • κ - (1 / 2 : ℝ) • κ.insert κ.doubleContraction -
    (2 : ℝ) • κ.triangleContraction

/-- The exact conversion between the physical and rescaled vector fields. -/
abbrev GradientScaling (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ κ : SymmetricCubic V,
    oneLoopBeta ε ((4 * Real.pi * Real.sqrt ε) • κ) =
      (ε * (4 * Real.pi * Real.sqrt ε)) • rescaledField κ

/-- Lemma 9-gradient, the A-function and the two forms of its tetrahedral term. -/
abbrev GradientPotential (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop :=
  ∀ (e : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V) (κ : SymmetricCubic V),
    let K := κ.doubleContraction
    let a := κ.coefficient e
    aFunction κ = -(1 / 4) * κ.tensorPairing κ +
      3 / 8 * LinearMap.trace ℝ V (K * K) + 1 / 2 * κ.tetrahedron ∧
    κ.tetrahedron = κ.tensorPairing κ.triangleContraction ∧
    κ.tetrahedron = Coords.tetSum a a a a

/-- Lemma 9-gradient, with the coefficient pairing as the metric on cubics. -/
abbrev Gradient (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop :=
  ∀ κ : SymmetricCubic V, HasGradientAt aFunction (-rescaledField κ) κ

/-- Lemma 9-gradient, dissipation along any solution, including one-sided endpoints. -/
abbrev GradientDissipation (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop :=
  ∀ (trajectory : ℝ → SymmetricCubic V) (times : Set ℝ),
    IsIntegralCurveOn trajectory (fun _ => rescaledField) times →
    ∀ s ∈ times, HasDerivWithinAt (aFunction ∘ trajectory)
      (- ‖rescaledField (trajectory s)‖ ^ 2) times s

/-- The scalar potential of a cubic on the real field space. -/
def fieldPotential (h : SymmetricCubic V) (φ : V) : ℝ := ‖h.squareMap φ‖ ^ 2 / 8

/-- Proposition variance (a), for every cubic and every orthonormal basis. -/
abbrev VarianceA (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : Prop :=
  ∀ (e : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V) (κ : SymmetricCubic V),
    let n : ℝ := Module.finrank ℝ V
    let x := κ.tensorPairing κ
    let v := κ.traceVec e
    let traceSq := vinner v v
    let K₀ := κ.mTraceless e
    let R₀ := κ.sigTraceless e
    let H := κ.harmQuartic e
    let V₂ := sphereVariance (κ.energyPart2 e)
    let V₄ := sphereVariance (κ.energyPart4 e)
    aFunction κ - floorValue n =
      (n + 10) / (8 * n * (n + 2)) * (x - floorStrength n) ^ 2 +
      minner K₀ K₀ / 8 + traceSq * (4 * x + traceSq) / (4 * n * (n + 2)) +
      minner R₀ R₀ / (2 * (n + 4)) + qinner H H / 12 ∧
    minner R₀ R₀ / (2 * (n + 4)) = 4 * n * (n + 2) * (n + 4) * V₂ ∧
    qinner H H / 12 = 2 * n * (n + 2) * (n + 4) * (n + 6) * V₄ ∧
    V₂ + V₄ = sphereVariance (fieldPotential κ) ∧
    floorValue n ≤ aFunction κ ∧
    (aFunction κ = floorValue n ↔
      x = floorStrength n ∧ κ.TraceFree ∧
      (∃ m : ℝ, κ.doubleContraction = m • (LinearMap.id : V →ₗ[ℝ] V)) ∧
      ∃ u : ℝ, ConstantOnSphere (fieldPotential κ) u)

/-- Proposition variance (b), with the full sphere variance in the trace-free scalar case. -/
abbrev VarianceB (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : Prop :=
  ∀ κ : SymmetricCubic V, κ.TraceFree →
    ∀ m : ℝ, κ.doubleContraction = m • (LinearMap.id : V →ₗ[ℝ] V) →
    let n : ℝ := Module.finrank ℝ V
    aFunction κ - floorValue n =
      (n + 10) / (8 * n * (n + 2)) * (κ.tensorPairing κ - floorStrength n) ^ 2 +
      2 * n * (n + 2) * (n + 4) * (n + 6) * sphereVariance (fieldPotential κ)

/-- The normalization of any harmonic round cubic used in Proposition 9-hessian. -/
def unitRoundCubic (h : SymmetricCubic V) (c : ℝ) : SymmetricCubic V :=
  Real.sqrt (2 / (c * ((Module.finrank ℝ V : ℝ) + 10))) • h

/-- The trace vector of a cubic, written in the field space. -/
def cubicTrace (Y : SymmetricCubic V) : V :=
  let e := stdOrthonormalBasis ℝ V
  ∑ i, Y.L (e i) (e i)

/-- The Frobenius adjoint of `A ↦ C.insert A` on skew operators, in the pullback convention. -/
def rotationAdjoint (C Y : SymmetricCubic V) : V →ₗ[ℝ] V :=
  let e := stdOrthonormalBasis ℝ V
  let J := kMat (C.coefficient e) (Y.coefficient e)
  skewOp e fun i j => (3 / 2 : ℝ) * (J i j - J j i)

/-- The Hessian operator for the coefficient metric, as the derivative of the gradient. -/
def hessianOperator (C : SymmetricCubic V) : Module.End ℝ (SymmetricCubic V) :=
  (fderiv ℝ (gradient aFunction) C).toLinearMap

/-- Proposition 9-hessian (a), including the exact operator and its three eigenspaces. -/
abbrev HessianA (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : Prop :=
  ∀ (h : SymmetricCubic V) (c : ℝ), h.TraceFree → ThirteenPlanes.IsRound h c →
    let C := unitRoundCubic h c
    let H := hessianOperator C
    let n := Module.finrank ℝ V
    let μ : ℝ := 2 / ((n : ℝ) + 10)
    rescaledField C = 0 ∧
    (∀ Y : SymmetricCubic V,
      H Y = Y + (3 * μ) • traceAdjoint (cubicTrace Y) -
        (1 / 3 : ℝ) • C.insert (rotationAdjoint C Y)) ∧
    LinearMap.ker H = rotationSpace C ∧
    1 < traceEigenvalue n ∧
    Module.End.eigenspace H (traceEigenvalue n) = traceSpace V ∧
    Module.finrank ℝ (traceSpace V) = n ∧
    Module.End.eigenspace H 1 = complementSpace C ∧
    (∀ Y : SymmetricCubic V,
      (1 / 3 : ℝ) • C.insert (rotationAdjoint C Y) = (rotationSpace C).starProjection Y)

/-- Proposition 9-hessian (b), with the stabilizer characterized by its skew generators. -/
abbrev HessianB (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : Prop :=
  ∀ (h : SymmetricCubic V) (c : ℝ), h.TraceFree → ThirteenPlanes.IsRound h c →
    let C := unitRoundCubic h c
    let n := Module.finrank ℝ V
    Module.finrank ℝ (rotationSpace C) = n.choose 2 - Module.finrank ℝ (skewStabilizer C) ∧
    (∀ Ω : skewEnd V, Ω ∈ skewStabilizer C ↔
      ∀ s : ℝ,
        let A : skewEnd V := s • Ω
        C.pullback (skewRotation A.val (mem_skewEnd.mp A.property)).toLinearMap = C) ∧
    Module.finrank ℝ (Module.End.eigenspace (hessianOperator C) 1) =
      (n + 2).choose 3 - n - Module.finrank ℝ (rotationSpace C)

/-- Proposition 9-hessian (c), with forward extension and a limit for every trajectory. -/
abbrev HessianC (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : Prop :=
  ∀ (h : SymmetricCubic V) (c : ℝ), h.TraceFree → ThirteenPlanes.IsRound h c →
    let C := unitRoundCubic h c
    ∃ U : Set (SymmetricCubic V), IsOpen U ∧
      (∀ Q : V ≃ₗᵢ[ℝ] V, C.pullback Q.toLinearMap ∈ U) ∧
      ∀ X ∈ U,
        (∃ trajectory : ℝ → SymmetricCubic V, trajectory 0 = X ∧
          IsIntegralCurveOn trajectory (fun _ => rescaledField) (Ici 0) ∧
          ∀ (T : ℝ) (segment : ℝ → SymmetricCubic V), 0 < T → segment 0 = X →
            IsIntegralCurveOn segment (fun _ => rescaledField) (Icc 0 T) →
            EqOn trajectory segment (Icc 0 T)) ∧
        (∀ trajectory : ℝ → SymmetricCubic V, trajectory 0 = X →
          IsIntegralCurveOn trajectory (fun _ => rescaledField) (Ici 0) →
          ∃ Q : V ≃ₗᵢ[ℝ] V, Tendsto trajectory atTop (𝓝 (C.pullback Q.toLinearMap)))

end

end ThirteenPlanes.PencilFlow.Statements
