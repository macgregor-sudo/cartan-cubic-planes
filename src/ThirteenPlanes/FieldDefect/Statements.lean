module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import ThirteenPlanes.Quaternionic.Definitions

@[expose] public section

/-! The radial-gradient defect and the six-frame quaternionic overlap defect.

For `m ≥ 1` let `𝒲_m` be the set of cubics
`W(z) = ∑ᵢ Re zᵢ³ + ∑_{i<j<k} T_{ijk}(zᵢ,zⱼ,z_k)` on `ℂ^m = ℝ^{2m}`, each `T_{ijk}` real trilinear
over `ℝ` (conjugates allowed), with no hypothesis on the gradient, and
`def W = max_{‖z‖=1} |(1/9)‖∇W(z)‖² − 1|`, `δ_m = inf_{W ∈ 𝒲_m} def W`.
For frames `p¹,…,pᵏ` of `H₃(ℍ)`, `μ = max_{i<j} max_{a,b} |tr(pⁱ_a • pʲ_b) − 1/3|`.
(i) If `m ∉ {1,4,13}` then `def` attains `δ_m` on `𝒲_m` and `δ_m > 0`.
(ii) `δ₇ ≤ 3/4`, with `def W = 3/4` for `W = W₄(z₁,…,z₄) + Re z₅³ + Re z₆³ + Re z₇³`.
(iii) `μ` attains a positive minimum `ε₆` on `𝓕⁶`, and `μ ≥ ε₆` on `𝓕ᵏ` for every `k ≥ 6`.

Carriers. `ℂ^m` is `EuclideanSpace ℂ (Fin m)`, whose real structure is `ℝ^{2m}` with its Euclidean
norm; `∇W` is Mathlib's `gradient` for that real inner product, so `‖∇W z‖` is the length of the
real gradient. The trilinear forms are arbitrary real multilinear maps `ℂ × ℂ × ℂ → ℝ`. The frames
are the native quaternionic frames `QuaternionicMUB.Frame` of the quaternionic five-basis bound development,
with `tr(p • q)` its `traceForm`. The field-count hypothesis `Section6.FieldsCount` is the count clause of the radial field classification. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading

namespace Defect

open Complex

/-- The field space `ℂ^m = ℝ^{2m}` with its Euclidean norm. -/
abbrev Field (m : ℕ) := EuclideanSpace ℂ (Fin m)

/-- Strictly increasing index triples `i < j < k`. -/
def Triple (m : ℕ) := {t : Fin 3 → Fin m // t 0 < t 1 ∧ t 1 < t 2}

instance (m : ℕ) : Fintype (Triple m) := by unfold Triple; infer_instance

instance (m : ℕ) : DecidableEq (Triple m) := by unfold Triple; infer_instance

/-- Real trilinear forms `ℂ × ℂ × ℂ → ℝ`, linear over `ℝ` in each slot. -/
abbrev TriForm := MultilinearMap (RingHom.id ℝ) (fun _ : Fin 3 => ℂ) ℝ

/-- The diagonal part `∑ᵢ Re zᵢ³`. -/
def diagonalCubic {m : ℕ} (z : Field m) : ℝ := ∑ i, ((z i) ^ 3).re

/-- `W_T(z) = ∑ᵢ Re zᵢ³ + ∑_{i<j<k} T_{ijk}(zᵢ,zⱼ,z_k)`. -/
def fieldCubic {m : ℕ} (T : Triple m → TriForm) (z : Field m) : ℝ :=
  diagonalCubic z + ∑ t : Triple m, T t (fun a => z (t.1 a))

/-- The class `𝒲_m`. -/
def cubicClass (m : ℕ) : Set (Field m → ℝ) := {W | ∃ T : Triple m → TriForm, W = fieldCubic T}

/-- The length of the real gradient. -/
def gradNorm {m : ℕ} (W : Field m → ℝ) (z : Field m) : ℝ := ‖gradient W z‖

/-- `def W = max_{‖z‖=1} |(1/9)‖∇W(z)‖² − 1|` (a supremum over the unit sphere; it is a maximum
for every `W ∈ 𝒲_m`, `m ≥ 1`, since the integrand is continuous and the sphere compact). -/
def defect {m : ℕ} (W : Field m → ℝ) : ℝ :=
  sSup ((fun z => |(1 / 9 : ℝ) * gradNorm W z ^ 2 - 1|) '' Metric.sphere (0 : Field m) 1)

/-- `δ_m = inf_{W ∈ 𝒲_m} def W`. -/
def delta (m : ℕ) : ℝ := sInf (defect '' cubicClass m)

/-- Example four-field model, equation four-field polynomial:
`W₄(z) = Re[z₀³+z₁³+z₂³+z₃³ − 3z₁z₂z₃ − 3z₀(z̄₁z₂ + z̄₂z₃ + z̄₃z₁)]`. -/
def W4 (z₀ z₁ z₂ z₃ : ℂ) : ℝ :=
  (z₀ ^ 3 + z₁ ^ 3 + z₂ ^ 3 + z₃ ^ 3 - 3 * z₁ * z₂ * z₃
    - 3 * z₀ * ((starRingEnd ℂ) z₁ * z₂ + (starRingEnd ℂ) z₂ * z₃ + (starRingEnd ℂ) z₃ * z₁)).re

/-- The seven-field cubic of (ii): `W₄` on the first four fields plus three uncoupled planes
(fields are indexed `0,…,6`; the manuscript's `z₁,…,z₇`). -/
def sevenCubic (z : Field 7) : ℝ :=
  W4 (z 0) (z 1) (z 2) (z 3) + ((z 4) ^ 3).re + ((z 5) ^ 3).re + ((z 6) ^ 3).re

open QuaternionicMUB in
/-- `μ(p¹,…,pᵏ) = max_{i<j} max_{a,b} |tr(pⁱ_a • pʲ_b) − 1/3|`. -/
def mu {k : ℕ} (F : Fin k → Frame) : ℝ :=
  sSup ((fun q : Fin k × Fin k × Fin 3 × Fin 3 =>
      |traceForm ((F q.1).point q.2.2.1) ((F q.2.1).point q.2.2.2) - 1 / 3|) ''
    {q | q.1 < q.2.1})

end Defect

open Defect

/-- Hypothesis from the radial field classification (Theorem A(i)), first sentence:
for a cubic `W` as in radial field count and model (an element of `𝒲_m`, `m ≥ 1`) whose real gradient has length
depending only on `‖z‖`, `m` is `1`, `4` or `13`. -/
def FieldClassification.FieldsCount : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ W ∈ cubicClass m,
    (∃ φ : ℝ → ℝ, ∀ z : Field m, gradNorm W z = φ ‖z‖) → m = 1 ∨ m = 4 ∨ m = 13

/-- Radial field defect (i). -/
def Statements.DefectAttained : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≠ 1 → m ≠ 4 → m ≠ 13 →
    (∃ W ∈ cubicClass m, defect W = delta m) ∧ 0 < delta m

/-- Radial field defect (ii). -/
def Statements.DefectSeven : Prop :=
  sevenCubic ∈ cubicClass 7 ∧ defect sevenCubic = 3 / 4 ∧ delta 7 ≤ 3 / 4

open QuaternionicMUB in
/-- Radial field defect (iii). -/
def Statements.SixFramesGap : Prop :=
  ∃ ε₆ : ℝ, 0 < ε₆ ∧ (∃ F : Fin 6 → Frame, mu F = ε₆) ∧ (∀ F : Fin 6 → Frame, ε₆ ≤ mu F) ∧
    ∀ k : ℕ, 6 ≤ k → ∀ F : Fin k → Frame, ε₆ ≤ mu F

end ThirteenPlanes.AlbertGrading

end
