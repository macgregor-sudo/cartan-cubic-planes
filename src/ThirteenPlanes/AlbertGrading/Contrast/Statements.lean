module

public import ThirteenPlanes.AlbertGrading.Contrast.Complexification
public import ThirteenPlanes.Graded.FullLineModel
public import ThirteenPlanes.Weyl
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

/-!
# Targets for Fourier contrast identities and qutrit contrast table (Section 5)

Carriers. `J = Glennie.Albert` with `Glennie.jordan`, `Glennie.trace`; a Jordan frame is
`Glennie.Frame` (ordered trace-one orthogonal idempotents with sum `1`). `J_ℂ` is `AlbertC`
(pairs `x + i y`, product and trace form extended complex-bilinearly, `conj` fixing `J`).
`ω = e^{2πi/3}` is the `chargeRoot = (-1 + i√3)/2`, and `ω^a` for `a ∈ 𝔽₃ = ZMod 3`
is `chargePhase a`. The Hermitian complex three-by-three Jordan algebra is the accepted
`Graded.FullHermitian3` with `Graded.fullHermitianProduct` (`½(XY+YX)`), and `D_v` is the accepted
`weylMatrix v` (`D_v e_j = ω^{-ab+bj} e_{j+a}`, i.e. `ω^{-ab} X^a Z^b`).
-/

open scoped Matrix

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Contrast Contrast.AlbertC Graded

namespace Contrast

/-- `μ₃ = {1, ω, ω²}`. -/
def mu3 : Set ℂ := {1, chargeRoot, chargeRoot ^ 2}

/-- The outcome label `a : Fin 3` read in `𝔽₃ = ZMod 3` (the identity map). -/
def outcome (a : Fin 3) : ZMod 3 := a

/-- The contrast `u_f = ∑_{a ∈ 𝔽₃} ω^a p_{fa} ∈ J_ℂ` of an ordered frame. -/
def contrast (p : Fin 3 → Glennie.Albert) : AlbertC :=
  ∑ a : Fin 3, chargePhase (outcome a) • ofReal (p a)

/-- The plane `U_F = ℝ q₁ + ℝ q₂ + ℝ q₃`, `q_a = p_a - e/3`, of a frame (Section 3). -/
def framePlane (p : Fin 3 → Glennie.Albert) : Submodule ℝ Glennie.Albert :=
  Submodule.span ℝ (Set.range fun a => p a - (1 / 3 : ℝ) • (1 : Glennie.Albert))

/-- Two frames are unbiased: `tr (p_a ∘ q_b) = 1/3` for all `a, b`. -/
def Unbiased (p q : Fin 3 → Glennie.Albert) : Prop :=
  ∀ a b, Glennie.trace (Glennie.jordan (p a) (q b)) = 1 / 3

/-- A Jordan frame of `Herm₃(ℂ)`: trace-one orthogonal idempotents with sum the unit. -/
structure HermFrame (P : Fin 3 → FullHermitian3) : Prop where
  trace_one : ∀ a, (Matrix.trace (P a).val).re = 1
  idempotent : ∀ a, fullHermitianProduct (P a) (P a) = P a
  orthogonal : ∀ a b, a ≠ b → fullHermitianProduct (P a) (P b) = 0
  sum_unit : P 0 + P 1 + P 2 = ⟨1, Matrix.isHermitian_one⟩

/-- Unbiased frames of `Herm₃(ℂ)` for its own trace. -/
def HermUnbiased (P R : Fin 3 → FullHermitian3) : Prop :=
  ∀ a b, (Matrix.trace (fullHermitianProduct (P a) (R b)).val).re = 1 / 3

/-- The four points of the projective line over `𝔽₃`: `Z`, `X`, `XZ`, `XZ²`. -/
def weylLinePoint : Fin 4 → WeylLabel := ![(0, 1), (1, 0), (1, 1), (1, 2)]

/-- `(1/3)(1 + ω^{-b} D_v + ω^b D_v^*)`, the eigenprojection of `D_v` for `ω^b`. -/
def weylEigenMatrix (v : WeylLabel) (b : ZMod 3) : Matrix (ZMod 3) (ZMod 3) ℂ :=
  (1 / 3 : ℂ) • (1 + chargePhase (-b) • weylMatrix v + chargePhase b • weylMatrix (-v))

theorem weylEigenMatrix_hermitian (v : WeylLabel) (b : ZMod 3) :
    (weylEigenMatrix v b).IsHermitian := by
  unfold weylEigenMatrix
  change Matrix.conjTranspose _ = _
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  change star (1 / 3 : ℂ) • (1 + star (chargePhase (-b)) • (weylMatrix v)ᴴ +
    star (chargePhase b) • (weylMatrix (-v))ᴴ) = _
  rw [weylMatrix_adjoint, weylMatrix_adjoint, neg_neg, ← chargePhase_neg, ← chargePhase_neg,
    neg_neg]
  simp only [star_div₀, star_one, star_ofNat]
  abel_nf

/-- The eigenframe of `D_v` at the `k`-th projective point, labelled by the eigenvalue exponent. -/
def weylEigenframe (k : Fin 4) (b : Fin 3) : FullHermitian3 :=
  ⟨weylEigenMatrix (weylLinePoint k) (outcome b), weylEigenMatrix_hermitian _ _⟩

/-- Linear dependence of two vectors of `𝔽₃²`. -/
def Dependent (v w : WeylLabel) : Prop := v = 0 ∨ ∃ c : ZMod 3, w = c • v

end Contrast

namespace FrameProperties

/-- The four-plane theorem (iii) in frame form (with Jordan frame and closed-plane correspondence, planes determine frames): any four
pairwise unbiased frames of `Herm₃(ℂ)` are carried by conjugation with a unitary matrix to the
four eigenframes of the `D_v`, after relabelling the frames and the outcomes of each frame. -/
def QutritFourFrames : Prop :=
  ∀ F : Fin 4 → Fin 3 → FullHermitian3, (∀ i, HermFrame (F i)) →
    (∀ i j, i ≠ j → HermUnbiased (F i) (F j)) →
    ∃ U ∈ Matrix.unitaryGroup (Fin 3) ℂ, ∃ π : Equiv.Perm (Fin 4),
      ∃ σ : Fin 4 → Equiv.Perm (Fin 3),
        ∀ i a, U * (F i a).val * star U = (weylEigenframe (π i) (σ i a)).val

end FrameProperties

namespace Statements

/-- Fourier contrast identities. (i) For every ordered Jordan frame `p`: `u∘u = ū`, `u∘ū = e`,
`⟨u,u⟩ = 0`, `⟨u,ū⟩ = 3`, `p_a = (e + ω^{-a} u + ω^a ū)/3`; the complexified plane
`U_F ⊗ ℂ = {x + i y : x, y ∈ U_F}` is the complex span of `u, ū`; every outcome permutation
replaces `u` by `ζ u` or `ζ ū`, `ζ ∈ μ₃`. (ii) Two frames are unbiased iff
`⟨u_f,u_g⟩ = ⟨u_f,ū_g⟩ = 0`. -/
def FrameContrast : Prop :=
  (∀ p : Fin 3 → Glennie.Albert, Glennie.Frame p →
    jordan (contrast p) (contrast p) = conj (contrast p) ∧
    jordan (contrast p) (conj (contrast p)) = ofReal 1 ∧
    pair (contrast p) (contrast p) = 0 ∧
    pair (contrast p) (conj (contrast p)) = 3 ∧
    (∀ a : Fin 3, ofReal (p a) = (1 / 3 : ℂ) • (ofReal 1 + chargePhase (-outcome a) • contrast p +
      chargePhase (outcome a) • conj (contrast p))) ∧
    (∀ z : AlbertC, (z.re ∈ framePlane p ∧ z.im ∈ framePlane p) ↔
      z ∈ Submodule.span ℂ {contrast p, conj (contrast p)}) ∧
    (∀ σ : Equiv.Perm (Fin 3), ∃ ζ ∈ mu3,
      contrast (p ∘ σ) = ζ • contrast p ∨ contrast (p ∘ σ) = ζ • conj (contrast p))) ∧
  (∀ p q : Fin 3 → Glennie.Albert, Glennie.Frame p → Glennie.Frame q →
    (Unbiased p q ↔
      pair (contrast p) (contrast q) = 0 ∧ pair (contrast p) (conj (contrast q)) = 0))

/-- Qutrit contrast table. Let `Q ⊆ J` be a unital subalgebra isomorphic to `Herm₃(ℂ)` containing four
pairwise unbiased frames. Their contrasts and conjugate contrasts can be labelled `u_v`,
`v ∈ 𝔽₃² ∖ 0`, with `u_{-v} = ū_v` and `u_0 = e`, so that `u_v ∘ u_w` is a nonzero multiple of
`u_{v+w}` for all `v, w`: `1` if `v, w` are dependent, in `-½ μ₃` if independent. -/
def QutritContrastTable : Prop :=
  ∀ Q : Submodule ℝ Glennie.Albert, (1 : Glennie.Albert) ∈ Q →
    (∀ x y, x ∈ Q → y ∈ Q → Glennie.jordan x y ∈ Q) →
    (∃ I : FullHermitian3 ≃ₗ[ℝ] Q,
      ∀ X Y, (I (fullHermitianProduct X Y)).val = Glennie.jordan (I X).val (I Y).val) →
    ∀ F : Fin 4 → Fin 3 → Glennie.Albert, (∀ i, Glennie.Frame (F i)) → (∀ i a, F i a ∈ Q) →
      (∀ i j, i ≠ j → Unbiased (F i) (F j)) →
      ∃ (u : WeylLabel → AlbertC) (lab : Fin 4 → WeylLabel),
        u 0 = ofReal 1 ∧ (∀ v, u (-v) = conj (u v)) ∧
        (∀ i, lab i ≠ 0 ∧ u (lab i) = contrast (F i)) ∧
        (∀ v, v ≠ 0 → ∃ i, v = lab i ∨ v = -lab i) ∧
        (∀ v w, ∃ c : ℂ, c ≠ 0 ∧ jordan (u v) (u w) = c • u (v + w) ∧
          (Dependent v w → c = 1) ∧
          (¬ Dependent v w → c ∈ (fun ζ => -(1 / 2 : ℂ) * ζ) '' mu3))

end Statements

end

end ThirteenPlanes.AlbertGrading
