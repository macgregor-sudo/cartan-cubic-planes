module

public import ThirteenPlanes.AlbertGrading.Tits.HomogeneousProducts
public import ThirteenPlanes.AlbertGrading.Tits.NonVacuity
public import ThirteenPlanes.Shares.Support
public import ThirteenPlanes.NativeFramesPlaneData
public import Glennie.Automorphism
public import Glennie.Diagonalization

@[expose] public section

/-!
# Targets for recognition of the graded frame system (Section 5)

The compact first Tits carrier `J_T` is
`Tits.CompactTits`, `J_T ⊗ ℂ` is `FirstTits ℂ` with the conjugation `σ = Tits.compactInvolution`,
the product `(5-tits)` is `paperProduct`, `u_g = ι_k(D_v)` is `titsBasis g`, frames are
`IsTitsFrame`, contrasts are `titsContrast` and the exterior frame is `exteriorPoint`.

The graded frames of the first-Tits grading and Weyl basis are `p_{g,a} = (e + ω^{-a} u_g + ω^a u_{-g})/3`
(the display after the proof of the first-Tits grading and Weyl basis); `gradedFrame g a` is this element of `J_T`.
The eigenframe of `ι₀(D_v)`, labelled by the exponent of the eigenvalue, is `gradedFrame (v,0)`
(`weylEigenframe`).

recognition of systems with 52 positive shares is stated on the native Albert algebra `Glennie.Albert` (the paper's `𝔸`): a
thirteen-plane system is a `TightNativeCode` (thirteen frames, pairwise unbiased:
`tr(p_a ∘ q_b) = 1/3`), its shares are `planeShare nativeEqualCubic` of its planes, and an
automorphism is a `Glennie.CompactAutomorphism` (a real-linear bijection preserving the Jordan
product and the trace; the trace condition is automatic for Jordan automorphisms and only
strengthens the conclusion).
-/

open scoped Matrix
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

/-- Coordinates of `p_{g,a} = (e + ω^{-a} u_g + ω^a u_{-g})/3`. -/
def gradedCoords (g : Charge) (a : ZMod 3) : FirstTits ℂ :=
  (1 / 3 : ℂ) • (firstTitsOne + chargePhase (-a) • titsBasis g + chargePhase a • titsBasis (-g))

theorem gradedCoords_fixed (g : Charge) (a : ZMod 3) :
    compactInvolution (gradedCoords g a) = gradedCoords g a := by
  have h1 : compactInvolution firstTitsOne = firstTitsOne := by
    rw [← titsBasis_zero, titsBasis_involution, neg_zero]
  have hs : star (1 / 3 : ℂ) = 1 / 3 := by simp
  have hn : star (chargePhase (-a)) = chargePhase a := by
    rw [chargePhase_neg, star_star]
  have hp : star (chargePhase a) = chargePhase (-a) := (chargePhase_neg a).symm
  rw [gradedCoords, compactInvolution_complex_smul, map_add, map_add,
    compactInvolution_complex_smul, compactInvolution_complex_smul, titsBasis_involution,
    titsBasis_involution, neg_neg, h1, hs, hn, hp, add_assoc, add_assoc,
    add_comm (chargePhase a • titsBasis (-g))]

/-- The graded idempotent `p_{g,a}` as an element of `J_T`. -/
def gradedFrame (g : Charge) (a : ZMod 3) : CompactTits :=
  CompactTits.ofFixed (gradedCoords g a) (gradedCoords_fixed g a)

@[simp] theorem gradedFrame_coordinates (g : Charge) (a : ZMod 3) :
    CompactTits.coordinates (gradedFrame g a) = gradedCoords g a := rfl

/-- The eigenframe of `ι₀(D_v)`, labelled by the exponent of the eigenvalue. -/
def weylEigenframe (v : WeylLabel) : ZMod 3 → CompactTits := gradedFrame (chargeFrom v 0)

/-- The vectors `e`, `u_f`, `σ u_f` for the frames `f` of a family. -/
def titsContrastLines (F : Fin 13 → ZMod 3 → CompactTits) : Set (FirstTits ℂ) :=
  {firstTitsOne} ∪ Set.range (fun i => titsContrast (F i)) ∪
    Set.range (fun i => compactInvolution (titsContrast (F i)))

/-- Recognition of the graded frame system. Thirteen frames `F i` of `J_T` (indexed; a frame is identified with its
set of idempotents, so "contains" and "`f ≠ g`" refer to `Set.range`). If the family contains the
four eigenframes of the `ι₀(D_v)` and the exterior frame, and for any two different frames every
product of `u_f` or `σ u_f` with `u_g` or `σ u_g` is a nonzero multiple of `e` or of a contrast or
conjugate contrast of a frame of the family, then every frame of the family is, as a set, the
graded frame `{p_{g,a}}` of one point `{±g}`. -/
def Statements.Recognition : Prop :=
  ∀ F : Fin 13 → ZMod 3 → CompactTits, (∀ i, IsTitsFrame (F i)) →
    (∀ v : WeylLabel, v ≠ 0 → ∃ i, Set.range (F i) = Set.range (weylEigenframe v)) →
    (∃ i, Set.range (F i) = Set.range exteriorPoint) →
    (∀ i j, Set.range (F i) ≠ Set.range (F j) →
      ∀ x ∈ ({titsContrast (F i), compactInvolution (titsContrast (F i))} : Set (FirstTits ℂ)),
      ∀ y ∈ ({titsContrast (F j), compactInvolution (titsContrast (F j))} : Set (FirstTits ℂ)),
      ∃ c : ℂ, c ≠ 0 ∧ ∃ m ∈ titsContrastLines F, firstTitsJordanProduct x y = c • m) →
    ∀ i, ∃ g : Charge, g ≠ 0 ∧ Set.range (F i) = Set.range (gradedFrame g)

/-- Recognition of systems with 52 positive shares. The Albert algebra has a thirteen-plane system with exactly 52 positive shares,
and for any two such systems there are an automorphism `φ` of `𝔸`, a relabelling `σ` of the frames
and relabellings `τ i` of the outcomes of each frame with `φ(p_{i,a}) = p'_{σ i, τ_i a}` for all
39 idempotents. -/
def Statements.Sparsest : Prop :=
  (∃ c : TightNativeCode,
      (RoundCubics.positivePlaneTriples nativeEqualCubic c.decomposition).card = 52) ∧
    ∀ c c' : TightNativeCode,
      (RoundCubics.positivePlaneTriples nativeEqualCubic c.decomposition).card = 52 →
      (RoundCubics.positivePlaneTriples nativeEqualCubic c'.decomposition).card = 52 →
      ∃ φ : Glennie.CompactAutomorphism, ∃ σ : Equiv.Perm (Fin 13),
        ∃ τ : Fin 13 → Equiv.Perm (Fin 3), ∀ i a, φ.equiv (c.point i a) = c'.point (σ i) (τ i a)

/-- `ω_u^m` in `ℂ_u = ℝ + ℝu`, `ω_u = -½ + (√3/2) u`, computed through `ℂ_u ≅ ℂ`, `u ↦ i`:
`ω_u^m = Re(ω^m) + Im(ω^m) u`. -/
def omegaU (u : Glennie.Octonion) (m : ZMod 3) : Glennie.Octonion :=
  (((chargePhase m).re : Quaternion ℝ), 0) + (chargePhase m).im • u

/-- The Fourier frame `{P_0, P_1, P_2}` of the unbiased-pair and slot normal forms (i), `(P_k)_{ij} = ω_u^{k(i-j)}/3`, in the
native coordinates (diagonal entries, then the upper entries `(0,1)`, `(0,2)`, `(1,2)`). -/
def fourierFrameU (u : Glennie.Octonion) (k : ZMod 3) : Glennie.Albert :=
  ⟨1 / 3, 1 / 3, 1 / 3, (1 / 3 : ℝ) • omegaU u (k * (0 - 1)),
    (1 / 3 : ℝ) • omegaU u (k * (0 - 2)), (1 / 3 : ℝ) • omegaU u (k * (1 - 2))⟩

/-- Unbiased-pair and slot normal forms (i) for `𝕂 = 𝕆`. For
unbiased frames `F, G` of `𝔸` there are an automorphism `φ` and a unit imaginary `u ∈ 𝕆` with
`φ(F)` the diagonal frame and `φ(G)` the Fourier frame `{P_k}`, as sets. The automorphism is a
`Glennie.CompactAutomorphism` (product and trace preserving; Jordan automorphisms of `𝔸` preserve
the trace). The clause "all these matrices lie in `H₃(ℂ_u)`" is not used and not assumed. -/
def FrameProperties.NormalFormOctonion : Prop :=
  ∀ F G : Fin 3 → Glennie.Albert, Glennie.Frame F → Glennie.Frame G →
    (∀ a b, Glennie.inner (F a) (G b) = 1 / 3) →
    ∃ φ : Glennie.CompactAutomorphism, ∃ u : Glennie.Octonion,
      u.1.re = 0 ∧ Glennie.octNormSq u = 1 ∧
      Set.range (fun a => φ.equiv (F a)) = Set.range Glennie.standardFrame ∧
      Set.range (fun a => φ.equiv (G a)) = Set.range (fourierFrameU u)

/-- The sentence "the automorphism group of `J_T` is transitive on unbiased pairs, up to labels"
in the proof of the recognition of systems with 52 positive shares (step *Normalizing a quartet*): any ordered pair of unbiased frames
of `J_T` is carried by a trace-preserving automorphism to the eigenframes of `ι₀(Z) = ι₀(D_{(0,1)})`
and `ι₀(X) = ι₀(D_{(1,0)})`, as sets. The paper derives it from the unbiased-pair and slot normal forms (i) and the
transitivity of `Aut(𝕆)` on unit imaginary octonions. -/
def OrbitHypotheses.PairNormalization : Prop :=
  ∀ P Q : ZMod 3 → CompactTits, IsTitsFrame P → IsTitsFrame Q →
    (∀ a b, CompactTits.trace (CompactTits.product (P a) (Q b)) = 1 / 3) →
    ∃ f : CompactTits ≃ₗ[ℝ] CompactTits, IsTitsAutomorphism f ∧
      (∀ x, CompactTits.trace (f x) = CompactTits.trace x) ∧
      Set.range (fun a => f (P a)) = Set.range (weylEigenframe (0, 1)) ∧
      Set.range (fun a => f (Q a)) = Set.range (weylEigenframe (1, 0))

end

end ThirteenPlanes.AlbertGrading
