module

public import ThirteenPlanes.AlbertGrading.Recut.Complexification
public import ThirteenPlanes.Shares.Support
public import ThirteenPlanes.Shares.ThreePlanes
public import ThirteenPlanes.NativeFramesPlaneData
public import ThirteenPlanes.SignedSupport
public import ThirteenPlanes.Weyl

@[expose] public section

/-! # Target for rotation of four planes on a graded line (Section 5)

Let `E` be a ternary grading
group. Fix a line `ℓ` of `PG(2,3)` and an automorphism `φ` of the qutrit `Q_ℓ ≅ H₃(ℂ)` of
The ternary grading theorem (v). The re-cut system replaces the four frames of `ℓ` by their images
under `φ` and keeps the other nine.
(i) Every re-cut system is a thirteen-plane system.
(ii) A re-cut system has exactly 52 positive shares if and only if `φ` permutes the four planes
`P_p`, `p ∈ ℓ`. Every other re-cut system is not the image of the graded system under an
automorphism of `J`.

Carriers: `J = Glennie.Albert` with `Glennie.jordan`, `Glennie.trace`, `Glennie.inner`; frames are
`Glennie.Frame`; `V = NativeTraceless` with the cubic `nativeEqualCubic`; shares are the
accepted projection shares `planeShare`/`positivePlaneTriples` of a `TightNativeCode` (thirteen
pairwise unbiased frames). The definitions of a ternary grading group, its character spaces, the
graded frames, the planes `P_p = J ∩ (A_g ⊕ A_{-g})` and the qutrits `Q_ℓ` agree with the corresponding objects in the grading model. -/

namespace ThirteenPlanes.AlbertGrading.Recut

open JC ThirteenPlanes.RoundCubics

noncomputable section

/-- An automorphism of `J`: a real-linear bijection preserving the Jordan product. -/
def IsJordanAutomorphism (φ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert) : Prop :=
  ∀ x y, φ (Glennie.jordan x y) = Glennie.jordan (φ x) (φ y)

/-- An action of `G = 𝔽₃³` on `J` by real-linear bijections. -/
abbrev TernaryAction := Multiplicative Charge →* (Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)

/-- The complex-linear extension of `ρ(s)` to `J_ℂ`. -/
def act (ρ : TernaryAction) (s : Charge) : JC →ₗ[ℂ] JC :=
  mapC (ρ (Multiplicative.ofAdd s)).toLinearMap

/-- The character `g` of `G`, evaluated at `s`: `ω^{s·g}`. -/
def gradeCharacter (s g : Charge) : ℂ := chargePhase (chargeDot s g)

/-- The character space `A_g ⊂ J_ℂ`. -/
def charSpace (ρ : TernaryAction) (g : Charge) : Submodule ℂ JC where
  carrier := {z | ∀ s, act ρ s z = gradeCharacter s g • z}
  add_mem' {z w} hz hw s := by
    rw [map_add, hz s, hw s, smul_add]
  zero_mem' s := by rw [map_zero, smul_zero]
  smul_mem' c z hz s := by
    rw [map_smul, hz s, smul_comm]

/-- A ternary grading group of `J`: `ρ` is injective, takes values in `Aut(J)`, and every one of the
27 characters has a one-dimensional eigenspace on `J_ℂ`. -/
structure IsTernaryGrading (ρ : TernaryAction) : Prop where
  injective : Function.Injective ρ
  automorphism : ∀ s, IsJordanAutomorphism (ρ s)
  lineDim : ∀ g, Module.finrank ℂ (charSpace ρ g) = 1

/-- The normalization `u ∘ u = ū`, `u ∘ ū = e`. -/
def IsNormalized (u : JC) : Prop := mul u u = conj u ∧ mul u (conj u) = one

/-- Outcomes `a ∈ 𝔽₃`, written `Fin 3` for the frame index. -/
def outcome (a : Fin 3) : ZMod 3 := a

/-- `p_a = ⅓(e + ω^{-a} u + ω^a ū)`. -/
def framePoint (u : JC) (a : Fin 3) : JC :=
  (1 / 3 : ℂ) • (one + chargePhase (-(outcome a)) • u + chargePhase (outcome a) • conj u)

/-- `p` is the ordered frame of `J` with points `p_a = ⅓(e + ω^{-a} u + ω^a ū)`. -/
def IsFrameOf (u : JC) (p : Fin 3 → Glennie.Albert) : Prop :=
  Glennie.Frame p ∧ ∀ a, of (p a) = framePoint u a

/-- `J ∩ (A_g ⊕ A_{-g})`. -/
def gradedPlaneJ (ρ : TernaryAction) (g : Charge) : Submodule ℝ Glennie.Albert :=
  ((charSpace ρ g ⊔ charSpace ρ (-g)).restrictScalars ℝ).comap ofLinear

/-- The same space viewed inside `V`. -/
def gradedPlane (ρ : TernaryAction) (g : Charge) : Submodule ℝ NativeTraceless :=
  (gradedPlaneJ ρ g).comap Glennie.traceLinear.ker.subtype

/-- The plane `P_p` of a point `p = {g,-g}`. -/
def pointPlane (ρ : TernaryAction) (p : SignedPlaneIndex) : Submodule ℝ NativeTraceless :=
  gradedPlane ρ p.val.val

/-- `Q_ℓ = ℝ e ⊕ ⨁_{p ∈ ℓ} P_p`. -/
def lineAlgebraOf (ρ : TernaryAction) (l : SignedPlaneIndex) : Submodule ℝ Glennie.Albert :=
  Submodule.span ℝ ({1} ∪ ⋃ (p : SignedPlaneIndex) (_ : signedPointOnLine p l),
    (gradedPlaneJ ρ p.val.val : Set Glennie.Albert))

/-! Graded-system facts used in the line-rotation theorem. -/

/-- The clauses of the ternary grading theorem used here, from `Targets.GradedSystem`:
(ii) the frame of a normalized `u ∈ A_g` has plane `P_p` and `P_p` is traceless, (iii) the graded
frames are pairwise unbiased, (iv) the product space of two planes is the sum of the other two
planes of their line and the shares are the collinearity indicator, (v) `Q_ℓ` is closed under the
Jordan product. -/
def GradingData.GradedFacts : Prop :=
  ∀ ρ : TernaryAction, IsTernaryGrading ρ →
    (∀ g : Charge, g ≠ 0 → ∀ u ∈ charSpace ρ g, IsNormalized u →
      ∃ p : Fin 3 → Glennie.Albert, IsFrameOf u p ∧
        nativeFramePlane p = gradedPlane ρ g ∧ gradedPlaneJ ρ g ≤ Glennie.traceLinear.ker) ∧
    (∀ (u : Charge → JC) (P : Charge → Fin 3 → Glennie.Albert),
      (∀ g, g ≠ 0 → u g ∈ charSpace ρ g ∧ IsNormalized (u g) ∧ IsFrameOf (u g) (P g)) →
      ∀ g h, g ≠ 0 → h ≠ 0 → h ≠ g → h ≠ -g → ∀ a b, Glennie.inner (P g a) (P h b) = 1 / 3) ∧
    (∀ p q r r' : SignedPlaneIndex, p ≠ q → r ≠ r' → r ≠ p → r ≠ q → r' ≠ p → r' ≠ q →
      signedCollinear p q r → signedCollinear p q r' →
      mixedProductSpace nativeEqualCubic (pointPlane ρ p) (pointPlane ρ q) =
        pointPlane ρ r ⊔ pointPlane ρ r') ∧
    (∀ p q r : SignedPlaneIndex, p ≠ q → p ≠ r → q ≠ r →
      shareOfThreePlanes nativeEqualCubic (pointPlane ρ p) (pointPlane ρ q) (pointPlane ρ r) =
        if signedCollinear p q r then 1 else 0) ∧
    (∀ l : SignedPlaneIndex, ∀ x y, x ∈ lineAlgebraOf ρ l → y ∈ lineAlgebraOf ρ l →
      Glennie.jordan x y ∈ lineAlgebraOf ρ l)

/-! ## Re-cut systems -/

/-- The plane of a frame `F`, as a subspace of `J`: the span of the centered idempotents
`F a - e/3`, i.e. the `nativeFramePlane F ⊂ V` viewed in `J`. -/
def planeA (F : Fin 3 → Glennie.Albert) : Submodule ℝ Glennie.Albert :=
  (nativeFramePlane F).map Glennie.traceLinear.ker.subtype

/-- `φ` is an automorphism of the subalgebra `Q`: it preserves the Jordan product of `J`
restricted to `Q`. -/
def IsSubalgebraAutomorphism (Q : Submodule ℝ Glennie.Albert) (φ : Q ≃ₗ[ℝ] Q) : Prop :=
  ∀ (x y : Q) (h : Glennie.jordan (x : Glennie.Albert) y ∈ Q),
    (φ ⟨_, h⟩ : Glennie.Albert) = Glennie.jordan (φ x : Glennie.Albert) (φ y)

/-- `φ` applied to elements of `Q`, and the identity elsewhere (used only on `Q`). -/
def extendOn (Q : Submodule ℝ Glennie.Albert) (φ : Q ≃ₗ[ℝ] Q) (x : Glennie.Albert) :
    Glennie.Albert :=
  haveI := Classical.propDecidable (x ∈ Q)
  if h : x ∈ Q then (φ ⟨x, h⟩ : Glennie.Albert) else x

/-- The re-cut system: the frames of the points of `ℓ` are replaced by their images under `φ`, the
other nine graded frames are kept. The graded frame of a point `p` is `P` at its representative. -/
def recutFrame (ρ : TernaryAction) (l : SignedPlaneIndex)
    (φ : lineAlgebraOf ρ l ≃ₗ[ℝ] lineAlgebraOf ρ l) (P : Charge → Fin 3 → Glennie.Albert)
    (p : SignedPlaneIndex) (a : Fin 3) : Glennie.Albert :=
  if signedPointOnLine p l then extendOn (lineAlgebraOf ρ l) φ (P p.val.val a) else P p.val.val a

/-- `φ` permutes the four planes `P_p`, `p ∈ ℓ`: some permutation `σ` of the points of `ℓ` has
`φ(P_p) = P_{σ p}` for every `p ∈ ℓ`. -/
def PermutesLinePlanes (ρ : TernaryAction) (l : SignedPlaneIndex)
    (φ : lineAlgebraOf ρ l ≃ₗ[ℝ] lineAlgebraOf ρ l) : Prop :=
  ∃ σ : {p : SignedPlaneIndex // signedPointOnLine p l} ≃
      {p : SignedPlaneIndex // signedPointOnLine p l},
    ∀ p x, x ∈ gradedPlaneJ ρ (σ p).val.val.val ↔
      ∃ y : lineAlgebraOf ρ l, (y : Glennie.Albert) ∈ gradedPlaneJ ρ p.val.val.val ∧
        (φ y : Glennie.Albert) = x

/-- The automorphism `ψ` of `J` carries the graded system onto the re-cut system `R`: the image
of the plane of every graded frame is the plane of some re-cut frame. (Carrying frames to frames
up to relabelling implies this, so its negation below is the stronger statement.) -/
def CarriesGradedTo (ρ : TernaryAction) (ψ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (R : SignedPlaneIndex → Fin 3 → Glennie.Albert) : Prop :=
  ∀ p : SignedPlaneIndex, ∃ q : SignedPlaneIndex,
    ∀ x, x ∈ planeA (R q) ↔ ∃ y ∈ gradedPlaneJ ρ p.val.val, ψ y = x

/-- Rotation of four planes on a graded line, both clauses, for every ternary grading group, every choice of the
graded frames (normalized `u_g ∈ A_g` and their frames), every line and every automorphism of its
qutrit. -/
def Statements.OtherSystems : Prop :=
  ∀ ρ : TernaryAction, IsTernaryGrading ρ →
  ∀ (u : Charge → JC) (P : Charge → Fin 3 → Glennie.Albert),
    (∀ g, g ≠ 0 → u g ∈ charSpace ρ g ∧ IsNormalized (u g) ∧ IsFrameOf (u g) (P g)) →
  ∀ (l : SignedPlaneIndex) (φ : lineAlgebraOf ρ l ≃ₗ[ℝ] lineAlgebraOf ρ l),
    IsSubalgebraAutomorphism (lineAlgebraOf ρ l) φ →
    -- (i) thirteen pairwise unbiased frames (a `TightNativeCode` for every labelling)
    ((∀ p, Glennie.Frame (recutFrame ρ l φ P p)) ∧
      (∀ p q, p ≠ q → ∀ a b,
        Glennie.inner (recutFrame ρ l φ P p a) (recutFrame ρ l φ P q b) = 1 / 3) ∧
      (∀ e : Fin 13 ≃ SignedPlaneIndex, ∃ c : TightNativeCode,
        ∀ i, c.point i = recutFrame ρ l φ P (e i))) ∧
    -- (ii) first sentence
    (∀ (c : TightNativeCode) (e : Fin 13 ≃ SignedPlaneIndex),
      (∀ i, c.point i = recutFrame ρ l φ P (e i)) →
      ((positivePlaneTriples nativeEqualCubic c.decomposition).card = 52 ↔
        PermutesLinePlanes ρ l φ)) ∧
    -- (ii) second sentence
    (¬ PermutesLinePlanes ρ l φ →
      ¬ ∃ ψ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert, IsJordanAutomorphism ψ ∧
        CarriesGradedTo ρ ψ (recutFrame ρ l φ P))

end

end ThirteenPlanes.AlbertGrading.Recut
