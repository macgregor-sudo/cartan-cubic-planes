module

public import ThirteenPlanes.NativeFrames
public import ThirteenPlanes.Basic

@[expose] public section

/-! Unique completion of twelve unbiased Albert frames, or of twelve orthogonal closed planes.

Frames are ordered trace-one orthogonal idempotents summing to the unit in `Glennie.Albert`.
The metric is the trace form `Glennie.inner x y = tr (x ∘ y)`. On `NativeTraceless`,
`nativeEqualCubic` uses the centered product `x * y = x ∘ y - ⅓⟨x,y⟩e`.
Uniqueness of the missing frame is up to the ordering of its atoms. -/

namespace ThirteenPlanes.AlbertGrading

open ThirteenPlanes

/-- Two frames are unbiased: all nine overlaps `tr (p a ∘ q b)` equal `1/3`. -/
def NativeUnbiased (p q : Fin 3 → Glennie.Albert) : Prop :=
  ∀ a b, Glennie.inner (p a) (q b) = 1 / 3

/-- A thirteen-plane system: a set of thirteen pairwise orthogonal closed planes of `H₀(𝕆)`. -/
def IsThirteenPlaneSystem (S : Set (Submodule ℝ NativeTraceless)) : Prop :=
  ∃ Q : Fin 13 → Submodule ℝ NativeTraceless, Set.range Q = S ∧
    (∀ k, Module.finrank ℝ (Q k) = 2) ∧ (∀ k, IsClosedPiece nativeEqualCubic (Q k)) ∧
    Pairwise fun k l => (Q k).IsOrtho (Q l)

/-- First sentence: twelve pairwise unbiased frames have a frame unbiased to all twelve, and any two
such frames are the same unordered triple of idempotents. -/
def Statements.CompletionOFrames : Prop :=
  ∀ F : Fin 12 → Fin 3 → Glennie.Albert, (∀ i, Glennie.Frame (F i)) →
    Pairwise (fun i j => NativeUnbiased (F i) (F j)) →
    ∃ q : Fin 3 → Glennie.Albert, Glennie.Frame q ∧ (∀ i, NativeUnbiased (F i) q) ∧
      ∀ q' : Fin 3 → Glennie.Albert, Glennie.Frame q' → (∀ i, NativeUnbiased (F i) q') →
        Set.range q' = Set.range q

/-- Second sentence: twelve pairwise orthogonal closed planes lie in exactly one thirteen-plane
system. -/
def Statements.CompletionOPlanes : Prop :=
  ∀ P : Fin 12 → Submodule ℝ NativeTraceless, (∀ i, Module.finrank ℝ (P i) = 2) →
    (∀ i, IsClosedPiece nativeEqualCubic (P i)) → Pairwise (fun i j => (P i).IsOrtho (P j)) →
    ∃! S : Set (Submodule ℝ NativeTraceless), IsThirteenPlaneSystem S ∧ Set.range P ⊆ S

/-- Completion of twelve Albert frames, both sentences. -/
def Statements.CompletionO : Prop := Statements.CompletionOFrames ∧ Statements.CompletionOPlanes

end ThirteenPlanes.AlbertGrading
