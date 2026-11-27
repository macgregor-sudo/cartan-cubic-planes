module

public import Glennie.Native.Triality
public import Glennie.Diagonalization
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

/-!
# Related octonion maps in the cyclic Albert slots

Yokota's slots in §2.1 carry the entries (23), (31), and (12), in one-based
indices. In the upper-triangular native carrier these are `o12`,
`octConj o02`, and `o01`. The product condition in §1.16 and Theorem 2.7.1
conjugates the third slot map. A plain related triple consequently acts on
the cyclic slots by `g₁`, `g₂`, and `octConjMap g₃`.
-/

namespace ThirteenPlanes.AlbertTriality

open Glennie

noncomputable section

abbrev OctEquiv := Octonion ≃ₗ[ℝ] Octonion

def OctOrtho (g : OctEquiv) : Prop :=
  ∀ x, octNormSq (g x) = octNormSq x

def Related (g₁ g₂ g₃ : OctEquiv) : Prop :=
  ∀ x y, octMul (g₁ x) (g₂ y) = g₃ (octMul x y)

/-- Conjugation of a linear map by native octonion conjugation. -/
def octConjMap (g : OctEquiv) : OctEquiv :=
  octConjEquiv.trans (g.trans octConjEquiv)

@[simp] theorem octConjMap_apply (g : OctEquiv) (x : Octonion) :
    octConjMap g x = octConj (g (octConj x)) := rfl

@[simp] theorem octConjMap_involutive (g : OctEquiv) : octConjMap (octConjMap g) = g := by
  apply LinearEquiv.ext
  intro x
  simp only [octConjMap_apply, octConj_conj]

theorem octConjMap_ortho {g : OctEquiv} (h : OctOrtho g) : OctOrtho (octConjMap g) := by
  intro x
  rw [octConjMap_apply, octNormSq_conj, h, octNormSq_conj]

theorem octConjMap_det (g : OctEquiv) :
    LinearMap.det (octConjMap g).toLinearMap = LinearMap.det g.toLinearMap := by
  have hsymm : octConjEquiv.symm = octConjEquiv := by
    apply LinearEquiv.ext
    intro x
    rfl
  have h := LinearEquiv.det_conj g octConjEquiv
  rw [hsymm, LinearEquiv.trans_assoc] at h
  simpa only [LinearEquiv.coe_det, octConjMap] using (congrArg (fun u : ℝˣ => (u : ℝ)) h)

/-- Cyclically permute the maps in the Yokota slot convention, then express
the resulting product identity in the plain related-triple convention. -/
def cyclicRelated (g : OctRelatedTriple) : OctRelatedTriple where
  A := octConjMap g.C
  B := g.A
  C := octConjMap g.B
  norm_A := octConjMap_ortho g.norm_C
  norm_B := g.norm_A
  norm_C := octConjMap_ortho g.norm_B
  product x y := by
    have h := congrArg octConj (g.cross12 y (octConj x))
    simpa only [octConjMap_apply, octConj_mul, octConj_conj] using h

/-- The native Jordan automorphism for a related triple in the cyclic slot convention. -/
def relatedToCompactAuto (g₁ g₂ g₃ : OctEquiv) (h₁ : OctOrtho g₁)
    (h₂ : OctOrtho g₂) (h₃ : OctOrtho g₃) (h : Related g₁ g₂ g₃) :
    CompactAutomorphism :=
  (cyclicRelated ⟨g₁, g₂, g₃, h₁, h₂, h₃, h⟩).compactAutomorphism

theorem relatedToCompactAuto_apply (g₁ g₂ g₃ : OctEquiv) (h₁ : OctOrtho g₁)
    (h₂ : OctOrtho g₂) (h₃ : OctOrtho g₃) (h : Related g₁ g₂ g₃) (x : Albert) :
    (relatedToCompactAuto g₁ g₂ g₃ h₁ h₂ h₃ h).equiv x =
      ⟨x.d0, x.d1, x.d2, octConjMap g₃ x.o01, octConjMap g₂ x.o02, g₁ x.o12⟩ := rfl

theorem relatedToCompactAuto_fixes_frame (g₁ g₂ g₃ : OctEquiv) (h₁ : OctOrtho g₁)
    (h₂ : OctOrtho g₂) (h₃ : OctOrtho g₃) (h : Related g₁ g₂ g₃) (i : Fin 3) :
    (relatedToCompactAuto g₁ g₂ g₃ h₁ h₂ h₃ h).equiv (standardFrame i) =
      standardFrame i := by
  rw [relatedToCompactAuto_apply]
  fin_cases i <;> simp [standardFrame, -octConjMap_apply]

/-- The direct action is realized by the three identity maps. -/
theorem related_identity :
    Related (LinearEquiv.refl ℝ Octonion) (LinearEquiv.refl ℝ Octonion)
      (LinearEquiv.refl ℝ Octonion) := fun _ _ => rfl

end
end ThirteenPlanes.AlbertTriality
