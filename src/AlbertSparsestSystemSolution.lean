/- SPDX-License-Identifier: Apache-2.0 -/

module

public import AlbertSparsestOrbitAdapter
public import ThirteenPlanes.AlbertGrading.Recognition.NativePairNormalization

@[expose] public section

/-! The sharp thirteen-frame Albert support theorem in the independent Challenge coordinates. -/

namespace Challenge

/-- A thirteen-frame system with exactly 52 positive shares exists, and any two such systems are
related by a unital Albert automorphism, up to relabelling the frames and their outcomes. -/
theorem albertSparsestSystem :
    (∃ F : Fin 13 → Fin 3 → Hermitian3, SparseAlbertSystem F) ∧
    (∀ F G : Fin 13 → Fin 3 → Hermitian3, SparseAlbertSystem F → SparseAlbertSystem G →
      ∃ (φ : Hermitian3 ≃ₗ[ℝ] Hermitian3) (σ : Equiv.Perm (Fin 13))
        (τ : Fin 13 → Equiv.Perm (Fin 3)),
        φ hermitianOne = hermitianOne ∧
        (∀ x y, φ (jordanMul x y) = jordanMul (φ x) (φ y)) ∧
        ∀ i a, φ (F i a) = G (σ i) (τ i a)) :=
  albertSparsestSystem_of_native ThirteenPlanes.AlbertGrading.nativeSparsest

end Challenge
