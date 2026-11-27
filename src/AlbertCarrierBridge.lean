/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ExceptionalDefs
public import ThirteenPlanes.NativeFrames

@[expose] public section

set_option backward.privateInPublic true

noncomputable section

namespace Challenge

/-- The same real diagonal and upper entries in the independently defined and native carriers. -/
def glennieAlbertEquiv : Hermitian3 ≃ₗ[ℝ] Glennie.Albert where
  toFun x := ⟨x.1 0, x.1 1, x.1 2, x.2 0, x.2 1, x.2 2⟩
  invFun x := (![x.d0, x.d1, x.d2], ![x.o01, x.o02, x.o12])
  left_inv x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv x := by cases x; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem glennieAlbertEquiv_one : glennieAlbertEquiv hermitianOne = 1 := rfl

private theorem glennieAlbertEquiv_matrix (x : Hermitian3) :
    Glennie.toMatrix (glennieAlbertEquiv x) = hermitianMatrix x := rfl

private theorem glennie_matrixMul_eq (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    Glennie.matrixMul A B = octMatrixMul A B := rfl

private theorem glennie_fromMatrix_eq (A : Matrix (Fin 3) (Fin 3) Octonion) :
    glennieAlbertEquiv ((fun i => (A i i).1.re), ![A 0 1, A 0 2, A 1 2]) =
      Glennie.fromMatrix A := rfl

@[simp] theorem glennieAlbertEquiv_jordan (x y : Hermitian3) :
    glennieAlbertEquiv (jordanMul x y) =
      Glennie.jordan (glennieAlbertEquiv x) (glennieAlbertEquiv y) := by
  unfold jordanMul Glennie.jordan
  rw [glennieAlbertEquiv_matrix, glennieAlbertEquiv_matrix,
    glennie_matrixMul_eq, glennie_matrixMul_eq]
  exact glennie_fromMatrix_eq _

@[simp] theorem glennieAlbertEquiv_trace (x : Hermitian3) :
    Glennie.trace (glennieAlbertEquiv x) = jordanTrace x := by
  simp only [jordanTrace, Fin.sum_univ_three, Glennie.trace]
  rfl

/-- The coordinate equivalence restricted to the trace kernels. -/
def glennieTracelessEquiv : TracelessHermitian3 ≃ₗ[ℝ] ThirteenPlanes.NativeTraceless where
  toFun x := ⟨glennieAlbertEquiv x, by
    change Glennie.trace (glennieAlbertEquiv x) = 0
    rw [glennieAlbertEquiv_trace]
    exact x.property⟩
  invFun x := ⟨glennieAlbertEquiv.symm x, by
    change jordanTrace (glennieAlbertEquiv.symm x) = 0
    rw [← glennieAlbertEquiv_trace, glennieAlbertEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext (glennieAlbertEquiv.symm_apply_apply x)
  right_inv x := Subtype.ext (glennieAlbertEquiv.apply_symm_apply x)
  map_add' x y := Subtype.ext (glennieAlbertEquiv.map_add x y)
  map_smul' r x := Subtype.ext (glennieAlbertEquiv.map_smul r x)

@[simp] theorem glennieTracelessEquiv_apply (x : TracelessHermitian3) :
    (glennieTracelessEquiv x : Glennie.Albert) = glennieAlbertEquiv x := rfl

theorem albertFrame_iff_glennieFrame (p : Fin 3 → Hermitian3) :
    AlbertFrame p ↔ Glennie.Frame (fun a => glennieAlbertEquiv (p a)) := by
  constructor
  · intro h
    refine ⟨fun a => by rw [glennieAlbertEquiv_trace, h.trace_one], ?_, ?_, ?_⟩
    · intro a
      rw [← glennieAlbertEquiv_jordan, h.idempotent]
    · intro a b hab
      rw [← glennieAlbertEquiv_jordan, h.orthogonal a b hab, map_zero]
    · simpa only [Fin.sum_univ_three, map_add, glennieAlbertEquiv_one, add_assoc] using
        congrArg glennieAlbertEquiv h.sum_unit
  · intro h
    refine ⟨fun a => (glennieAlbertEquiv_trace (p a)).symm.trans (h.trace_one a), ?_, ?_, ?_⟩
    · intro a
      exact glennieAlbertEquiv.injective ((glennieAlbertEquiv_jordan _ _).trans (h.idempotent a))
    · intro a b hab
      apply glennieAlbertEquiv.injective
      rw [map_zero, glennieAlbertEquiv_jordan]
      exact h.orthogonal a b hab
    · apply glennieAlbertEquiv.injective
      simpa only [Fin.sum_univ_three, map_add, glennieAlbertEquiv_one, add_assoc] using h.sum_unit

theorem albertUnbiased_iff_inner (p q : Fin 3 → Hermitian3) :
    AlbertUnbiased p q ↔ ∀ a b,
      Glennie.inner (glennieAlbertEquiv (p a)) (glennieAlbertEquiv (q b)) = 1 / 3 := by
  simp only [AlbertUnbiased, Glennie.inner, ← glennieAlbertEquiv_jordan, glennieAlbertEquiv_trace]

end Challenge
