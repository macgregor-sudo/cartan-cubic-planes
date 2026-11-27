module

public import ThirteenPlanes.PencilFlow.Pencil.RoundPlanes
public import ThirteenPlanes.PencilFlow.TensorStatements

@[expose] public section

/-! The one-loop invariance of the pencil, first half: the double and triangle contractions on the
intrinsic pencil of a round cubic with a closed plane system, at arbitrary strength `c`.

Route: rescale `h = s • g` with `s² = 6c`, so that `g` has the normalized square law for the normalized model; apply the plane theorem `planeContractionLaws` to the pencil of `g`; and
transport the laws back through `planePencil h = s • planePencil g`. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.PencilFlow.Pencil

noncomputable section

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem pullback_smul (s : ℝ) (g : SymmetricCubic V) (f : V →ₗ[ℝ] V) :
    (s • g).pullback f = s • g.pullback f := by
  apply SymmetricCubic.ext
  intro x y z
  simp only [pullback_apply, apply_smul]

theorem planePencil_smul {ι : Type*} [Fintype ι] (s : ℝ) (g : SymmetricCubic V)
    (planes : PlaneDecomposition V ι) :
    (planePencil (s • g) planes).diagonalCubic = s • (planePencil g planes).diagonalCubic ∧
      (planePencil (s • g) planes).mixingCubic = s • (planePencil g planes).mixingCubic := by
  have hd : (planePencil (s • g) planes).diagonalCubic =
      s • (planePencil g planes).diagonalCubic := by
    simp only [planePencil, pullback_smul, Finset.smul_sum]
  refine ⟨hd, ?_⟩
  change s • g - (planePencil (s • g) planes).diagonalCubic =
    s • (g - (planePencil g planes).diagonalCubic)
  rw [hd, smul_sub]

/-- The contraction laws of the actual pencil, in physical strength `c`. -/
theorem closedPencil_contractions {m : ℕ} (h : SymmetricCubic V) (c : ℝ)
    (planes : PlaneDecomposition V (Fin m)) (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) (a b : ℝ) :
    let lam := Statements.pencilLambda V
    let P := planePencil h planes
    let f := coupling P (a, b)
    f.doubleContraction =
        (2 * c * (a ^ 2 + 3 * lam * b ^ 2)) • (LinearMap.id : V →ₗ[ℝ] V) ∧
      f.triangleContraction = (-3 * c * lam * b ^ 3) • P.diagonalCubic +
        (-3 * c * b ^ 2 * (a - b + lam * b)) • P.mixingCubic := by
  intro lam P f
  obtain ⟨s, g, hs2, hs, hh, law⟩ := normalize round
  have closedg : IsClosedPlaneSystem g planes := by
    intro i x y hx hy
    have hp := closed i hx hy
    rw [hh, map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at hp
    have hn := (planes.plane i).smul_mem s⁻¹ hp
    rwa [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at hn
  have roundg : IsRound g (1 / 6) := by
    refine ⟨by norm_num, fun x => ?_⟩
    rw [law x]
    ring
  have data := planePencil_hasPlaneData roundg closedg
  have lawg : HasSquareLaw (interactionCubic (planePencil g planes) 1) := by
    rw [planePencil_at_one]
    exact law
  have laws := planeContractionLaws (planePencil g planes) planes data lawg
  have hlam : ((Module.finrank ℝ V : ℝ) - 2) / 12 = lam := rfl
  rw [hlam] at laws
  obtain ⟨hD, hM⟩ := planePencil_smul s g planes
  have hP : P.diagonalCubic = s • (planePencil g planes).diagonalCubic := by
    simp only [P, hh, hD]
  have hPM : P.mixingCubic = s • (planePencil g planes).mixingCubic := by
    simp only [P, hh, hM]
  have hf : f = coupling (planePencil g planes) (s * a, s * b) := by
    simp only [f, coupling_apply, hP, hPM, smul_smul, mul_comm a s, mul_comm b s]
  rw [hf, laws.double, laws.triangle, hP, hPM]
  refine ⟨?_, ?_⟩
  · congr 1
    simp only [familyM]
    linear_combination (a ^ 2 / 3 + lam * b ^ 2) * hs2
  · simp only [coupling_apply, familyP, familyQ, smul_smul]
    congr 2
    · linear_combination (-lam * s * b ^ 3 / 2) * hs2
    · linear_combination (s * ((1 - lam) * b ^ 3 - a * b ^ 2) / 2) * hs2

end

end ThirteenPlanes.PencilFlow.Pencil

namespace ThirteenPlanes.PencilFlow.Proofs

open Statements

/-- The one-loop invariance of the pencil, the two contraction formulas. -/
theorem pencilContractions (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.PencilContractions V := by
  intro m _ h c planes round closed a b
  exact Pencil.closedPencil_contractions h c planes round closed a b

end ThirteenPlanes.PencilFlow.Proofs
