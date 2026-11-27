module

public import ThirteenPlanes.RoundContractions
public import ThirteenPlanes.PlaneContractions

@[expose] public section

/-! Compatibility names for round plane geometry used by the pencil flow. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.PencilFlow.Pencil

noncomputable section

open SymmetricCubic PlaneContractions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {h : SymmetricCubic V} {c : ℝ}

/-- A round cubic is `√(6c)` times a cubic with the normalized square law. -/
theorem normalize (round : IsRound h c) :
    ∃ (s : ℝ) (g : SymmetricCubic V), s ^ 2 = 6 * c ∧ 0 < s ∧ h = s • g ∧ HasSquareLaw g := by
  let s := Real.sqrt (6 * c)
  have hc := round.positive
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 6 * c := Real.sq_sqrt (by positivity)
  refine ⟨s, s⁻¹ • h, hs2, hs, ?_, ?_⟩
  · rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  · intro x
    have hscale : s⁻¹ ^ 2 * c = 1 / 6 := by
      rw [inv_pow, hs2]
      field_simp
    rw [SymmetricCubic.squareMap_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hs.le), mul_pow, round.square_norm, ← mul_assoc, hscale]
    ring

theorem polarized (round : IsRound h c) (x y z w : V) :
    ⟪h.L x y, h.L z w⟫ + ⟪h.L x z, h.L y w⟫ + ⟪h.L x w, h.L y z⟫ =
      c * (⟪x, y⟫ * ⟪z, w⟫ + ⟪x, z⟫ * ⟪y, w⟫ + ⟪x, w⟫ * ⟪y, z⟫) :=
  RoundCubics.polarized round x y z w

/-- The basis-index form of the polarized round identity. -/
theorem polarized_coefficients (round : IsRound h c) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ V) (i j k l : ι) :
    Quartic.sq4 (h.coefficient e) i j k l = c * Quartic.piT i j k l :=
  RoundCubics.polarized_coefficients round e i j k l

variable [FiniteDimensional ℝ V]

/-- A round cubic in dimension two is harmonic. -/
theorem traceFree_of_round_finrank_two (round : IsRound h c) (hdim : Module.finrank ℝ V = 2) :
    h.TraceFree :=
  RoundCubics.traceFree_of_round_finrank_two round hdim

variable {ι : Type*} {planes : PlaneDecomposition V ι}

/-- Closed plane restrictions inherit the round identity at the same strength. -/
theorem restriction_isRound (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (i : ι) : IsRound (planes.restriction i h) c :=
  RoundCubics.restriction_isRound round closed i

variable [Fintype ι]

/-- The intrinsic pencil of a closed round plane system has the geometric plane data. -/
theorem planePencil_hasPlaneData (round : IsRound h c) (closed : IsClosedPlaneSystem h planes) :
    HasPlaneData (planePencil h planes) planes :=
  RoundCubics.planePencil_hasPlaneData round closed

end

end ThirteenPlanes.PencilFlow.Pencil
