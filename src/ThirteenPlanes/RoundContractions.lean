module

public import ThirteenPlanes.RoundIdentities
public import ThirteenPlanes.Quartic.Defs
public import ThirteenPlanes.PlaneContractions.Identities
public import ThirteenPlanes.FourPlanesPlaneData

@[expose] public section

set_option backward.privateInPublic true

/-! The contractions of harmonic round cubics in Lemma 8-contractions. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes.RoundCubics

noncomputable section

open SymmetricCubic PlaneContractions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {h : SymmetricCubic V} {c : ℝ}

/-- The basis-index form of the polarized round identity. -/
theorem polarized_coefficients (round : IsRound h c) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ V) (i j k l : ι) :
    Quartic.sq4 (h.coefficient e) i j k l = c * Quartic.piT i j k l := by
  have term (a b p q : ι) : (∑ r, h.coefficient e a b r * h.coefficient e p q r) =
      ⟪h.L (e a) (e b), h.L (e p) (e q)⟫ :=
    sum_inner_mul_inner' e _ _
  unfold Quartic.sq4 Quartic.piT Quartic.dlt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, term, term, term]
  simpa only [OrthonormalBasis.inner_eq_ite] using polarized round (e i) (e j) (e k) (e l)

private theorem normalized (round : IsRound h c) :
    ∃ (s : ℝ) (g : SymmetricCubic V), s ^ 2 = 6 * c ∧ s ≠ 0 ∧ h = s • g ∧ HasSquareLaw g := by
  let s := Real.sqrt (6 * c)
  have hc := round.positive
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 6 * c := Real.sq_sqrt (by positivity)
  refine ⟨s, s⁻¹ • h, hs2, hs.ne', ?_, ?_⟩
  · rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  · intro x
    have hscale : s⁻¹ ^ 2 * c = 1 / 6 := by
      rw [inv_pow, hs2]
      field_simp
    rw [squareMap_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hs.le), mul_pow, round.square_norm, ← mul_assoc, hscale]
    ring

private theorem slice_smul (s : ℝ) (g : SymmetricCubic V) (x : V) :
    (s • g).L x = s • g.L x := by
  simp only [map_smul, LinearMap.smul_apply]

private theorem traceFree_of_smul (s : ℝ) (hs : s ≠ 0) (g : SymmetricCubic V)
    (tf : (s • g).TraceFree) : g.TraceFree := by
  intro x
  have hx := tf x
  rw [slice_smul, map_smul, smul_eq_mul, mul_eq_zero] at hx
  exact hx.resolve_left hs

variable [FiniteDimensional ℝ V]

/-- The double contraction of a harmonic round cubic is `c (N + 2) / 2` times the identity. -/
theorem doubleContraction_of_round (round : IsRound h c) (tf : h.TraceFree) :
    h.doubleContraction =
      (c * ((Module.finrank ℝ V : ℝ) + 2) / 2) • (LinearMap.id : V →ₗ[ℝ] V) := by
  obtain ⟨s, g, hs2, hs, hh, law⟩ := normalized round
  have tg := traceFree_of_smul s hs g (hh ▸ tf)
  subst h
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [inner_doubleContraction, slice_smul, slice_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
    ← pow_two, map_smul, smul_eq_mul, trace_mul_of_squareLaw law tg, hs2,
    LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_left]
  ring

/-- The triangle contraction of a harmonic round cubic is `-c (N - 2) / 4` times the cubic. -/
theorem triangleContraction_of_round (round : IsRound h c) (tf : h.TraceFree) :
    h.triangleContraction =
      (-(c * ((Module.finrank ℝ V : ℝ) - 2) / 4)) • h := by
  obtain ⟨s, g, hs2, hs, hh, law⟩ := normalized round
  have tg := traceFree_of_smul s hs g (hh ▸ tf)
  have tri := triangleContraction_of_squareLaw law tg
  subst h
  apply SymmetricCubic.ext
  intro x y z
  have ht := congrArg (fun u : SymmetricCubic V => u.apply x y z) tri
  change g.triangleContraction.apply x y z = _ at ht
  rw [apply_triangleContraction, apply_smul] at ht
  rw [apply_triangleContraction, apply_smul, apply_smul]
  change LinearMap.trace ℝ V ((s • g.L x) * (s • g.L y) * (s • g.L z)) = _
  calc
    _ = s ^ 2 * (s * LinearMap.trace ℝ V (g.L x * g.L y * g.L z)) := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, map_smul, smul_eq_mul]
      ring
    _ = _ := by rw [hs2, ht]; ring


/-- A round cubic in dimension two is harmonic. -/
theorem traceFree_of_round_finrank_two (round : IsRound h c) (hdim : Module.finrank ℝ V = 2) :
    h.TraceFree := by
  let e := (stdOrthonormalBasis ℝ V).reindex (finCongr hdim)
  let a := h.coefficient e 0 0 0
  let b := h.coefficient e 0 0 1
  let d := h.coefficient e 0 1 1
  let f := h.coefficient e 1 1 1
  have hb₁ : h.coefficient e 0 1 0 = b := h.apply_swap₂₃ _ _ _
  have hb₂ : h.coefficient e 1 0 0 = b := (h.apply_swap₁₂ _ _ _).trans hb₁
  have hd₁ : h.coefficient e 1 0 1 = d := h.apply_swap₁₂ _ _ _
  have hd₂ : h.coefficient e 1 1 0 = d := (h.apply_swap₂₃ _ _ _).trans hd₁
  have h₁ := polarized_coefficients round e 0 0 0 0
  have h₂ := polarized_coefficients round e 1 1 1 1
  have h₃ := polarized_coefficients round e 0 0 0 1
  have h₄ := polarized_coefficients round e 0 1 1 1
  have h₅ := polarized_coefficients round e 0 0 1 1
  have ha : h.coefficient e 0 0 0 = a := rfl
  have hb : h.coefficient e 0 0 1 = b := rfl
  have hd : h.coefficient e 0 1 1 = d := rfl
  have hf : h.coefficient e 1 1 1 = f := rfl
  norm_num [Quartic.sq4, Quartic.piT, Quartic.dlt, Fin.sum_univ_two,
    ha, hb, hd, hf, hb₁, hb₂, hd₁, hd₂] at h₁ h₂ h₃ h₄ h₅
  have hba : b * (a + d) = 0 := by nlinarith only [h₃]
  have hdf : d * (b + f) = 0 := by nlinarith only [h₄]
  have htr : a + d = 0 ∧ b + f = 0 := by
    by_cases hb0 : b = 0
    · by_cases hd0 : d = 0
      · simp [hb0, hd0] at h₅
        exact (round.positive.ne' h₅.symm).elim
      · have hf0 := (mul_eq_zero.mp hdf).resolve_left hd0
        have hf0' : f = 0 := by simpa [hb0] using hf0
        refine ⟨(mul_eq_zero.mp ?_).resolve_left hd0, hf0⟩
        simp [hb0, hf0'] at h₂ h₅
        show d * (a + d) = 0
        nlinarith only [h₂, h₅]
    · have ha0 := (mul_eq_zero.mp hba).resolve_left hb0
      by_cases hd0 : d = 0
      · have ha0' : a = 0 := by simpa [hd0] using ha0
        refine ⟨ha0, (mul_eq_zero.mp ?_).resolve_left hb0⟩
        simp [hd0, ha0'] at h₁ h₅
        show b * (b + f) = 0
        nlinarith only [h₁, h₅]
      · exact ⟨ha0, (mul_eq_zero.mp hdf).resolve_left hd0⟩
  have hbase (i : Fin 2) : ∑ j, h.apply (e i) (e j) (e j) = 0 := by
    fin_cases i
    · change (∑ j, h.coefficient e 0 j j) = 0
      rw [Fin.sum_univ_two, ha, hd]
      exact htr.1
    · change (∑ j, h.coefficient e 1 j j) = 0
      rw [Fin.sum_univ_two, hb₂, hf]
      exact htr.2
  intro x
  rw [← sum_apply_diag e]
  have hexpand (j : Fin 2) :
      h.apply x (e j) (e j) = ∑ i, ⟪e i, x⟫ * h.apply (e i) (e j) (e j) := by
    conv_lhs => rw [← e.sum_repr' x]
    simp only [SymmetricCubic.apply, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, real_inner_smul_left, sum_inner]
  simp only [hexpand]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hbase, mul_zero, Finset.sum_const_zero]

variable {ι : Type*} {planes : PlaneDecomposition V ι}

/-- Closed plane restrictions inherit the round identity at the same strength. -/
theorem restriction_isRound (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (i : ι) : IsRound (planes.restriction i h) c := by
  refine ⟨round.positive, fun x => ?_⟩
  let y : planes.plane i := ⟨h.L (x : V) (x : V), closed i x.property x.property⟩
  have hy : (planes.restriction i h).squareMap x = y := by
    apply ext_inner_right ℝ
    intro z
    change (planes.restriction i h).apply x x z = h.apply x x z
    exact planes.restriction_apply i h x x z
  rw [hy]
  exact round.square_norm (x : V)

variable [Fintype ι]

/-- The intrinsic pencil of a closed round plane system has the geometric plane data. -/
theorem planePencil_hasPlaneData (round : IsRound h c) (closed : IsClosedPlaneSystem h planes) :
    HasPlaneData (planePencil h planes) planes := by
  refine ⟨?_, ?_, ?_⟩
  · rw [planePencil_at_one]
    rfl
  · intro i
    rw [planePencil_at_one]
    exact traceFree_of_round_finrank_two (restriction_isRound round closed i) (planes.dimension i)
  · intro i x y z
    rw [planePencil_at_one]
    exact Submodule.inner_right_of_mem_orthogonal (closed i x.property y.property) z.property

/-- In a closed round plane system, the ambient cubic is harmonic. -/
theorem traceFree_of_isClosedPlaneSystem (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) : h.TraceFree := by
  have ht := traceFree_interaction (planePencil_hasPlaneData round closed)
  rwa [planePencil_at_one] at ht


/-- The diagonal cubic of a closed round plane system has double contraction `2c I`
and zero triangle contraction. -/
theorem planePencil_diagonal_contractions (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) :
    let D := (planePencil h planes).diagonalCubic
    D.doubleContraction = (2 * c) • (LinearMap.id : V →ₗ[ℝ] V) ∧
      D.triangleContraction = 0 := by
  obtain ⟨s, g, hs2, hs, hh, law⟩ := normalized round
  have closedg : IsClosedPlaneSystem g planes := by
    intro i x y hx hy
    have hp := closed i hx hy
    rw [hh, slice_smul, LinearMap.smul_apply] at hp
    have hn := (planes.plane i).smul_mem s⁻¹ hp
    rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at hn
  have roundg : IsRound g (1 / 6) := by
    refine ⟨by norm_num, fun x => ?_⟩
    rw [law x]
    ring
  have data := planePencil_hasPlaneData roundg closedg
  have lawg : HasSquareLaw (interactionCubic (planePencil g planes) 1) := by
    rw [planePencil_at_one]
    exact law
  let D := (planePencil g planes).diagonalCubic
  have hD : (planePencil h planes).diagonalCubic = s • D := by
    apply SymmetricCubic.ext
    intro x y z
    simp only [D, planePencil, apply_sum, pullback_apply, hh, apply_smul,
      Finset.mul_sum]
  change (planePencil h planes).diagonalCubic.doubleContraction = _ ∧
    (planePencil h planes).diagonalCubic.triangleContraction = _
  rw [hD]
  constructor
  · apply LinearMap.ext
    intro x
    apply ext_inner_right ℝ
    intro y
    rw [inner_doubleContraction, slice_smul, slice_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
      ← pow_two, map_smul, smul_eq_mul, hs2, LinearMap.smul_apply, LinearMap.id_apply,
      real_inner_smul_left]
    rw [show LinearMap.trace ℝ V (D.L x * D.L y) = _ from trace_diag_mul_diag data lawg x y]
    ring
  · apply SymmetricCubic.ext
    intro x y z
    rw [apply_triangleContraction, apply_zero]
    change LinearMap.trace ℝ V ((s • D.L x) * (s • D.L y) * (s • D.L z)) = _
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, map_smul, smul_eq_mul]
    rw [show LinearMap.trace ℝ V (D.L x * D.L y * D.L z) = 0 from
      trace_diag_diag_diag data lawg x y z, mul_zero]

end

end ThirteenPlanes.RoundCubics


namespace ThirteenPlanes.PencilEnergy

noncomputable section

open RoundCubics

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {h : SymmetricCubic V} {c : ℝ}

/-- Lemma 8-contractions, including the diagonal cubic of any closed round plane system. -/
theorem roundContractions (round : IsRound h c) (tf : h.TraceFree) :
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V) (i j k l : ι),
      Quartic.sq4 (h.coefficient e) i j k l = c * Quartic.piT i j k l) ∧
    h.doubleContraction =
      (c * ((Module.finrank ℝ V : ℝ) + 2) / 2) • (LinearMap.id : V →ₗ[ℝ] V) ∧
    h.triangleContraction = (-(c * ((Module.finrank ℝ V : ℝ) - 2) / 4)) • h ∧
    (∀ {ι : Type*} [Fintype ι] (planes : PlaneDecomposition V ι), IsClosedPlaneSystem h planes →
      let D := (planePencil h planes).diagonalCubic
      D.doubleContraction = (2 * c) • (LinearMap.id : V →ₗ[ℝ] V) ∧
        D.triangleContraction = 0) := by
  refine ⟨fun e => polarized_coefficients round e, doubleContraction_of_round round tf,
    triangleContraction_of_round round tf, fun _ closed => planePencil_diagonal_contractions round closed⟩

/-- The four matrix planes give a closed harmonic round system at every positive strength. -/
theorem fourPlane_roundWitness (c : ℝ) (hc : 0 < c) :
    ∃ h : SymmetricCubic TracelessHermitian3,
      IsRound h c ∧ h.TraceFree ∧ IsClosedPlaneSystem h fourPlaneDecomposition := by
  let g := interactionCubic fourPlanePair 1
  let s := Real.sqrt (6 * c)
  have law : HasSquareLaw g := fourPlane_squareLaw
  have hr : IsRound (s • g) c := by
    refine ⟨hc, fun x => ?_⟩
    rw [SymmetricCubic.squareMap_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity), law x]
    ring
  have hp : IsClosedPlaneSystem (s • g) fourPlaneDecomposition := by
    intro i x y hx hy
    have hxy : g.L x y ∈ (fourPlaneDecomposition.plane i)ᗮᗮ := by
      rw [Submodule.mem_orthogonal']
      intro z hz
      exact fourPlaneData.repeatedPlane i ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    rw [Submodule.orthogonal_orthogonal] at hxy
    simpa only [map_smul, LinearMap.smul_apply] using
      (fourPlaneDecomposition.plane i).smul_mem s hxy
  exact ⟨s • g, hr, traceFree_of_isClosedPlaneSystem hr hp, hp⟩

end

end ThirteenPlanes.PencilEnergy
