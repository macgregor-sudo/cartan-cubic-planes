module

public import ThirteenPlanes.ClosedBlocks.Dimensions

@[expose] public section

set_option backward.privateInPublic true

/-! Closed decompositions of the reducible eikonal cubic. -/

open scoped BigOperators RealInnerProductSpace

namespace ThirteenPlanes.Reducible

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The metric product of the reducible cubic with distinguished axis `a`. -/
private def axisProduct (a : V) : V →ₗ[ℝ] V →ₗ[ℝ] V :=
  LinearMap.mk₂ ℝ (fun x y =>
      (4 * ⟪a, x⟫ * ⟪a, y⟫ - ⟪x, y⟫) • a - ⟪a, x⟫ • y - ⟪a, y⟫ • x)
    (by intro x x' y; simp only [inner_add_right, inner_add_left]; module)
    (by intro t x y; simp only [real_inner_smul_right, real_inner_smul_left]; module)
    (by intro x y y'; simp only [inner_add_right]; module)
    (by intro t x y; simp only [real_inner_smul_right]; module)

/-- The symmetric tensor whose diagonal is the reducible cubic. -/
def cubic (a : V) : SymmetricCubic V :=
  SymmetricCubic.ofProduct (axisProduct a)
    (by
      intro x y
      change (4 * ⟪a, x⟫ * ⟪a, y⟫ - ⟪x, y⟫) • a - ⟪a, x⟫ • y - ⟪a, y⟫ • x =
        (4 * ⟪a, y⟫ * ⟪a, x⟫ - ⟪y, x⟫) • a - ⟪a, y⟫ • x - ⟪a, x⟫ • y
      rw [real_inner_comm y x]
      module)
    (by
      intro x y z
      change ⟪(4 * ⟪a, x⟫ * ⟪a, y⟫ - ⟪x, y⟫) • a - ⟪a, x⟫ • y - ⟪a, y⟫ • x, z⟫ =
        ⟪(4 * ⟪a, x⟫ * ⟪a, z⟫ - ⟪x, z⟫) • a - ⟪a, x⟫ • z - ⟪a, z⟫ • x, y⟫
      simp only [inner_sub_left, real_inner_smul_left, real_inner_comm z y]
      ring)

/-- The cubic polynomial in axial and perpendicular coordinates. -/
theorem cubic_diagonal {a : V} (ha : ‖a‖ = 1) (x : V) :
    (cubic a).apply x x x =
      ⟪a, x⟫ ^ 3 - 3 * ⟪a, x⟫ * ‖x - ⟪a, x⟫ • a‖ ^ 2 := by
  change ⟪(4 * ⟪a, x⟫ * ⟪a, x⟫ - ⟪x, x⟫) • a - ⟪a, x⟫ • x - ⟪a, x⟫ • x, x⟫ = _
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm x a]
  rw [real_inner_self_eq_norm_sq a, ha, real_inner_self_eq_norm_sq x]
  ring

theorem cubic_square (a x : V) :
    (cubic a).L x x = (4 * ⟪a, x⟫ ^ 2 - ‖x‖ ^ 2) • a - (2 * ⟪a, x⟫) • x := by
  change (4 * ⟪a, x⟫ * ⟪a, x⟫ - ⟪x, x⟫) • a - ⟪a, x⟫ • x - ⟪a, x⟫ • x = _
  rw [real_inner_self_eq_norm_sq]
  module

variable [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] {a : V}

omit [FiniteDimensional ℝ V] [Fintype ι] in
private theorem axial_multiple_mem (d : ClosedBlocks.Decomposition (cubic a) ι)
    {i : ι} {x : V} (hx : x ∈ d.piece i) :
    (4 * ⟪a, x⟫ ^ 2 - ‖x‖ ^ 2) • a ∈ d.piece i := by
  have hm := (d.piece i).add_mem (d.closed i hx hx) ((d.piece i).smul_mem (2 * ⟪a, x⟫) hx)
  simpa only [cubic_square, sub_add_cancel] using hm

omit [FiniteDimensional ℝ V] in
private theorem axis_not_mem (ha : ‖a‖ = 1) (d : ClosedBlocks.Decomposition (cubic a) ι)
    (proper : 1 < Fintype.card ι) (i : ι) : a ∉ d.piece i := by
  intro hai
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp proper
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (d.nonzero j)
  have ho := (d.orthogonal hji.symm).inner_eq hai hx
  have hc : 4 * ⟪a, x⟫ ^ 2 - ‖x‖ ^ 2 ≠ 0 := by
    rw [ho]
    have hp := norm_pos_iff.mpr hx0
    nlinarith
  have haj := ((d.piece j).smul_mem_iff hc).mp (axial_multiple_mem d hx)
  have hz := (d.orthogonal hji.symm).inner_eq hai haj
  rw [real_inner_self_eq_norm_sq, ha] at hz
  norm_num at hz

omit [FiniteDimensional ℝ V] in
private theorem axial_norm (ha : ‖a‖ = 1) (d : ClosedBlocks.Decomposition (cubic a) ι)
    (proper : 1 < Fintype.card ι) {i : ι} {x : V} (hx : x ∈ d.piece i) :
    4 * ⟪a, x⟫ ^ 2 = ‖x‖ ^ 2 := by
  by_contra hn
  exact axis_not_mem ha d proper i
    (((d.piece i).smul_mem_iff (sub_ne_zero.mpr hn)).mp (axial_multiple_mem d hx))

omit [FiniteDimensional ℝ V] in
private theorem oriented_generator (ha : ‖a‖ = 1) (d : ClosedBlocks.Decomposition (cubic a) ι)
    (proper : 1 < Fintype.card ι) (i : ι) :
    ∃ v : V, v ∈ d.piece i ∧ ‖v‖ = 1 ∧ ⟪a, v⟫ = 1/2 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (d.nonzero i)
  have hs := axial_norm ha d proper hx
  have hs0 : ⟪a, x⟫ ≠ 0 := by
    intro hz
    rw [hz] at hs
    nlinarith [norm_pos_iff.mpr hx0]
  let v := (2 * ⟪a, x⟫)⁻¹ • x
  have hv := (d.piece i).smul_mem (2 * ⟪a, x⟫)⁻¹ hx
  have hp : ⟪a, v⟫ = 1/2 := by
    dsimp [v]
    rw [real_inner_smul_right]
    field_simp
  refine ⟨v, hv, ?_, hp⟩
  have hvn := axial_norm ha d proper hv
  change 4 * ⟪a, v⟫ ^ 2 = ‖v‖ ^ 2 at hvn
  rw [hp] at hvn
  nlinarith [norm_nonneg v]

omit [FiniteDimensional ℝ V] in
/-- Every proper closed orthogonal decomposition of the reducible cubic is the four
lines over the vertices of a regular tetrahedron in the complement of its axis. -/
theorem four_lines {a : V} (ha : ‖a‖ = 1) (d : ClosedBlocks.Decomposition (cubic a) ι)
    (proper : 1 < Fintype.card ι) :
    Module.finrank ℝ V = 4 ∧ Fintype.card ι = 4 ∧
      ∃ w : ι → V, (∀ i, ‖w i‖ = 1 ∧ ⟪a, w i⟫ = 0 ∧
        d.piece i = Submodule.span ℝ {(1/2 : ℝ) • a + (Real.sqrt 3 / 2) • w i}) ∧
        Pairwise (fun i j => ⟪w i, w j⟫ = -(1/3 : ℝ)) := by
  classical
  choose v hmem hv hp using oriented_generator ha d proper
  have hspan (i : ι) : d.piece i = Submodule.span ℝ {v i} := by
    apply le_antisymm
    · intro x hx
      apply Submodule.mem_span_singleton.mpr
      refine ⟨2 * ⟪a, x⟫, ?_⟩
      have hm := (d.piece i).sub_mem hx ((d.piece i).smul_mem (2 * ⟪a, x⟫) (hmem i))
      have hsq := axial_norm ha d proper hm
      have hz : ⟪a, x - (2 * ⟪a, x⟫) • v i⟫ = 0 := by
        rw [inner_sub_right, real_inner_smul_right, hp]
        ring
      rw [hz] at hsq
      have hn : ‖x - (2 * ⟪a, x⟫) • v i‖ = 0 := by nlinarith [norm_nonneg (x - (2 * ⟪a, x⟫) • v i)]
      exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hmem i))
  have hon : Orthonormal ℝ v := ⟨hv, fun i j hij => (d.orthogonal hij).inner_eq (hmem i) (hmem j)⟩
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rw [← d.exhaustive]
    refine iSup_le fun i => ?_
    rw [hspan i]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self i))
  let b := OrthonormalBasis.mk hon htop
  have hb (i : ι) : b i = v i := congrFun (OrthonormalBasis.coe_mk hon htop) i
  have parseval := b.sum_inner_mul_inner a a
  have hpa (i : ι) : ⟪v i, a⟫ = 1/2 := (real_inner_comm _ _).trans (hp i)
  simp only [hb, hp, hpa, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    real_inner_self_eq_norm_sq, ha] at parseval
  have hcardR : (Fintype.card ι : ℝ) = 4 := by linarith
  have hcard : Fintype.card ι = 4 := by exact_mod_cast hcardR
  refine ⟨(Module.finrank_eq_card_basis b.toBasis).trans hcard, hcard, ?_⟩
  let w (i : ι) := (2 / Real.sqrt 3) • (v i - (1/2 : ℝ) • a)
  have hr : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have haa : ⟪a, a⟫ = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hw (i : ι) : (1/2 : ℝ) • a + (Real.sqrt 3 / 2) • w i = v i := by
    dsimp [w]
    rw [smul_smul, show (Real.sqrt 3 / 2) * (2 / Real.sqrt 3) = 1 by field_simp, one_smul]
    abel
  refine ⟨w, fun i => ⟨?_, ?_, by rw [hw, hspan]⟩, ?_⟩
  · have hii : ⟪v i, v i⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    have hww : ⟪w i, w i⟫ = 1 := by
      simp only [w, real_inner_smul_right, real_inner_smul_left, inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right, hii, hpa, hp, haa]
      field_simp
      nlinarith
    rw [real_inner_self_eq_norm_sq] at hww
    nlinarith [norm_nonneg (w i)]
  · simp only [w, real_inner_smul_right, inner_sub_right, hp, haa]
    ring
  · intro i j hij
    have hij' := hon.2 hij
    simp only [w, real_inner_smul_right, real_inner_smul_left, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, hij', hpa, hp, haa]
    field_simp
    nlinarith

/-- In dimension four every unit axis has a proper closed decomposition. -/
theorem exists_four_lines {a : V} (ha : ‖a‖ = 1) (dim : Module.finrank ℝ V = 4) :
    Nonempty (ClosedBlocks.Decomposition (cubic a) (Fin 4)) := by
  classical
  let b := (stdOrthonormalBasis ℝ V).reindex (finCongr dim)
  let e : V := ∑ i : Fin 4, (1/2 : ℝ) • b i
  have hb (i : Fin 4) : ⟪e, b i⟫ = 1/2 := by
    simp [e, sum_inner, real_inner_smul_left, orthonormal_iff_ite.mp b.orthonormal]
  have he : ‖e‖ = 1 := by
    have h := b.sum_inner_mul_inner e e
    have hb' (i : Fin 4) : ⟪b i, e⟫ = 1/2 := (real_inner_comm _ _).trans (hb i)
    simp only [hb, hb', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg e]
  let R := (Submodule.span ℝ {e-a})ᗮ.reflection
  have hR : R e = a := Submodule.reflection_sub (he.trans ha.symm)
  let v := b.map R
  have hp (i : Fin 4) : ⟪a, v i⟫ = 1/2 := by
    rw [← hR]
    exact (R.inner_map_map e (b i)).trans (hb i)
  refine ⟨{ piece := fun i => Submodule.span ℝ {v i}, nonzero := ?_, orthogonal := ?_,
            exhaustive := ?_, closed := ?_ }⟩
  · intro i hi
    have hm := Submodule.mem_span_singleton_self (R := ℝ) (v i)
    rw [hi, Submodule.mem_bot] at hm
    have hv := v.orthonormal.norm_eq_one i
    simp [hm] at hv
  · intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    intro x hx y hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [real_inner_smul_left, real_inner_smul_right, v.orthonormal.2 hij]
  · apply eq_top_iff.mpr
    intro x _
    rw [← v.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup (fun j => Submodule.span ℝ {v j}) i)
      ((Submodule.span ℝ {v i}).smul_mem _ (Submodule.mem_span_singleton_self _))
  · intro i x y hx hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hv : (cubic a).L (v i) (v i) = -v i := by
      rw [cubic_square, hp, v.orthonormal.norm_eq_one]
      norm_num
    simp only [map_smul, LinearMap.smul_apply, hv]
    exact (Submodule.span ℝ {v i}).smul_mem _
      ((Submodule.span ℝ {v i}).smul_mem _
        ((Submodule.span ℝ {v i}).neg_mem (Submodule.mem_span_singleton_self _)))

end

end ThirteenPlanes.Reducible
