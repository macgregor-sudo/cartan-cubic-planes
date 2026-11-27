module

public import ThirteenPlanes.PencilFlow.Dynamics.Scalar

@[expose] public section

/-! The plane pencil on fields from one or two planes: its diagonal part reproduces the cubic on a
single closed plane and vanishes on two different planes. Consequences: the energy of every
equal split and the injectivity of the coupling map. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes.PencilFlow.Dynamics

noncomputable section

open Statements SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {m : ℕ} {planes : PlaneDecomposition V (Fin m)}

omit [FiniteDimensional ℝ V] in
theorem apply_finset_sum {ι : Type*} (s : Finset ι) (f : ι → SymmetricCubic V) (x y z : V) :
    (∑ k ∈ s, f k).apply x y z = ∑ k ∈ s, (f k).apply x y z := by
  simp only [SymmetricCubic.apply, map_sum, LinearMap.sum_apply, sum_inner]

theorem proj_apply (k : Fin m) (x : V) :
    planes.proj k x = (planes.plane k).starProjection x := by
  simp [PlaneDecomposition.proj]

theorem proj_of_mem {k : Fin m} {x : V} (hx : x ∈ planes.plane k) : planes.proj k x = x := by
  rw [proj_apply]; exact Submodule.starProjection_eq_self_iff.mpr hx

theorem proj_of_mem_ne {i k : Fin m} (hik : i ≠ k) {x : V} (hx : x ∈ planes.plane i) :
    planes.proj k x = 0 := by
  have hx' : x ∈ (planes.plane k)ᗮ := (planes.pairwise_orthogonal hik).le hx
  rw [proj_apply, Submodule.starProjection_apply,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hx']
  rfl

omit [FiniteDimensional ℝ V] in
theorem inner_planes {i j : Fin m} (hij : i ≠ j) {x y : V} (hx : x ∈ planes.plane i)
    (hy : y ∈ planes.plane j) : ⟪x, y⟫ = 0 := by
  have hx' : x ∈ (planes.plane j)ᗮ := (planes.pairwise_orthogonal hij).le hx
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal hy hx'

omit [FiniteDimensional ℝ V] in
@[simp] theorem apply_zero₁ (h : SymmetricCubic V) (y z : V) : h.apply 0 y z = 0 := by
  simp [SymmetricCubic.apply]

omit [FiniteDimensional ℝ V] in
@[simp] theorem apply_zero₂ (h : SymmetricCubic V) (x z : V) : h.apply x 0 z = 0 := by
  simp [SymmetricCubic.apply]

omit [FiniteDimensional ℝ V] in
theorem norm_sq_three (A B C : V) (a b d : ℝ) (hAB : ⟪A, B⟫ = 0) (hAC : ⟪A, C⟫ = 0)
    (hBC : ⟪B, C⟫ = 0) :
    ‖a • A + b • B + d • C‖ ^ 2 = a ^ 2 * ‖A‖ ^ 2 + b ^ 2 * ‖B‖ ^ 2 + d ^ 2 * ‖C‖ ^ 2 := by
  have hBA : ⟪B, A⟫ = 0 := by rw [real_inner_comm]; exact hAB
  have hCA : ⟪C, A⟫ = 0 := by rw [real_inner_comm]; exact hAC
  have hCB : ⟪C, B⟫ = 0 := by rw [real_inner_comm]; exact hBC
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq A,
    ← real_inner_self_eq_norm_sq B, ← real_inner_self_eq_norm_sq C]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hAB, hBA, hAC, hCA, hBC, hCB, mul_zero]
  ring

variable {h : SymmetricCubic V}

theorem diagonal_apply_same (hclosed : IsClosedPlaneSystem h planes) {i : Fin m} {x y : V}
    (hx : x ∈ planes.plane i) (hy : y ∈ planes.plane i) (z : V) :
    (planePencil h planes).diagonalCubic.apply x y z = h.apply x y z := by
  change (∑ k, h.pullback (planes.proj k)).apply x y z = _
  rw [apply_finset_sum, Finset.sum_eq_single i]
  · rw [pullback_apply, proj_of_mem hx, proj_of_mem hy, SymmetricCubic.apply, proj_apply,
      ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hclosed i hx hy)]
    rfl
  · intro k _ hki
    rw [pullback_apply, proj_of_mem_ne (Ne.symm hki) hx, apply_zero₁]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem diagonal_apply_cross {i j : Fin m} (hij : i ≠ j) {x y : V}
    (hx : x ∈ planes.plane i) (hy : y ∈ planes.plane j) (z : V) :
    (planePencil h planes).diagonalCubic.apply x y z = 0 := by
  change (∑ k, h.pullback (planes.proj k)).apply x y z = _
  rw [apply_finset_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [pullback_apply]
  by_cases hki : k = i
  · subst hki
    rw [proj_of_mem_ne (Ne.symm hij) hy, apply_zero₂]
  · rw [proj_of_mem_ne (Ne.symm hki) hx, apply_zero₁]

omit [FiniteDimensional ℝ V] in
theorem L_eq_of_apply {g k : SymmetricCubic V} {x y : V} (H : ∀ z, g.apply x y z = k.apply x y z) :
    g.L x y = k.L x y :=
  ext_inner_right ℝ H

theorem diagonal_L_same (hclosed : IsClosedPlaneSystem h planes) {i : Fin m} {x y : V}
    (hx : x ∈ planes.plane i) (hy : y ∈ planes.plane i) :
    (planePencil h planes).diagonalCubic.L x y = h.L x y :=
  L_eq_of_apply (diagonal_apply_same hclosed hx hy)

theorem diagonal_L_cross {i j : Fin m} (hij : i ≠ j) {x y : V}
    (hx : x ∈ planes.plane i) (hy : y ∈ planes.plane j) :
    (planePencil h planes).diagonalCubic.L x y = 0 := by
  have : (planePencil h planes).diagonalCubic.L x y = (0 : SymmetricCubic V).L x y :=
    L_eq_of_apply fun z => by rw [diagonal_apply_cross hij hx hy, SymmetricCubic.apply_zero]
  simpa using this

theorem mixing_L (x y : V) :
    (planePencil h planes).mixingCubic.L x y =
      h.L x y - (planePencil h planes).diagonalCubic.L x y := by
  change (h - (planePencil h planes).diagonalCubic).L x y = _
  simp

theorem coupling_L_same (hclosed : IsClosedPlaneSystem h planes) {i : Fin m} {x y : V}
    (hx : x ∈ planes.plane i) (hy : y ∈ planes.plane i) (u : ℝ × ℝ) :
    (coupling (planePencil h planes) u).L x y = u.1 • h.L x y := by
  simp only [coupling_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    mixing_L, diagonal_L_same hclosed hx hy, sub_self, smul_zero, add_zero]

theorem coupling_L_cross {i j : Fin m} (hij : i ≠ j) {x y : V}
    (hx : x ∈ planes.plane i) (hy : y ∈ planes.plane j) (u : ℝ × ℝ) :
    (coupling (planePencil h planes) u).L x y = u.2 • h.L x y := by
  simp only [coupling_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    mixing_L, diagonal_L_cross hij hx hy, sub_zero, smul_zero, zero_add]

/-! ### Norms of the three products of two unit fields from different planes -/

section Norms

variable {c : ℝ} (hround : IsRound h c) (hclosed : IsClosedPlaneSystem h planes)
variable {i j : Fin m} (hij : i ≠ j) {x y : V} (hx : x ∈ planes.plane i)
  (hy : y ∈ planes.plane j) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1)
include hround hclosed hij hx hy hx1 hy1

omit [FiniteDimensional ℝ V] in
theorem cross_facts :
    ‖h.L x x‖ ^ 2 = c ∧ ‖h.L y y‖ ^ 2 = c ∧ ‖h.L x y‖ ^ 2 = c / 2 ∧
      ⟪h.L x x, h.L y y⟫ = 0 ∧ ⟪h.L x x, h.L x y⟫ = 0 ∧ ⟪h.L y y, h.L x y⟫ = 0 := by
  have hA : ‖h.L x x‖ ^ 2 = c := by
    have := hround.square_norm x; rw [hx1] at this; simpa [squareMap] using this
  have hB : ‖h.L y y‖ ^ 2 = c := by
    have := hround.square_norm y; rw [hy1] at this; simpa [squareMap] using this
  have hAB : ⟪h.L x x, h.L y y⟫ = 0 := inner_planes hij (hclosed i hx hx) (hclosed j hy hy)
  have hAC : ⟪h.L x x, h.L x y⟫ = 0 := by
    rw [real_inner_comm]
    have e := h.apply_swap₂₃ x y (h.L x x)
    simp only [SymmetricCubic.apply] at e
    rw [e, real_inner_comm]
    exact inner_planes (Ne.symm hij) hy (hclosed i hx (hclosed i hx hx))
  have hBC : ⟪h.L y y, h.L x y⟫ = 0 := by
    rw [real_inner_comm]
    have e1 := h.apply_swap₁₂ x y (h.L y y)
    have e2 := h.apply_swap₂₃ y x (h.L y y)
    simp only [SymmetricCubic.apply] at e1 e2
    rw [e1, e2, real_inner_comm]
    exact inner_planes hij hx (hclosed j hy (hclosed j hy hy))
  have hxy : ⟪x, y⟫ = 0 := inner_planes hij hx hy
  have hnorm : ‖x + y‖ ^ 2 = 2 := by
    have := norm_sq_three x y 0 1 1 0 hxy (by simp) (by simp)
    simp only [one_smul, zero_smul, add_zero, hx1, hy1] at this
    rw [this]; norm_num
  have hsum := hround.square_norm (x + y)
  have hsq : h.squareMap (x + y) = (1 : ℝ) • h.L x x + (1 : ℝ) • h.L y y + (2 : ℝ) • h.L x y := by
    simp only [squareMap, map_add, LinearMap.add_apply, h.L_comm y x]
    module
  rw [hsq, show ‖x + y‖ ^ 4 = (‖x + y‖ ^ 2) ^ 2 by ring, hnorm,
    norm_sq_three _ _ _ _ _ _ hAB hAC hBC, hA, hB] at hsum
  refine ⟨hA, hB, by linarith, hAB, hAC, hBC⟩

/-- The squared field energy of the equal split along the pencil. -/
theorem equalSplit_norm (t : ℝ) :
    ‖(interactionCubic (planePencil h planes) t).squareMap ((Real.sqrt 2)⁻¹ • (x + y))‖ ^ 2 =
      c * (1 + t ^ 2) / 2 := by
  obtain ⟨hA, hB, hC, hAB, hAC, hBC⟩ := cross_facts hround hclosed hij hx hy hx1 hy1
  set Q := interactionCubic (planePencil h planes) t
  have hxx : Q.L x x = h.L x x := by
    simpa [Q, interactionCubic] using coupling_L_same hclosed hx hx (1, t)
  have hyy : Q.L y y = h.L y y := by
    simpa [Q, interactionCubic] using coupling_L_same hclosed hy hy (1, t)
  have hxy : Q.L x y = t • h.L x y := by
    simpa [Q, interactionCubic] using coupling_L_cross hij hx hy (1, t)
  set s := (Real.sqrt 2)⁻¹
  have hs : s * s = 1 / 2 := by
    rw [← pow_two, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hsq0 : Q.squareMap (s • (x + y)) =
      (s * s) • (Q.L x x + Q.L y y + (2 : ℝ) • Q.L x y) := by
    simp only [squareMap, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      Q.L_comm y x]
    module
  have hsq : Q.squareMap (s • (x + y)) =
      (1 / 2 : ℝ) • h.L x x + (1 / 2 : ℝ) • h.L y y + t • h.L x y := by
    rw [hsq0, hxx, hyy, hxy, hs]
    module
  rw [hsq, norm_sq_three _ _ _ _ _ _ hAB hAC hBC, hA, hB, hC]
  ring

end Norms

omit [FiniteDimensional ℝ V] in
/-- Each plane contains a unit vector. -/
theorem exists_unit_mem (k : Fin m) : ∃ x ∈ planes.plane k, ‖x‖ = 1 := by
  have hne : planes.plane k ≠ ⊥ := by
    intro hb
    have := planes.dimension k
    rw [hb, finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨‖x‖⁻¹ • x, Submodule.smul_mem _ _ hx, norm_smul_inv_norm hx0⟩

/-- The coupling map of a round closed plane pencil is injective. -/
theorem coupling_injective {c : ℝ} (hm : 2 ≤ m) (hround : IsRound h c)
    (hclosed : IsClosedPlaneSystem h planes) :
    Function.Injective (coupling (planePencil h planes)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  obtain ⟨x, hx, hx1⟩ := exists_unit_mem (planes := planes) i
  obtain ⟨y, hy, hy1⟩ := exists_unit_mem (planes := planes) j
  obtain ⟨hA, -, hC, -⟩ := cross_facts hround hclosed hij hx hy hx1 hy1
  have hc := hround.positive
  have h1 := coupling_L_same hclosed hx hx u
  have h2 := coupling_L_cross (h := h) hij hx hy u
  rw [hu] at h1 h2
  simp only [map_zero, LinearMap.zero_apply] at h1 h2
  have ha : u.1 = 0 := by
    by_contra ha
    have : h.L x x = 0 := by
      have := h1.symm; rwa [smul_eq_zero, or_iff_right ha] at this
    rw [this, norm_zero] at hA; norm_num at hA; linarith
  have hb : u.2 = 0 := by
    by_contra hb
    have : h.L x y = 0 := by
      have := h2.symm; rwa [smul_eq_zero, or_iff_right hb] at this
    rw [this, norm_zero] at hC; norm_num at hC; linarith
  exact Prod.ext ha hb

end

end ThirteenPlanes.PencilFlow.Dynamics

namespace ThirteenPlanes.PencilFlow.Proofs

open Statements Dynamics

/-- The one-loop pencil flow, the energy of every equal split. -/
theorem equalSplitEnergy (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Statements.EqualSplitEnergy V := by
  intro m _ h c planes hround hclosed i j hij x hx y hy hx1 hy1 t
  have hc := hround.positive
  show _ / c = _
  rw [equalSplit_norm hround hclosed hij hx hy hx1 hy1 t]
  field_simp

end ThirteenPlanes.PencilFlow.Proofs
