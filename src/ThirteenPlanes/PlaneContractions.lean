module

public import ThirteenPlanes.PlaneContractions.Identities

@[expose] public section

/-! The plane theorem: an exhaustive orthogonal decomposition into trace-free planes and the
square law of the equal-strength cubic give the contraction laws of the whole coupling pencil. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

open SymmetricCubic PlaneContractions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem PlaneContractions.coupling_eq_diag_interaction (P : CubicPair V) (u : ℝ × ℝ) :
    coupling P u = (u.1 - u.2) • P.diagonalCubic + u.2 • interactionCubic P 1 := by
  rw [coupling_apply, interactionCubic_one]
  module

/-- Plane theorem: orthogonal trace-free planes with no repeated-plane mixing and the square law
give scalar double contraction `a²/3 + λb²` and closed triangle contraction on the pencil
`aD + bC`, with `λ = (dim V - 2)/12`. -/
theorem planeContractionLaws {ι : Type*} [Fintype ι] (P : CubicPair V)
    (planes : PlaneDecomposition V ι) (hP : HasPlaneData P planes)
    (hsq : HasSquareLaw (interactionCubic P 1)) :
    HasContractionLaws P (((Module.finrank ℝ V : ℝ) - 2) / 12) := by
  set d := interactionCubic P 1 with hd
  set D := P.diagonalCubic with hDdef
  set n : ℝ := (Module.finrank ℝ V : ℝ) with hn
  have tf := traceFree_interaction hP
  have Md : ∀ x y, LinearMap.trace ℝ V (d.L x * d.L y) = (n + 2) / 12 * ⟪x, y⟫ :=
    trace_mul_of_squareLaw hsq tf
  have Td := triangleContraction_of_squareLaw hsq tf
  have hL : ∀ (u : ℝ × ℝ) (x : V),
      (coupling P u).L x = (u.1 - u.2) • D.L x + u.2 • d.L x := by
    intro u x
    rw [coupling_eq_diag_interaction, map_add, map_smul, map_smul]
    rfl
  constructor
  · intro u
    ext x : 1
    apply ext_inner_right ℝ
    intro y
    rw [inner_doubleContraction, hL, hL]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul, smul_eq_mul,
      LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_left]
    rw [trace_diag_mul_diag hP hsq, trace_diag_mul_d hP hsq, LinearMap.trace_mul_comm ℝ (d.L x),
      trace_diag_mul_d hP hsq, Md, real_inner_comm y x, familyM]
    ring
  · intro u
    ext x y z
    rw [apply_triangleContraction, hL, hL, hL, coupling_eq_diag_interaction]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul, smul_eq_mul,
      apply_add, apply_smul]
    have e1 := trace_diag_diag_diag hP hsq x y z
    have e2 := trace_diag_diag_d hP hsq x y z
    have e3 : LinearMap.trace ℝ V (D.L x * d.L y * D.L z) = 0 := by
      rw [LinearMap.trace_mul_cycle]; exact trace_diag_diag_d hP hsq z x y
    have e4 : LinearMap.trace ℝ V (d.L x * D.L y * D.L z) = 0 := by
      rw [LinearMap.trace_mul_cycle, LinearMap.trace_mul_cycle]
      exact trace_diag_diag_d hP hsq y z x
    have e5 := trace_diag_d_d hP hsq x y z
    have e6 : LinearMap.trace ℝ V (d.L x * D.L y * d.L z) = (D.apply y z x - d.apply y z x) / 6 := by
      rw [LinearMap.trace_mul_cycle, LinearMap.trace_mul_cycle]
      exact trace_diag_d_d hP hsq y z x
    have e7 : LinearMap.trace ℝ V (d.L x * d.L y * D.L z) = (D.apply z x y - d.apply z x y) / 6 := by
      rw [LinearMap.trace_mul_cycle]
      exact trace_diag_d_d hP hsq z x y
    have e8 : LinearMap.trace ℝ V (d.L x * d.L y * d.L z) = (-(n - 2) / 24) * d.apply x y z := by
      rw [← apply_triangleContraction, Td, apply_smul]
    have cyc : ∀ (h : SymmetricCubic V) (a b c : V), h.apply a b c = h.apply c a b :=
      fun h a b c => by rw [h.apply_swap₁₂ c, h.apply_swap₂₃]
    have c1 := cyc D y z x
    have c2 := cyc D x y z
    have c3 := cyc d y z x
    have c4 := cyc d x y z
    rw [e1, e2, e3, e4, e5, e6, e7, e8]
    simp only [familyP, familyQ]
    rw [c1, ← c2, c3, ← c4]
    ring

end

end ThirteenPlanes
