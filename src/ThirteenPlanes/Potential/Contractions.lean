module

public import ThirteenPlanes.Potential.Coords

@[expose] public section

/-! The quartic contractions of a cubic in orthonormal coordinates.

`tr M_h²` and the tetrahedron `⟨h, T(h)⟩`, together with the pairings of a direction `k` against
`T(h)` and against the insertion of `M_h`, are written as the coordinate sums of
`ThirteenPlanes.Potential.Coords`. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace SymmetricCubic

/-- `tr M_h²`, the trace of the square of the double contraction. -/
def doubleTraceSq (h : SymmetricCubic V) : ℝ :=
  LinearMap.trace ℝ V (h.doubleContraction * h.doubleContraction)

/-- The tetrahedron contraction `⟨h, T(h)⟩ = h_ijk h_ilm h_jln h_kmn`. -/
def tetrahedron (h : SymmetricCubic V) : ℝ :=
  h.tensorPairing h.triangleContraction

variable {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)

omit [FiniteDimensional ℝ V] in
theorem coefficient_symm (h : SymmetricCubic V) : Coords.Symm (h.coefficient e) :=
  ⟨fun _ _ _ => h.apply_swap₁₂ _ _ _, fun _ _ _ => h.apply_swap₂₃ _ _ _⟩

omit [FiniteDimensional ℝ V] in
theorem coefficient_path (h k : SymmetricCubic V) (s : ℝ) :
    (h + s • k).coefficient e = Coords.path (h.coefficient e) (k.coefficient e) s := by
  funext i j l
  simp [coefficient, Coords.path]

theorem tensorPairing_eq_tuple (g h : SymmetricCubic V) :
    g.tensorPairing h = ∑ t : ι × ι × ι,
      g.coefficient e t.1 t.2.1 t.2.2 * h.coefficient e t.1 t.2.1 t.2.2 := by
  rw [tensorPairing_eq_sum e]
  simp only [Fintype.sum_prod_type]

theorem tensorPairing_triangle_eq (g h : SymmetricCubic V) :
    g.tensorPairing h.triangleContraction = Coords.tetSum (g.coefficient e) (h.coefficient e)
      (h.coefficient e) (h.coefficient e) := by
  rw [tensorPairing_eq_sum e]
  simp only [coefficient, apply_triangleContraction_eq_sum e, Finset.mul_sum,
    Fintype.sum_prod_type, Coords.tetSum, Coords.tetTerm, mul_assoc]

theorem tetrahedron_eq (h : SymmetricCubic V) :
    h.tetrahedron = Coords.tetSum (h.coefficient e) (h.coefficient e) (h.coefficient e)
      (h.coefficient e) :=
  tensorPairing_triangle_eq e h h

omit [FiniteDimensional ℝ V] in
theorem apply_sum₁ (h : SymmetricCubic V) (c : ι → ℝ) (w u : V) :
    h.apply (∑ j, c j • e j) w u = ∑ j, c j * h.apply (e j) w u := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [apply]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, apply_add₁, apply_smul₁, ih]

theorem apply_doubleContraction₁ (h : SymmetricCubic V) (v w u : V) :
    h.apply (h.doubleContraction v) w u = ∑ j,
      (∑ z, ∑ y, h.apply v (e z) (e y) * h.apply (e j) (e z) (e y)) * h.apply (e j) w u := by
  conv_lhs => rw [← e.sum_repr' (h.doubleContraction v)]
  rw [apply_sum₁]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm, inner_doubleContraction_eq_sum e]

/-- Pairing a direction with the doubly contracted insertion, in coordinates. -/
theorem sum_apply_doubleContraction (g : ι → ι → ι → ℝ) (h : SymmetricCubic V) :
    ∑ i, ∑ x, ∑ y, g i x y * h.apply (h.doubleContraction (e i)) (e x) (e y) =
      Coords.quadSum g (h.coefficient e) (h.coefficient e) (h.coefficient e) := by
  simp only [apply_doubleContraction₁ e, Finset.mul_sum, Finset.sum_mul, Coords.quadSum,
    Coords.quadTerm, Fintype.sum_prod_type, coefficient]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
  ring

theorem doubleTraceSq_eq (h : SymmetricCubic V) :
    h.doubleTraceSq = Coords.quadSum (h.coefficient e) (h.coefficient e) (h.coefficient e)
      (h.coefficient e) := by
  rw [← sum_apply_doubleContraction e, doubleTraceSq, trace_eq_sum_inner e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_apply_eq_comp, real_inner_comm, inner_doubleContraction_eq_sum e]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [coefficient, mul_comm]

/-- Pairing a symmetric cubic with the insertion of an endomorphism: the three slots contribute
equally. -/
theorem tensorPairing_insert (g h : SymmetricCubic V) (A : V →ₗ[ℝ] V) :
    g.tensorPairing (h.insert A) =
      3 * ∑ i, ∑ x, ∑ y, g.coefficient e i x y * h.apply (A (e i)) (e x) (e y) := by
  rw [tensorPairing_eq_sum e]
  simp only [coefficient, apply_insert, mul_add, Finset.sum_add_distrib]
  have h2 : ∑ i, ∑ x, ∑ y, g.apply (e i) (e x) (e y) * h.apply (e i) (A (e x)) (e y) =
      ∑ i, ∑ x, ∑ y, g.apply (e i) (e x) (e y) * h.apply (A (e i)) (e x) (e y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun y _ => ?_
    rw [g.apply_swap₁₂, h.apply_swap₁₂]
  have h3 : ∑ i, ∑ x, ∑ y, g.apply (e i) (e x) (e y) * h.apply (e i) (e x) (A (e y)) =
      ∑ i, ∑ x, ∑ y, g.apply (e i) (e x) (e y) * h.apply (e i) (A (e x)) (e y) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [g.apply_swap₂₃, h.apply_swap₂₃]
  rw [h3, h2]
  ring

theorem tensorPairing_insert_doubleContraction (g h : SymmetricCubic V) :
    g.tensorPairing (h.insert h.doubleContraction) =
      3 * Coords.quadSum (g.coefficient e) (h.coefficient e) (h.coefficient e)
        (h.coefficient e) := by
  rw [tensorPairing_insert e, sum_apply_doubleContraction e]

end SymmetricCubic

end

end ThirteenPlanes
