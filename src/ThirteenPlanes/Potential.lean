module

public import ThirteenPlanes.Potential.Contractions

@[expose] public section

/-! The one-loop tensor field is a gradient.

With `M_h` the double contraction, `T(h)` the triangle and `P(h) = ⟨h, T(h)⟩` the tetrahedron, the
directional derivatives along `h + s k` are `d⟨h,h⟩[k] = 2⟨k,h⟩`, `d tr M_h²[k] = (4/3)⟨k, ins_h M_h⟩`
and `dP[k] = 4⟨k,T(h)⟩`. Hence the tensor one-loop field `oneLoopBeta ε` is the gradient, for the
coefficient pairing, of

  `Φ_ε(h) = (16π²)⁻¹ (4π²ε ⟨h,h⟩ - (3/8) tr M_h² - (1/2) P(h))`,

and the paper's A-function `A(κ) = -¼⟨κ,κ⟩ + (3/8) tr M_κ² + ½ P(κ)` has gradient
`-16π² · oneLoopBeta (1/(16π²))`. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace SymmetricCubic

theorem tensorPairing_comm (g h : SymmetricCubic V) : g.tensorPairing h = h.tensorPairing g := by
  simp only [tensorPairing_eq_sum (stdOrthonormalBasis ℝ V), mul_comm]

theorem tensorPairing_add_right (k g h : SymmetricCubic V) :
    k.tensorPairing (g + h) = k.tensorPairing g + k.tensorPairing h := by
  simp only [tensorPairing_eq_sum (stdOrthonormalBasis ℝ V), coefficient, apply_add, mul_add,
    Finset.sum_add_distrib]

theorem tensorPairing_smul_right (k g : SymmetricCubic V) (a : ℝ) :
    k.tensorPairing (a • g) = a * k.tensorPairing g := by
  simp only [tensorPairing_eq_sum (stdOrthonormalBasis ℝ V), coefficient, apply_smul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem tensorPairing_sub_right (k g h : SymmetricCubic V) :
    k.tensorPairing (g - h) = k.tensorPairing g - k.tensorPairing h := by
  have hs : ∀ x y z : V, (g - h).apply x y z = g.apply x y z - h.apply x y z := by
    intro x y z
    simp [apply, SymmetricCubic.L, inner_sub_left]
  simp only [tensorPairing_eq_sum (stdOrthonormalBasis ℝ V), coefficient, hs, mul_sub,
    Finset.sum_sub_distrib]

/-- Directional derivative of the squared coefficient norm: `d⟨h,h⟩[k] = 2⟨k,h⟩`. -/
theorem hasDerivAt_tensorPairing_self (h k : SymmetricCubic V) :
    HasDerivAt (fun s : ℝ => (h + s • k).tensorPairing (h + s • k)) (2 * k.tensorPairing h) 0 := by
  let e := stdOrthonormalBasis ℝ V
  have hf : (fun s : ℝ => (h + s • k).tensorPairing (h + s • k)) = fun s : ℝ =>
      ∑ t : _ × _ × _, (h.coefficient e t.1 t.2.1 t.2.2 + s * k.coefficient e t.1 t.2.1 t.2.2) *
        (h.coefficient e t.1 t.2.1 t.2.2 + s * k.coefficient e t.1 t.2.1 t.2.2) := by
    funext s
    rw [tensorPairing_eq_tuple e, coefficient_path e]
    rfl
  rw [hf]
  refine (Coords.hasDerivAt_sum_mul2 _ _ _ _).congr_deriv ?_
  rw [tensorPairing_eq_tuple e, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Directional derivative of `tr M_h²`: `d tr M_h²[k] = (4/3)⟨k, ins_h M_h⟩`, where `ins_h A` inserts
the endomorphism `A` in each of the three slots of `h` and sums. -/
theorem hasDerivAt_doubleTraceSq (h k : SymmetricCubic V) :
    HasDerivAt (fun s : ℝ => (h + s • k).doubleTraceSq)
      (4 / 3 * k.tensorPairing (h.insert h.doubleContraction)) 0 := by
  let e := stdOrthonormalBasis ℝ V
  have hf : (fun s : ℝ => (h + s • k).doubleTraceSq) = fun s : ℝ =>
      Coords.quadSum (Coords.path (h.coefficient e) (k.coefficient e) s)
        (Coords.path (h.coefficient e) (k.coefficient e) s)
        (Coords.path (h.coefficient e) (k.coefficient e) s)
        (Coords.path (h.coefficient e) (k.coefficient e) s) := by
    funext s
    rw [doubleTraceSq_eq e, coefficient_path e]
  rw [hf]
  refine (Coords.hasDerivAt_quadSum_path' _ _).congr_deriv ?_
  rw [tensorPairing_insert_doubleContraction e]
  ring

/-- The tetrahedron is a potential for the triangle: `dP_h[k] = 4⟨k, T(h)⟩`. -/
theorem hasDerivAt_tetrahedron (h k : SymmetricCubic V) :
    HasDerivAt (fun s : ℝ => (h + s • k).tetrahedron)
      (4 * k.tensorPairing h.triangleContraction) 0 := by
  let e := stdOrthonormalBasis ℝ V
  have hf : (fun s : ℝ => (h + s • k).tetrahedron) = fun s : ℝ =>
      Coords.tetSum (Coords.path (h.coefficient e) (k.coefficient e) s)
        (Coords.path (h.coefficient e) (k.coefficient e) s)
        (Coords.path (h.coefficient e) (k.coefficient e) s)
        (Coords.path (h.coefficient e) (k.coefficient e) s) := by
    funext s
    rw [tetrahedron_eq e, coefficient_path e]
  rw [hf, tensorPairing_triangle_eq e]
  exact Coords.hasDerivAt_tetSum_path_symm (coefficient_symm e h) (coefficient_symm e k)

end SymmetricCubic

open SymmetricCubic

/-- The one-loop potential `(16π²)⁻¹ (4π²ε ⟨h,h⟩ - (3/8) tr M_h² - (1/2) ⟨h, T(h)⟩)`. -/
def oneLoopPotential (ε : ℝ) (h : SymmetricCubic V) : ℝ :=
  (16 * Real.pi ^ 2)⁻¹ * (4 * Real.pi ^ 2 * ε * h.tensorPairing h - 3 / 8 * h.doubleTraceSq -
    1 / 2 * h.tetrahedron)

/-- The A-function `-¼⟨κ,κ⟩ + (3/8) tr M_κ² + ½ ⟨κ, T(κ)⟩` in rescaled couplings. -/
def aFunction (κ : SymmetricCubic V) : ℝ :=
  -(1 / 4) * κ.tensorPairing κ + 3 / 8 * κ.doubleTraceSq + 1 / 2 * κ.tetrahedron

/-- The one-loop tensor field is the gradient of the one-loop potential for the coefficient pairing:
the derivative of `Φ_ε` at `h` in direction `k` is `⟨k, β_ε(h)⟩`. -/
theorem oneLoopPotential_hasDerivAt (ε : ℝ) (h k : SymmetricCubic V) :
    HasDerivAt (fun s : ℝ => oneLoopPotential ε (h + s • k))
      (k.tensorPairing (oneLoopBeta ε h)) 0 := by
  have := ((((hasDerivAt_tensorPairing_self h k).const_mul (4 * Real.pi ^ 2 * ε)).sub
    ((hasDerivAt_doubleTraceSq h k).const_mul (3 / 8))).sub
    ((hasDerivAt_tetrahedron h k).const_mul (1 / 2))).const_mul (16 * Real.pi ^ 2)⁻¹
  refine this.congr_deriv ?_
  rw [oneLoopBeta, tensorPairing_smul_right, tensorPairing_sub_right, tensorPairing_sub_right,
    tensorPairing_smul_right, tensorPairing_smul_right, tensorPairing_smul_right]
  ring

/-- The A-function has gradient `-16π² β` at `ε = 1/(16π²)`: the derivative of `A` at `κ` in direction
`k` is `-⟨k, ½κ - ½ ins_κ M_κ - 2T(κ)⟩`. -/
theorem aFunction_hasDerivAt (κ k : SymmetricCubic V) :
    HasDerivAt (fun s : ℝ => aFunction (κ + s • k))
      (-(16 * Real.pi ^ 2) * k.tensorPairing (oneLoopBeta (16 * Real.pi ^ 2)⁻¹ κ)) 0 := by
  have := (((hasDerivAt_tensorPairing_self κ k).const_mul (-(1 / 4))).add
    ((hasDerivAt_doubleTraceSq κ k).const_mul (3 / 8))).add
    ((hasDerivAt_tetrahedron κ k).const_mul (1 / 2))
  refine this.congr_deriv ?_
  have hπ : (16 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  rw [oneLoopBeta, tensorPairing_smul_right, tensorPairing_sub_right, tensorPairing_sub_right,
    tensorPairing_smul_right, tensorPairing_smul_right, tensorPairing_smul_right]
  field_simp
  ring

end

end ThirteenPlanes
