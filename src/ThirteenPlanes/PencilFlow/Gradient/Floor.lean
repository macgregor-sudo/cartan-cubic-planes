module

public import ThirteenPlanes.EikonalRigidityStatements
public import ThirteenPlanes.SphereFloorEquality

@[expose] public section

/-! Proposition variance (spherical variance and potential), parts (a) and (b): the floor of the A-function for
every cubic, with the last two squares written as sphere variances of the harmonic parts of the
scalar potential, and the trace-free isotropic form.

The identities are `ThirteenPlanes.aFunction_sub_floor`, `ThirteenPlanes.sphereVariance_energyPart2`,
`ThirteenPlanes.sphereVariance_energyPart4`, `ThirteenPlanes.sphereVariance_energy`, and the floor
equality `ThirteenPlanes.aFunction_floor_equality`. The bridge proved here turns the vanishing of the
coordinate trace vector and traceless double contraction into the basis-free hypotheses. -/

open scoped BigOperators RealInnerProductSpace

namespace ThirteenPlanes.PencilFlow.Proofs

noncomputable section

open ThirteenPlanes ThirteenPlanes.SymmetricCubic ThirteenPlanes.PencilFlow.Statements Quartic

section Bridges

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

omit [DecidableEq ι] in
/-- A vanishing coordinate trace vector means the cubic is trace-free. -/
theorem traceFree_of_traceVec_eq_zero (κ : SymmetricCubic V) (hv : κ.traceVec e = 0) :
    κ.TraceFree := by
  have hw : ‖κ.trVector‖ ^ 2 = 0 := by
    rw [← vinner_traceVec e, hv]; simp [vinner]
  have hw0 : κ.trVector = 0 := by simpa using hw
  intro x
  have := inner_riesz ((LinearMap.trace ℝ V).comp κ.L) x
  rw [← trVector, hw0, inner_zero_left, LinearMap.comp_apply] at this
  exact this.symm

/-- A vanishing traceless double contraction means the double contraction is scalar. -/
theorem doubleContraction_scalar_of_mTraceless_eq_zero (κ : SymmetricCubic V)
    (hM : κ.mTraceless e = 0) :
    ∃ m : ℝ, κ.doubleContraction = m • (LinearMap.id : V →ₗ[ℝ] V) := by
  refine ⟨mtrace (mMat (κ.coefficient e)) / dim ι, ?_⟩
  apply e.toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis]
  apply InnerProductSpace.ext_inner_right_basis e.toBasis
  intro j
  rw [OrthonormalBasis.coe_toBasis, inner_doubleContraction_eq_sum e, LinearMap.smul_apply,
    LinearMap.id_apply, real_inner_smul_left, e.inner_eq_ite]
  have hij := congrFun (congrFun hM i) j
  simp only [mTraceless, traceless, Pi.zero_apply, dlt, mMat, coefficient] at hij
  rw [mul_ite, mul_one, mul_zero] at hij ⊢
  split_ifs at hij ⊢ <;> linarith

end Bridges

/-- Spherical variance and potential (a), for every cubic and every orthonormal basis. -/
theorem potentialFloor (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : Statements.VarianceA V := by
  intro e κ n x v traceSq K₀ R₀ H V₂ V₄
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hN : (0 : ℝ) < n := by simp only [n]; exact_mod_cast hn
  have key := aFunction_sub_floor e hn κ
  simp only at key
  have hV₂ := sphereVariance_energyPart2 e κ
  have hV₄ := sphereVariance_energyPart4 e κ
  have hV := sphereVariance_energy e κ
  have h2 : n + 2 ≠ 0 := by linarith
  have h4 : n + 4 ≠ 0 := by linarith
  have h6 : n + 6 ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_, floorValue_le_aFunction_of_basis e hn κ, ?_⟩
  · rw [key]; ring
  · change _ = 4 * n * (n + 2) * (n + 4) * sphereVariance (κ.energyPart2 e)
    rw [hV₂]; field_simp; ring
  · change _ = 2 * n * (n + 2) * (n + 4) * (n + 6) * sphereVariance (κ.energyPart4 e)
    rw [hV₄]; field_simp; ring
  · change sphereVariance (κ.energyPart2 e) + sphereVariance (κ.energyPart4 e) =
      sphereVariance (fun y => ‖κ.squareMap y‖ ^ 2 / 8)
    rw [hV₂, hV₄, hV]
  · constructor
    · intro hA
      obtain ⟨hx, hv, hM, -, -⟩ := (aFunction_eq_floor_iff e hn κ).mp hA
      have hTF := traceFree_of_traceVec_eq_zero e κ hv
      have hK := doubleContraction_scalar_of_mTraceless_eq_zero e κ hM
      have heq := (aFunction_floor_equality κ hTF hK).2
      obtain ⟨-, u, hu⟩ := heq.mp (by rw [hA]; simp only [floorValue, floorStrength, n])
      exact ⟨hx, hTF, hK, u, hu⟩
    · rintro ⟨hx, hTF, hK, u, hu⟩
      have heq := (aFunction_floor_equality κ hTF hK).2
      rw [heq.mpr ⟨hx, u, hu⟩]
      simp only [floorValue, floorStrength, n]

/-- Spherical variance and potential (b), the trace-free scalar case with the full sphere variance. -/
theorem harmonicIsotropicFloor (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : Statements.VarianceB V := by
  intro κ hv m hM n
  have key := aFunction_floor_identity κ hv ⟨m, hM⟩
  simp only at key
  simp only [floorValue, floorStrength, n]
  exact key

end

end ThirteenPlanes.PencilFlow.Proofs
