module

public import ThirteenPlanes.Cartan.Conjugation
public import ThirteenPlanes.Cartan.DiagonalWeightsScalar
public import ThirteenPlanes.Cartan.QuaternionJordan
public import ThirteenPlanes.Peirce.SlotQuaternionModel

@[expose] public section

set_option backward.privateInPublic true

/-! The standard Cartan acting on the native traceless quaternionic Hermitian matrices. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB Peirce
open scoped Matrix BigOperators RealInnerProductSpace

noncomputable section

/-- The standard imaginary diagonal, as a skew-Hermitian matrix. -/
def quaternionSkewDiagonal : (Fin 3 → ℝ) →ₗ[ℝ] quaternionSkewMatrices :=
  quaternionicStandardDiagonal.codRestrict _ (fun a => by
    change (Matrix.diagonal fun k => a k • qi)ᴴ = -(Matrix.diagonal fun k => a k • qi)
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
    congr 1
    funext k
    change star (a k • qi) = -(a k • qi)
    rw [Quaternion.star_smul, show star qi = -qi by ext <;> simp [qi], smul_neg])

def quaternionStandardFull : (Fin 3 → ℝ) →ₗ[ℝ] quaternionOperatorAlgebra :=
  quaternionCommutatorLinear.rangeRestrict.comp quaternionSkewDiagonal

@[simp] theorem quaternionSkewDiagonal_matrix (a : Fin 3 → ℝ) :
    (quaternionSkewDiagonal a).val = quaternionicStandardDiagonal a := rfl

/-- The standard diagonal Cartan in the unital quaternionic operator algebra. -/
def quaternionStandardCartan : Submodule ℝ quaternionOperatorAlgebra :=
  quaternionStandardFull.range

private abbrev V := quaternionJordan.traceFree
private abbrev qmat (x : V) := fullMat x.val

/-- The standard diagonal action restricted to the actual traceless matrices. -/
def quaternionStandardRestricted : (Fin 3 → ℝ) →ₗ[ℝ] SkewOperator V :=
  (quaternionJordan.restrictOperators quaternionOperatorAlgebra quaternionOperatorAlgebra_le).toLinearMap.comp
    quaternionStandardFull

theorem quaternionStandardRestricted_range :
    quaternionStandardRestricted.range = quaternionStandardCartan.map
      (quaternionJordan.restrictOperators quaternionOperatorAlgebra quaternionOperatorAlgebra_le).toLinearMap := by
  rw [quaternionStandardRestricted, LinearMap.range_comp, quaternionStandardCartan]

/-- Each native entry carries the two quaternionic weights of its row and column. -/
theorem quaternionStandardRestricted_matrix (a : Fin 3 → ℝ) (x : V) (i j : Fin 3) :
    qmat ((quaternionStandardRestricted a).val x) i j =
      quaternionWeight (a i) (a j) (qmat x i j) := by
  change fullMat (quaternionCommutator (quaternionSkewDiagonal a) x.val) i j = _
  rw [quaternionCommutator_matrix]
  change ((Matrix.diagonal fun k => a k • qi) * qmat x -
    qmat x * (Matrix.diagonal fun k => a k • qi)) i j = _
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rfl

private abbrev Coordinates := ℝ × ℝ × Q × Q × Q

private def coordinates : Coordinates ≃ₗ[ℝ] V :=
  quaternionCartanEquiv.trans quaternionTraceEquiv.symm.toLinearEquiv

private theorem coordinates_matrix (d e : ℝ) (p q r : Q) :
    qmat (coordinates (d, e, p, q, r)) = quaternionCartanMatrix d e p q r := by
  change traceMat (quaternionCartanEquiv (d, e, p, q, r)) = _
  rw [quaternionCartanEquiv_apply, traceMat_quaternionCartanField]

private theorem coordinates_inner (d e f g : ℝ) (p q r s t u : Q) :
    ⟪coordinates (d, e, p, q, r), coordinates (f, g, s, t, u)⟫ =
      d * f + e * g + ⟪p, s⟫ + ⟪q, t⟫ + ⟪r, u⟫ := by
  change ⟪(coordinates (d, e, p, q, r)).val, (coordinates (f, g, s, t, u)).val⟫ = _
  rw [hermitianHilbert_inner]
  change traceForm (qmat (coordinates (d, e, p, q, r))) (qmat (coordinates (f, g, s, t, u))) = _
  rw [coordinates_matrix, coordinates_matrix, ← traceMat_quaternionCartanField, ← traceMat_quaternionCartanField]
  have h := quaternionCartanField_inner d e f g p q r s t u
  rw [tracelessHilbert_inner] at h
  exact h

private def coordAction (a : Fin 3 → ℝ) : Module.End ℝ Coordinates :=
  (0 : Module.End ℝ ℝ).prodMap ((0 : Module.End ℝ ℝ).prodMap
    ((quaternionWeight (a 1) (a 2)).prodMap
      ((quaternionWeight (a 0) (a 2)).prodMap (quaternionWeight (a 0) (a 1)))))

private theorem quaternionWeight_real (a d : ℝ) :
    quaternionWeight a a (d : Q) = 0 := by
  rw [quaternionWeight_apply]
  apply Quaternion.ext <;> simp

private theorem quaternionWeight_star (a b : ℝ) (x : Q) :
    quaternionWeight b a (star x) = star (quaternionWeight a b x) := by
  rw [quaternionWeight_apply b a, quaternionWeight_apply a b]
  apply Quaternion.ext <;> simp <;> ring_nf <;> simp

set_option maxHeartbeats 500000 in
private theorem coordinates_action (a : Fin 3 → ℝ) (d e : ℝ) (p q r : Q) :
    (quaternionStandardRestricted a).val (coordinates (d, e, p, q, r)) =
      coordinates (0, 0, quaternionWeight (a 1) (a 2) p,
        quaternionWeight (a 0) (a 2) q, quaternionWeight (a 0) (a 1) r) := by
  apply Subtype.ext
  apply fullMat_injective
  apply Matrix.ext
  intro i j
  change qmat ((quaternionStandardRestricted a).val (coordinates (d, e, p, q, r))) i j =
    qmat (coordinates (0, 0, quaternionWeight (a 1)
      (a 2) p, quaternionWeight (a 0)
      (a 2) q, quaternionWeight (a 0)
      (a 1) r)) i j
  rw [quaternionStandardRestricted_matrix, coordinates_matrix, coordinates_matrix]
  fin_cases i <;> fin_cases j
  · change quaternionWeight (a 0) (a 0)
      ((2 * ((Real.sqrt 6)⁻¹ * d) : ℝ) : Q) = ((2 * ((Real.sqrt 6)⁻¹ * 0) : ℝ) : Q)
    rw [quaternionWeight_real]
    simp
  · exact map_smul (quaternionWeight (a 0) (a 1)) (Real.sqrt 2)⁻¹ r
  · exact map_smul (quaternionWeight (a 0) (a 2)) (Real.sqrt 2)⁻¹ q
  · change quaternionWeight (a 1) (a 0) (star ((Real.sqrt 2)⁻¹ • r)) =
      star ((Real.sqrt 2)⁻¹ • quaternionWeight (a 0) (a 1) r)
    rw [quaternionWeight_star, map_smul]
  · change quaternionWeight (a 1) (a 1)
      ((-((Real.sqrt 6)⁻¹ * d) + (Real.sqrt 2)⁻¹ * e : ℝ) : Q) =
        ((-((Real.sqrt 6)⁻¹ * 0) + (Real.sqrt 2)⁻¹ * 0 : ℝ) : Q)
    rw [quaternionWeight_real]
    simp
  · exact map_smul (quaternionWeight (a 1) (a 2)) (Real.sqrt 2)⁻¹ p
  · change quaternionWeight (a 2) (a 0) (star ((Real.sqrt 2)⁻¹ • q)) =
      star ((Real.sqrt 2)⁻¹ • quaternionWeight (a 0) (a 2) q)
    rw [quaternionWeight_star, map_smul]
  · change quaternionWeight (a 2) (a 1) (star ((Real.sqrt 2)⁻¹ • p)) =
      star ((Real.sqrt 2)⁻¹ • quaternionWeight (a 1) (a 2) p)
    rw [quaternionWeight_star, map_smul]
  · change quaternionWeight (a 2) (a 2)
      ((-((Real.sqrt 6)⁻¹ * d) - (Real.sqrt 2)⁻¹ * e : ℝ) : Q) =
        ((-((Real.sqrt 6)⁻¹ * 0) - (Real.sqrt 2)⁻¹ * 0 : ℝ) : Q)
    rw [quaternionWeight_real]
    simp

private theorem coordinates_conj_action (a : Fin 3 → ℝ) :
    coordinates.conj (coordAction a) = (quaternionStandardRestricted a).val := by
  apply LinearMap.ext
  intro x
  obtain ⟨⟨d, e, p, q, r⟩, rfl⟩ := coordinates.surjective x
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, coordinates_action]
  rfl

theorem quaternionStandardRestricted_inner (a b : Fin 3 → ℝ) :
    ⟪quaternionStandardRestricted a, quaternionStandardRestricted b⟫ =
      8 * ∑ i, a i * b i := by
  rw [skewOperator_inner, ← coordinates_conj_action, ← coordinates_conj_action,
    ← conj_mul, LinearMap.trace_conj']
  simp only [coordAction, LinearMap.prodMap_mul, LinearMap.trace_prodMap', zero_mul, map_zero,
    zero_add, quaternionWeight_trace_mul, Fin.sum_univ_three]
  ring

private theorem quaternionStandardRestricted_injective : Function.Injective quaternionStandardRestricted := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro a ha
  have hn := quaternionStandardRestricted_inner a a
  rw [ha, inner_zero_left] at hn
  have hz : ∑ i, a i * a i = 0 := by linarith

  funext i
  change a i = 0
  rcases mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_self_nonneg (a j))).mp hz i (Finset.mem_univ i)) with h | h
  · exact h
  · exact h

/-- The actual quaternionic Cartan has dimension three. -/
theorem quaternionStandardCartan_dim : Module.finrank ℝ quaternionStandardCartan = 3 := by
  rw [quaternionStandardCartan, LinearMap.finrank_range_of_inj, Module.finrank_pi_fintype]
  · simp
  · intro a b h
    apply quaternionStandardRestricted_injective
    exact congrArg (quaternionJordan.restrictOperators quaternionOperatorAlgebra quaternionOperatorAlgebra_le) h

private theorem quaternionStandardRestricted_dim :
    Module.finrank ℝ quaternionStandardRestricted.range = 3 := by
  rw [LinearMap.finrank_range_of_inj quaternionStandardRestricted_injective, Module.finrank_pi_fintype]
  simp

/-- The traceless real diagonal plane in the quaternionic Jordan model. -/
private def diagonalCoordinates : (ℝ × ℝ) →ₗ[ℝ] Coordinates where
  toFun p := (p.1, p.2, 0, 0, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private def diagonalInclusion : (ℝ × ℝ) →ₗ[ℝ] V :=
  coordinates.toLinearMap.comp diagonalCoordinates

private theorem diagonalInclusion_apply (d e : ℝ) :
    diagonalInclusion (d, e) = coordinates (d, e, 0, 0, 0) := rfl

/-- The traceless real diagonal plane in the quaternion Jordan model. -/
def quaternionDiagonalPlane : Submodule ℝ V := diagonalInclusion.range

theorem quaternionDiagonalPlane_dim : Module.finrank ℝ quaternionDiagonalPlane = 2 := by
  rw [quaternionDiagonalPlane, LinearMap.finrank_range_of_inj]
  · simp [Module.finrank_prod, Module.finrank_self]
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    rw [diagonalInclusion_apply, diagonalInclusion_apply] at h
    have he := coordinates.injective h
    exact Prod.ext (congrArg (fun t : Coordinates => t.1) he) (congrArg (fun t : Coordinates => t.2.1) he)

set_option maxHeartbeats 500000 in
theorem quaternionStandardFixedSpace :
    fixedSpace quaternionStandardRestricted.range = quaternionDiagonalPlane := by
  rw [quaternionDiagonalPlane]
  ext x
  obtain ⟨⟨d, e, p, q, r⟩, rfl⟩ := coordinates.surjective x
  rw [mem_fixedSpace]
  constructor
  · intro h
    have hz (a : Fin 3 → ℝ) :=
      coordinates.injective ((coordinates_action a d e p q r).symm.trans
        ((h ⟨quaternionStandardRestricted a, LinearMap.mem_range_self _ _⟩).trans
          (coordinates.map_zero.symm)))
    have hp : quaternionWeight 1 0 p = 0 := by
      simpa using congrArg (fun t : Coordinates => t.2.2.1) (hz ![0, 1, 0])
    have hq : quaternionWeight 1 0 q = 0 := by
      simpa using congrArg (fun t : Coordinates => t.2.2.2.1) (hz ![1, 0, 0])
    have hr : quaternionWeight 1 0 r = 0 := by
      simpa using congrArg (fun t : Coordinates => t.2.2.2.2) (hz ![1, 0, 0])
    have h0 (u : Q) (hu : quaternionWeight 1 0 u = 0) : u = 0 := by
      have hsq := (quaternionWeight_left_right_sq u).1
      rw [hu, map_zero] at hsq
      exact neg_eq_zero.mp hsq.symm
    rw [h0 p hp, h0 q hq, h0 r hr]
    exact ⟨(d, e), diagonalInclusion_apply d e⟩
  · rintro ⟨⟨f, g⟩, hx⟩
    rw [diagonalInclusion_apply] at hx
    rintro ⟨_, a, rfl⟩
    change (quaternionStandardRestricted a).val (coordinates (d, e, p, q, r)) = 0
    rw [← hx]
    rw [coordinates_action]
    simp only [map_zero]
    exact coordinates.map_zero


/-- Membership in the fixed plane means that every native off-diagonal entry vanishes. -/
theorem mem_quaternionDiagonalPlane_iff (x : quaternionJordan.traceFree) :
    x ∈ quaternionDiagonalPlane ↔ ∀ i j : Fin 3, i ≠ j → fullMat x.val i j = 0 := by
  constructor
  · rintro ⟨⟨d, e⟩, rfl⟩ i j hij
    rw [diagonalInclusion_apply]
    change qmat (coordinates (d, e, 0, 0, 0)) i j = 0
    rw [coordinates_matrix]
    fin_cases i <;> fin_cases j <;>
      simp_all [quaternionCartanMatrix, quaternionSlotMatrix, matrixOfHermCoordinates]
  · intro hx
    obtain ⟨⟨d, e, p, q, r⟩, rfl⟩ := coordinates.surjective x
    have hp := hx 1 2 (by decide)
    have hq := hx 0 2 (by decide)
    have hr := hx 0 1 (by decide)
    change qmat (coordinates (d, e, p, q, r)) 1 2 = 0 at hp
    change qmat (coordinates (d, e, p, q, r)) 0 2 = 0 at hq
    change qmat (coordinates (d, e, p, q, r)) 0 1 = 0 at hr
    rw [coordinates_matrix] at hp hq hr
    change (Real.sqrt 2)⁻¹ • p = (0 : Q) at hp
    change (Real.sqrt 2)⁻¹ • q = (0 : Q) at hq
    change (Real.sqrt 2)⁻¹ • r = (0 : Q) at hr
    have h : (Real.sqrt 2)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num))
    rw [(smul_eq_zero.mp hp).resolve_left h, (smul_eq_zero.mp hq).resolve_left h,
      (smul_eq_zero.mp hr).resolve_left h]
    exact ⟨(d, e), diagonalInclusion_apply d e⟩

private theorem quaternionDiagonalPlane_projection (d e : ℝ) (p q r : Q) :
    projection quaternionDiagonalPlane (coordinates (d, e, p, q, r)) = coordinates (d, e, 0, 0, 0) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [quaternionDiagonalPlane]
    exact ⟨(d, e), diagonalInclusion_apply d e⟩
  · rw [quaternionDiagonalPlane]
    rintro _ ⟨⟨f, g⟩, rfl⟩
    rw [diagonalInclusion_apply]
    change ⟪coordinates (d, e, p, q, r) - coordinates (d, e, 0, 0, 0),
      coordinates (f, g, 0, 0, 0)⟫ = 0
    have hsub : coordinates (d, e, p, q, r) - coordinates (d, e, 0, 0, 0) =
        coordinates (d - d, e - e, p - 0, q - 0, r - 0) :=
      (map_sub coordinates ((d, e, p, q, r) : Coordinates) ((d, e, 0, 0, 0) : Coordinates)).symm
    rw [hsub, coordinates_inner]
    simp

private def unitCoordinate (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

private theorem quaternionStandardRestricted_commute (a b : Fin 3 → ℝ) :
    Commute (quaternionStandardRestricted a).val (quaternionStandardRestricted b).val := by
  show (quaternionStandardRestricted a).val * (quaternionStandardRestricted b).val =
    (quaternionStandardRestricted b).val * (quaternionStandardRestricted a).val
  apply LinearMap.ext
  intro x
  obtain ⟨⟨d, e, p, q, r⟩, rfl⟩ := coordinates.surjective x
  simp only [mul_apply_eq_comp, coordinates_action]
  have h (a b c d : ℝ) (z : Q) :
      quaternionWeight a b (quaternionWeight c d z) = quaternionWeight c d (quaternionWeight a b z) := by
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, quaternionWeight_comp_apply,
      quaternionWeight_comp_apply, mul_comm (a - b), mul_comm (a + b)]
  simp only [h (a 1) (a 2), h (a 0) (a 2), h (a 0) (a 1)]

set_option maxHeartbeats 700000 in
theorem quaternionStandardRestricted_casimir :
    operatorCasimir quaternionStandardRestricted.range =
      (1 / 4 : ℝ) • (LinearMap.id - projection (fixedSpace quaternionStandardRestricted.range)) := by
  let A (i : Fin 3) : quaternionStandardRestricted.range :=
    ⟨quaternionStandardRestricted (unitCoordinate i), LinearMap.mem_range_self _ _⟩
  have hA (i j : Fin 3) : ⟪A i, A j⟫ = if i = j then (8 : ℝ) else 0 := by
    change ⟪quaternionStandardRestricted (unitCoordinate i),
      quaternionStandardRestricted (unitCoordinate j)⟫ = _
    rw [quaternionStandardRestricted_inner]
    simp [unitCoordinate, Pi.single_apply, eq_comm]
  rw [operatorCasimir_of_orthogonalBasis _ A (fun _ => 8)
    (quaternionStandardRestricted_dim.trans (Fintype.card_fin 3).symm) (by norm_num) hA,
    quaternionStandardFixedSpace]
  apply LinearMap.ext
  intro x
  obtain ⟨⟨d, e, p, q, r⟩, rfl⟩ := coordinates.surjective x
  simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.smul_apply, mul_apply_eq_comp,
    LinearMap.sub_apply, LinearMap.id_apply, quaternionDiagonalPlane_projection, Fin.sum_univ_three]
  simp only [A, coordinates_action]
  simp only [unitCoordinate, Pi.single_apply]
  norm_num
  simp only [(quaternionWeight_left_right_sq _).1, (quaternionWeight_left_right_sq _).2]
  have hzero (v : Q) : quaternionWeight 0 0 (quaternionWeight 0 0 v) = 0 := by
    rw [quaternionWeight_apply]
    apply Quaternion.ext <;> norm_num
  simp only [hzero, ← map_sub, ← map_smul, ← map_add, ← map_neg]
  apply congrArg coordinates
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  all_goals dsimp
  · ring
  · ring
  · module
  · module
  · module

/-- The standard quaternionic Cartan is of frame type for the actual trace normalization. -/
theorem quaternionStandardFrameType :
    IsFrameType (quaternionStandardCartan.map
      (quaternionJordan.restrictOperators quaternionOperatorAlgebra quaternionOperatorAlgebra_le).toLinearMap)
      3 (1 / 4) := by
  rw [← quaternionStandardRestricted_range]
  refine ⟨?_, quaternionStandardRestricted_dim, ?_, quaternionStandardRestricted_casimir⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact quaternionStandardRestricted_commute a b
  · rw [quaternionStandardFixedSpace, quaternionDiagonalPlane_dim]

/-- The centralizer of the standard diagonal in skew-Hermitian quaternionic matrices. -/
theorem quaternionicStandardDiagonal_centralizer (A : QMat) (hA : Aᴴ = -A)
    (h : ∀ a : Fin 3 → ℝ, Commute A (quaternionicStandardDiagonal a)) :
    A ∈ quaternionicStandardDiagonal.range := by
  refine ⟨fun i => (A i i).imI, ?_⟩
  apply Matrix.ext
  intro i j
  have he := congrArg (fun M : QMat => M i j) (h (unitCoordinate i)).eq
  change (A * Matrix.diagonal fun k => unitCoordinate i k • qi) i j =
    (Matrix.diagonal (fun k => unitCoordinate i k • qi) * A) i j at he
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  by_cases hij : i = j
  · subst j
    have hb := congrArg (fun M : QMat => M i i) hA
    change star (A i i) = -(A i i) at hb
    have hre := congrArg (fun x : Q => x.re) hb
    have hj := congrArg (fun x : Q => x.imK) he
    have hk := congrArg (fun x : Q => x.imJ) he
    simp [unitCoordinate, qi] at hj hk
    simp at hre
    change (Matrix.diagonal fun k => (A k k).imI • qi) i i = _
    rw [Matrix.diagonal_apply_eq]
    apply Quaternion.ext <;> simp [qi] <;> linarith
  · have hz : qi * A i j = 0 := by
      simpa [unitCoordinate, Pi.single_apply, hij] using he.symm
    have hqi : qi ≠ 0 := by
      intro hx
      have hy := congrArg (fun x : Q => x.imI) hx
      norm_num [qi] at hy
    change (Matrix.diagonal fun k => (A k k).imI • qi) i j = _
    rw [Matrix.diagonal_apply_ne _ hij, (mul_eq_zero.mp hz).resolve_left hqi]

end

end ThirteenPlanes.Cartan
