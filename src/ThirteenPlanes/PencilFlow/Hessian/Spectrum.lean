module

public import ThirteenPlanes.PencilFlow.Hessian.Floor

@[expose] public section

set_option backward.privateInPublic true

/-! The Hessian at a floor cubic, its spectrum, kernel, and the orthogonal projection to the rotation tangent. -/

open Filter Set
open scoped BigOperators RealInnerProductSpace Topology

namespace ThirteenPlanes.PencilFlow.HessianBridge

noncomputable section

open SymmetricCubic Statements Quartic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem tp_zero_left (k : SymmetricCubic V) : (0 : SymmetricCubic V).tensorPairing k = 0 := by
  rw [← inner_eq_tensorPairing, inner_zero_left]

/-- On the three summands the Hessian operator acts as `0`, `λ`, `1`. -/
theorem hessianOperator_decomp (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) {r t w : SymmetricCubic V}
    (hr : r ∈ rotationSpace C) (ht : t ∈ traceSpace V) (hw : w ∈ complementSpace C) :
    hessianOperator C (r + t + w) = traceEigenvalue (Module.finrank ℝ V) • t + w := by
  rw [hessianOperator_eq_iff]
  intro k
  rw [aHessian_spectral hn hfl hr ht hw, tensorPairing_add_left, tensorPairing_smul_left]

/-- Coordinates of the cubic trace in the standard basis. -/
theorem inner_cubicTrace (v : V) (Y : SymmetricCubic V) :
    ⟪v, cubicTrace Y⟫ = (traceAdjoint v).tensorPairing Y := by
  let e := stdOrthonormalBasis ℝ V
  rw [tensorPairing_traceAdjoint e]
  have hY := coefficient_symm e Y
  have hc : ∀ j, ⟪e j, cubicTrace Y⟫ = trVec (Y.coefficient e) j := by
    intro j
    simp only [cubicTrace, inner_sum, trVec, coefficient]
    refine Finset.sum_congr rfl fun a _ => ?_
    change ⟪e j, Y.L (e a) (e a)⟫ = Y.coefficient e j a a
    rw [real_inner_comm]
    change Y.coefficient e a a j = _
    rw [hY.s13 a a j]
  simp only [vinner, ← hc]
  rw [← e.sum_inner_mul_inner v]
  exact Finset.sum_congr rfl fun _ _ => by rw [real_inner_comm v]

theorem tensorPairing_traceAdjoint_traceAdjoint (u v : V) :
    (traceAdjoint v).tensorPairing (traceAdjoint u) =
      ((Module.finrank ℝ V : ℝ) + 2) / 3 * ⟪v, u⟫ := by
  let e := stdOrthonormalBasis ℝ V
  rw [tensorPairing_traceAdjoint e, coefficient_traceAdjoint e]
  have ht : trVec (tauAdj fun i => ⟪e i, u⟫) = fun i => (dim (Fin (Module.finrank ℝ V)) + 2) / 3 *
      ⟪e i, u⟫ := funext fun i => trVec_tauAdj _ i
  rw [ht, show dim (Fin (Module.finrank ℝ V)) = (Module.finrank ℝ V : ℝ) by simp [dim],
    ← e.sum_inner_mul_inner v u]
  simp only [vinner, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by rw [real_inner_comm v]; ring

omit [FiniteDimensional ℝ V] in
private theorem skew_identity {ι : Type*} [Fintype ι] (J K : ι → ι → ℝ) :
    ∑ i, ∑ j, (J i j - J j i) * (K i j - K j i) = 2 * ∑ i, ∑ b, (J b i - J i b) * K b i := by
  have a : ∑ i, ∑ j, (J i j - J j i) * K j i = -∑ i, ∑ j, (J i j - J j i) * K i j := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
  have b : ∑ i, ∑ b, (J b i - J i b) * K b i = ∑ i, ∑ j, (J i j - J j i) * K i j := by
    rw [Finset.sum_comm]
  have c : ∑ i, ∑ j, (J i j - J j i) * (K i j - K j i) =
      ∑ i, ∑ j, (J i j - J j i) * K i j - ∑ i, ∑ j, (J i j - J j i) * K j i := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [c, a, b]; ring

/-- The rotation adjoint pairs as the skew contraction. -/
theorem tensorPairing_insert_rotationAdjoint (C Y k : SymmetricCubic V) :
    k.tensorPairing (C.insert (rotationAdjoint C Y)) =
      9 / 4 * skewPair (C.coefficient (stdOrthonormalBasis ℝ V))
        (Y.coefficient (stdOrthonormalBasis ℝ V)) (k.coefficient (stdOrthonormalBasis ℝ V)) := by
  let e := stdOrthonormalBasis ℝ V
  have hdef : rotationAdjoint C Y = skewOp e (fun i j => (3 / 2 : ℝ) *
      (kMat (C.coefficient e) (Y.coefficient e) i j -
        kMat (C.coefficient e) (Y.coefficient e) j i)) := rfl
  rw [hdef, tensorPairing_insert_coord e]
  simp only [matOf_skewOp, skewPair]
  rw [skew_identity]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The explicit Hessian formula** at a floor cubic. -/
theorem hessianOperator_formula (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) (Y : SymmetricCubic V) :
    hessianOperator C Y = Y + (3 * (2 / ((Module.finrank ℝ V : ℝ) + 10))) •
        traceAdjoint (cubicTrace Y) - (1 / 3 : ℝ) • C.insert (rotationAdjoint C Y) := by
  let e := stdOrthonormalBasis ℝ V
  rw [hessianOperator_eq_iff]
  intro k
  rw [aHessian_floor e hn hfl, tensorPairing_sub_left, tensorPairing_add_left,
    tensorPairing_smul_left, tensorPairing_smul_left, tensorPairing_comm (C.insert _),
    tensorPairing_insert_rotationAdjoint, tensorPairing_traceAdjoint e]
  have hc : (fun i => ⟪e i, cubicTrace Y⟫) = trVec (Y.coefficient e) := by
    funext j
    rw [inner_cubicTrace, tensorPairing_traceAdjoint e]
    simp only [vinner]
    have := coefficient_traceAdjoint e (e j)
    have ho := orthonormal_iff_ite.mp e.orthonormal
    simp only [ho]
    simp
  rw [hc]
  ring

theorem hessianOperator_ker (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) :
    LinearMap.ker (hessianOperator C) = rotationSpace C := by
  ext Y
  rw [LinearMap.mem_ker, hessianOperator_eq_iff, mem_rotationSpace]
  simp only [tp_zero_left]
  rw [aHessian_kernel hn hfl]
  exact ⟨fun ⟨A, hA, h⟩ => ⟨A, hA, h.symm⟩, fun ⟨A, hA, h⟩ => ⟨A, hA, h.symm⟩⟩

theorem one_lt_traceEigenvalue (n : ℕ) : 1 < traceEigenvalue n := by
  rw [traceEigenvalue, lt_div_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  linarith

/-- Eigen-equation through the unique decomposition. -/
private theorem eigen_parts (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) {r t w : SymmetricCubic V}
    (hr : r ∈ rotationSpace C) (ht : t ∈ traceSpace V) (hw : w ∈ complementSpace C) (a : ℝ)
    (h : hessianOperator C (r + t + w) = a • (r + t + w)) :
    a • r = 0 ∧ a • t = traceEigenvalue (Module.finrank ℝ V) • t ∧ a • w = w := by
  rw [hessianOperator_decomp hn hfl hr ht hw] at h
  obtain ⟨p, _, huniq⟩ := existsUnique_decomposition hn hfl (a • (r + t + w))
  have h1 := huniq (⟨a • r, (rotationSpace C).smul_mem a hr⟩, ⟨a • t, (traceSpace V).smul_mem a ht⟩,
    ⟨a • w, (complementSpace C).smul_mem a hw⟩) (by simp only [smul_add])
  have h2 := huniq (⟨0, (rotationSpace C).zero_mem⟩,
    ⟨traceEigenvalue (Module.finrank ℝ V) • t, (traceSpace V).smul_mem _ ht⟩, ⟨w, hw⟩)
    (by simp only [zero_add]; exact h)
  have h3 := h1.trans h2.symm
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h3
  exact h3

theorem hessianOperator_eigenspace_trace (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) :
    Module.End.eigenspace (hessianOperator C) (traceEigenvalue (Module.finrank ℝ V)) =
      traceSpace V := by
  have hl1 := one_lt_traceEigenvalue (Module.finrank ℝ V)
  ext Y
  rw [Module.End.mem_eigenspace_iff]
  obtain ⟨⟨⟨r, hr⟩, ⟨t, ht⟩, ⟨w, hw⟩⟩, hsum, huniq⟩ := existsUnique_decomposition hn hfl Y
  simp only at hsum
  subst hsum
  constructor
  · intro h
    obtain ⟨h1, -, h3⟩ := eigen_parts hn hfl hr ht hw _ h
    have hr0 : r = 0 := (smul_eq_zero.mp h1).resolve_left (by linarith)
    have hw0 : w = 0 := by
      have : (traceEigenvalue (Module.finrank ℝ V) - 1) • w = 0 := by rw [sub_smul, h3, one_smul, sub_self]
      exact (smul_eq_zero.mp this).resolve_left (by linarith)
    rw [hr0, hw0, zero_add, add_zero]; exact ht
  · intro hY
    have h3 := huniq (⟨0, (rotationSpace C).zero_mem⟩, ⟨r + t + w, hY⟩,
      ⟨0, (complementSpace C).zero_mem⟩) (by simp only [zero_add, add_zero])
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h3
    obtain ⟨hr0, -, hw0⟩ := h3
    rw [← hr0, ← hw0, zero_add, add_zero]
    have := hessianOperator_decomp hn hfl (rotationSpace C).zero_mem ht (complementSpace C).zero_mem
    simpa only [zero_add, add_zero] using this

theorem hessianOperator_eigenspace_one (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) :
    Module.End.eigenspace (hessianOperator C) 1 = complementSpace C := by
  have hl1 := one_lt_traceEigenvalue (Module.finrank ℝ V)
  ext Y
  rw [Module.End.mem_eigenspace_iff]
  obtain ⟨⟨⟨r, hr⟩, ⟨t, ht⟩, ⟨w, hw⟩⟩, hsum, huniq⟩ := existsUnique_decomposition hn hfl Y
  simp only at hsum
  subst hsum
  constructor
  · intro h
    obtain ⟨h1, h2, -⟩ := eigen_parts hn hfl hr ht hw _ h
    rw [one_smul] at h1
    have ht0 : t = 0 := by
      have : (traceEigenvalue (Module.finrank ℝ V) - 1) • t = 0 := by
        rw [sub_smul, ← h2, one_smul, sub_self]
      exact (smul_eq_zero.mp this).resolve_left (by linarith)
    rw [h1, ht0, zero_add, zero_add]; exact hw
  · intro hY
    have h3 := huniq (⟨0, (rotationSpace C).zero_mem⟩, ⟨0, (traceSpace V).zero_mem⟩,
      ⟨r + t + w, hY⟩) (by simp only [zero_add])
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h3
    obtain ⟨hr0, ht0, -⟩ := h3
    rw [← hr0, ← ht0, zero_add, zero_add, one_smul]
    have := hessianOperator_decomp hn hfl (rotationSpace C).zero_mem (traceSpace V).zero_mem hw
    rwa [zero_add, zero_add, smul_zero, zero_add] at this

/-- The rotation projection. -/
theorem rotationAdjoint_projection (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) (Y : SymmetricCubic V) :
    (1 / 3 : ℝ) • C.insert (rotationAdjoint C Y) = (rotationSpace C).starProjection Y := by
  obtain ⟨⟨⟨r, hr⟩, ⟨t, ht⟩, ⟨w, hw⟩⟩, hsum, _⟩ := existsUnique_decomposition hn hfl Y
  simp only at hsum
  subst hsum
  obtain ⟨u, rfl⟩ := mem_traceSpace.mp ht
  set n : ℝ := (Module.finrank ℝ V : ℝ)
  have hnpos : (0 : ℝ) < n := by simp only [n]; exact_mod_cast hn
  -- the cubic trace
  have htr : cubicTrace (r + traceAdjoint u + w) = ((n + 2) / 3) • u := by
    apply ext_inner_left ℝ
    intro v
    rw [inner_cubicTrace, tensorPairing_add_right, tensorPairing_add_right, real_inner_smul_right,
      tensorPairing_traceAdjoint_traceAdjoint, tensorPairing_comm, rotation_orth_trace hn hfl hr
        (mem_traceSpace.mpr ⟨v, rfl⟩), trace_orth_complement (mem_traceSpace.mpr ⟨v, rfl⟩) hw]
    ring
  have hP := hessianOperator_formula hn hfl (r + traceAdjoint u + w)
  rw [hessianOperator_decomp hn hfl hr ht hw, htr, traceAdjoint_smul, smul_smul] at hP
  have hcoef : 3 * (2 / (n + 10)) * ((n + 2) / 3) = traceEigenvalue (Module.finrank ℝ V) - 1 := by
    simp only [traceEigenvalue]
    field_simp
    ring
  rw [hcoef, sub_smul, one_smul] at hP
  have hproj : (1 / 3 : ℝ) • C.insert (rotationAdjoint C (r + traceAdjoint u + w)) = r := by
    rw [eq_sub_iff_add_eq] at hP
    set P := (1 / 3 : ℝ) • C.insert (rotationAdjoint C (r + traceAdjoint u + w))
    have e1 : P = (traceEigenvalue (Module.finrank ℝ V) • traceAdjoint u + w + P) -
        (traceEigenvalue (Module.finrank ℝ V) • traceAdjoint u + w) := by abel
    rw [e1, hP]
    abel
  rw [hproj]
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hr
  intro x hx
  rw [show r + traceAdjoint u + w - r = traceAdjoint u + w by abel, inner_eq_tensorPairing,
    tensorPairing_add_left, tensorPairing_comm, rotation_orth_trace hn hfl hx ht,
    tensorPairing_comm, rotation_orth_complement hx hw, add_zero]

end

end ThirteenPlanes.PencilFlow.HessianBridge
