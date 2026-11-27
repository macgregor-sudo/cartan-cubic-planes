module

public import ThirteenPlanes.MinimumHessian.Floor
public import ThirteenPlanes.MinimumHessian.Skew
public import ThirteenPlanes.AllCubicSquares

@[expose] public section

/-! The Hessian of the A-function at a floor cubic.

Let `C` be a real symmetric cubic in dimension `n ≥ 1` with `A(C) = A*`. In any orthonormal basis,
`Hess_C(D,k) = ⟨D,k⟩ + 3λ τD·τk - 3⟨K_a(D), K_a(k)⟩` with `λ = 2/(n+10)` and `K_a` the skew part of
`K(D)_ij = C_iab D_jab`. Consequently:
* `Hess_C(C.insert A, ·) = 0` for every skew-adjoint `A` (infinitesimal rotations),
* `Hess_C(τ*u, ·) = (3n+14)/(n+10) ⟨τ*u, ·⟩` on the image of the trace adjoint,
* `Hess_C(D, ·) = ⟨D, ·⟩` for `D` orthogonal to both,
* the kernel of the Hessian is exactly the space of infinitesimal rotations `C.insert A`.
The floor is attained only in dimensions 2, 5, 8, 14, 26 (a cited classification, not used here);
the statements hold wherever `A(C) = A*`. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open Quartic Coords SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

/-- At the floor, `M = (n+2)/(n+10) δ`, `S = 2/(n+10) Π` and the trace vector vanishes. -/
theorem floorData_of_floor (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) :
    FloorData (C.coefficient e) (((Module.finrank ℝ V : ℝ) + 2) / ((Module.finrank ℝ V : ℝ) + 10))
      (2 / ((Module.finrank ℝ V : ℝ) + 10)) := by
  obtain ⟨hx, hv, hM, hSig, hH⟩ := (aFunction_eq_floor_iff e hn C).mp hfl
  set n : ℝ := (Module.finrank ℝ V : ℝ)
  have hpos : 0 < n := by simp only [n]; exact_mod_cast hn
  have hdim : dim ι = n := dim_eq_finrank e
  have hne : Nonempty ι := by
    rw [Module.finrank_eq_card_basis e.toBasis] at hn
    exact Fintype.card_pos_iff.mp hn
  set c := C.coefficient e
  have hc := coefficient_symm e C
  have hxc : strength c = floorStrength n := by rw [← tensorPairing_self_eq_strength e]; exact hx
  have h10 : n + 10 ≠ 0 := by linarith
  have h2 : n + 2 ≠ 0 := by linarith
  refine ⟨hc, hv, fun i j => ?_, fun i j k l => ?_⟩
  · have := congrFun (congrFun hM i) j
    simp only [mTraceless, traceless, Pi.zero_apply, mtrace_mMat] at this
    rw [hxc, hdim] at this
    simp only [floorStrength] at this
    have : mMat c i j = n * (n + 2) / (n + 10) / n * dlt i j := by linarith
    rw [this]; field_simp
  · rw [harm_decomp (sq4 c) i j k l]
    have h0 : sig0 (sq4 c) = 0 := hSig
    have h1 : harm (sq4 c) = 0 := hH
    have hv0 : trVec c = 0 := hv
    have hsig : sig (sq4 c) = 2 * floorStrength n := by
      rw [sig, mtrace_contr_sq4 hc, hv0, hxc]; simp [vinner]
    rw [h0, h1, hsig, hdim]
    simp only [dsym, Pi.zero_apply, mul_zero, add_zero, floorStrength]
    field_simp

/-- A floor cubic is a critical point of the A-function. -/
theorem gradPair_floor (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) (k : SymmetricCubic V) :
    gradPair C k = 0 := by
  let e := stdOrthonormalBasis ℝ V
  have F := floorData_of_floor e hn hfl
  rw [gradPair_eq e, gradC_floor F (coefficient_symm e k)]
  have h10 : (Module.finrank ℝ V : ℝ) + 10 ≠ 0 := by positivity
  field_simp; ring

/-- **The Hessian at the floor**, in any orthonormal basis:
`Hess_C(D,k) = ⟨D,k⟩ + 3λ τD·τk - ¾ Σ(K(D)-K(D)ᵀ)(K(k)-K(k)ᵀ)`, with `λ = 2/(n+10)`. -/
theorem aHessian_floor (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) (D k : SymmetricCubic V) :
    aHessian C D k = D.tensorPairing k +
      3 * (2 / ((Module.finrank ℝ V : ℝ) + 10)) *
        vinner (trVec (D.coefficient e)) (trVec (k.coefficient e)) -
      3 / 4 * skewPair (C.coefficient e) (D.coefficient e) (k.coefficient e) := by
  have F := floorData_of_floor e hn hfl
  rw [aHessian_eq e, hessC_floor F (coefficient_symm e D) (coefficient_symm e k),
    tensorPairing_eq_sum e]
  have h10 : (Module.finrank ℝ V : ℝ) + 10 ≠ 0 := by positivity
  have : -(1 / 2) + 3 / 2 * (((Module.finrank ℝ V : ℝ) + 2) / ((Module.finrank ℝ V : ℝ) + 10)) +
      6 * (2 / ((Module.finrank ℝ V : ℝ) + 10)) = 1 := by field_simp; ring
  rw [this, one_mul]; rfl

/-- **Eigenvalue 0 on the rotation tangent.** At a floor cubic `C`, the Hessian vanishes on every
infinitesimal rotation `C.insert A`, `A` skew-adjoint. -/
theorem aHessian_rotation (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) {A : V →ₗ[ℝ] V} (hA : IsSkew A)
    (k : SymmetricCubic V) : aHessian C (C.insert A) k = 0 := by
  rw [aHessian_comm]
  exact aHessian_insert_of_critical C k (gradPair_floor hn hfl) hA

theorem tensorPairing_traceAdjoint (u : V) (k : SymmetricCubic V) :
    (traceAdjoint u).tensorPairing k =
      vinner (fun i => ⟪e i, u⟫) (trVec (k.coefficient e)) := by
  rw [tensorPairing_eq_sum e, coefficient_traceAdjoint e]
  exact cinner_tauAdj (coefficient_symm e k) _

/-- **Eigenvalue (3n+14)/(n+10) on the trace directions.** -/
theorem aHessian_traceAdjoint (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) (u : V) (k : SymmetricCubic V) :
    aHessian C (traceAdjoint u) k =
      (3 * (Module.finrank ℝ V : ℝ) + 14) / ((Module.finrank ℝ V : ℝ) + 10) *
        (traceAdjoint u).tensorPairing k := by
  let e := stdOrthonormalBasis ℝ V
  have F := floorData_of_floor e hn hfl
  rw [aHessian_floor e hn hfl, tensorPairing_traceAdjoint e, coefficient_traceAdjoint e,
    skewPair_of_symm (kMat_tauAdj_symm F.symm F.tr _)]
  have ht : trVec (tauAdj fun i => ⟪e i, u⟫) = fun i => (dim (Fin (Module.finrank ℝ V)) + 2) / 3 *
      ⟪e i, u⟫ := funext fun i => trVec_tauAdj _ i
  rw [ht, show dim (Fin (Module.finrank ℝ V)) = (Module.finrank ℝ V : ℝ) by simp [dim]]
  have hv : vinner (fun i => ((Module.finrank ℝ V : ℝ) + 2) / 3 * ⟪e i, u⟫)
      (trVec (k.coefficient e)) = ((Module.finrank ℝ V : ℝ) + 2) / 3 *
      vinner (fun i => ⟪e i, u⟫) (trVec (k.coefficient e)) := by
    simp only [vinner, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hv]
  have h10 : (Module.finrank ℝ V : ℝ) + 10 ≠ 0 := by positivity
  field_simp; ring

omit [DecidableEq ι] in
theorem exists_vector_coords (w : ι → ℝ) : ∃ u : V, (fun i => ⟪e i, u⟫) = w := by
  refine ⟨e.repr.symm (WithLp.toLp 2 w), funext fun i => ?_⟩
  rw [← e.repr_apply_apply]; simp

/-- **Eigenvalue 1 on the complement.** If `D` is orthogonal to every `τ*u` and to every
infinitesimal rotation of the floor cubic `C`, then `Hess_C(D, ·) = ⟨D, ·⟩`. -/
theorem aHessian_complement (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) {D : SymmetricCubic V}
    (hτ : ∀ u : V, D.tensorPairing (traceAdjoint u) = 0)
    (hL : ∀ A : V →ₗ[ℝ] V, IsSkew A → D.tensorPairing (C.insert A) = 0) (k : SymmetricCubic V) :
    aHessian C D k = D.tensorPairing k := by
  let e := stdOrthonormalBasis ℝ V
  rw [aHessian_floor e hn hfl]
  set d := D.coefficient e
  set c := C.coefficient e
  -- the trace vector of `D` vanishes
  have htr : trVec d = 0 := by
    obtain ⟨u, hu⟩ := exists_vector_coords e (trVec d)
    have := hτ u
    rw [tensorPairing_comm, tensorPairing_traceAdjoint e, hu] at this
    exact (vinner_self_eq_zero _).mp this
  -- `K(D)` is symmetric
  have hK : ∀ i j, kMat c d i j = kMat c d j i := by
    set K := kMat c d
    let Ω : Fin (Module.finrank ℝ V) → Fin (Module.finrank ℝ V) → ℝ := fun b i => K b i - K i b
    have hΩ : ∀ a i, Ω a i = -Ω i a := fun a i => by simp only [Ω]; ring
    have h0 := hL _ (isSkew_skewOp e hΩ)
    rw [tensorPairing_insert_coord e] at h0
    simp only [matOf_skewOp] at h0
    have hsq : ∑ i, ∑ b, (K b i - K i b) * (K b i - K i b) =
        2 * ∑ i, ∑ b, Ω b i * K b i := by
      have hsw : ∑ i, ∑ b, (K b i - K i b) * K i b = -∑ i, ∑ b, (K b i - K i b) * K b i := by
        rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun _ _ => by
          rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
      have : ∑ i, ∑ b, (K b i - K i b) * (K b i - K i b) =
          ∑ i, ∑ b, (K b i - K i b) * K b i - ∑ i, ∑ b, (K b i - K i b) * K i b := by
        simp only [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [this, hsw]; simp only [Ω]; ring
    have hz : ∑ i, ∑ b, (K b i - K i b) * (K b i - K i b) = 0 := by rw [hsq]; linarith
    intro i j
    have n2 : ∀ i, 0 ≤ ∑ b, (K b i - K i b) * (K b i - K i b) := fun _ =>
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => n2 i).mp hz j (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => mul_self_nonneg (K b j - K j b)).mp h1
      i (Finset.mem_univ _)
    linarith [mul_self_eq_zero.mp h2]
  rw [htr, skewPair_of_symm hK]
  simp [vinner]

/-- **The kernel of the Hessian at the floor is exactly the rotation tangent:**
`Hess_C(D, ·) = 0` iff `D = C.insert A` for some skew-adjoint `A`. -/
theorem aHessian_kernel (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) (D : SymmetricCubic V) :
    (∀ k, aHessian C D k = 0) ↔ ∃ A : V →ₗ[ℝ] V, IsSkew A ∧ D = C.insert A := by
  constructor
  · intro h0
    let e := stdOrthonormalBasis ℝ V
    set d := D.coefficient e
    set c := C.coefficient e
    have hpos : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast hn
    have htr : trVec d = 0 := by
      obtain ⟨u, hu⟩ := exists_vector_coords e (trVec d)
      have := h0 (traceAdjoint u)
      rw [aHessian_comm, aHessian_traceAdjoint hn hfl, tensorPairing_traceAdjoint e, hu] at this
      have hc0 : (3 * (Module.finrank ℝ V : ℝ) + 14) / ((Module.finrank ℝ V : ℝ) + 10) ≠ 0 := by
        positivity
      exact (vinner_self_eq_zero _).mp ((mul_eq_zero.mp this).resolve_left hc0)
    have hD : ∀ k, D.tensorPairing k = 3 / 4 * skewPair c d (k.coefficient e) := by
      intro k
      have := h0 k
      rw [aHessian_floor e hn hfl, htr] at this
      simp only [vinner, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero] at this
      linarith
    set K := kMat c d
    let Ω : Fin (Module.finrank ℝ V) → Fin (Module.finrank ℝ V) → ℝ :=
      fun b i => 1 / 2 * (K b i - K i b)
    have hΩ : ∀ a i, Ω a i = -Ω i a := fun a i => by simp only [Ω]; ring
    refine ⟨skewOp e Ω, isSkew_skewOp e hΩ, eq_of_tensorPairing _ _ fun k => ?_⟩
    rw [hD k, tensorPairing_comm (C.insert _), tensorPairing_insert_coord e]
    simp only [matOf_skewOp, skewPair, Ω]
    set Kk := kMat c (k.coefficient e)
    have e1 : ∑ i, ∑ j, (K i j - K j i) * (Kk i j - Kk j i) =
        2 * ∑ i, ∑ j, (K i j - K j i) * Kk i j := by
      have hsw : ∑ i, ∑ j, (K i j - K j i) * Kk j i = -∑ i, ∑ j, (K i j - K j i) * Kk i j := by
        rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun _ _ => by
          rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
      have : ∑ i, ∑ j, (K i j - K j i) * (Kk i j - Kk j i) =
          ∑ i, ∑ j, (K i j - K j i) * Kk i j - ∑ i, ∑ j, (K i j - K j i) * Kk j i := by
        simp only [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [this, hsw]; ring
    have e2 : ∑ i, ∑ b, 1 / 2 * (K b i - K i b) * Kk b i =
        1 / 2 * ∑ i, ∑ j, (K i j - K j i) * Kk i j := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2]; ring
  · rintro ⟨A, hA, rfl⟩ k
    exact aHessian_rotation hn hfl hA k

theorem traceAdjoint_sub (u u' : V) :
    traceAdjoint (u - u') = traceAdjoint u - traceAdjoint u' := by
  apply ext; intro x y z
  have hs : ∀ (g h : SymmetricCubic V), (g - h).apply x y z = g.apply x y z - h.apply x y z :=
    fun g h => by simp [SymmetricCubic.apply, SymmetricCubic.L, inner_sub_left]
  rw [hs]
  simp only [traceAdjoint, apply_ofProduct, LinearMap.mk₂_apply, real_inner_smul_left,
    inner_add_left, inner_sub_left, inner_sub_right, real_inner_smul_left]
  ring

/-- `⟨τ*u, τ*u⟩ = (n+2)/3 ‖u‖²`; in particular `τ*` is injective, so its image has dimension `n`. -/
theorem tensorPairing_traceAdjoint_self (u : V) :
    (traceAdjoint u).tensorPairing (traceAdjoint u) =
      ((Module.finrank ℝ V : ℝ) + 2) / 3 * ‖u‖ ^ 2 := by
  let e := stdOrthonormalBasis ℝ V
  rw [tensorPairing_traceAdjoint e, coefficient_traceAdjoint e]
  have ht : trVec (tauAdj fun i => ⟪e i, u⟫) = fun i => (dim (Fin (Module.finrank ℝ V)) + 2) / 3 *
      ⟪e i, u⟫ := funext fun i => trVec_tauAdj _ i
  rw [ht, show dim (Fin (Module.finrank ℝ V)) = (Module.finrank ℝ V : ℝ) by simp [dim],
    ← e.sum_sq_inner_right]
  simp only [vinner, Finset.mul_sum, sq]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem traceAdjoint_injective : Function.Injective (traceAdjoint : V → SymmetricCubic V) := by
  intro u u' h
  have h0 : traceAdjoint (u - u') = 0 := by rw [traceAdjoint_sub, h]; exact sub_self (traceAdjoint u')
  have := tensorPairing_traceAdjoint_self (u - u')
  rw [h0] at this
  have hz : (0 : SymmetricCubic V).tensorPairing 0 = 0 := by
    rw [tensorPairing_eq_sum (stdOrthonormalBasis ℝ V)]; simp [coefficient]
  rw [hz] at this
  have hpos : (0 : ℝ) < ((Module.finrank ℝ V : ℝ) + 2) / 3 := by positivity
  have : ‖u - u'‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp this.symm with h1 | h1
    · exact absurd h1 hpos.ne'
    · exact h1
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))

end

end ThirteenPlanes
