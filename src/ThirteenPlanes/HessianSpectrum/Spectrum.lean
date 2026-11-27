module

public import ThirteenPlanes.HessianSpectrum.Decomposition

@[expose] public section

/-! The spectral form of the Hessian at a floor cubic.

The Hessian bilinear form is linear in each argument. At a floor cubic `C`, on the orthogonal
decomposition `D = r + t + w` (rotation, trace, complement) it acts as `0`, `(3n+14)/(n+10)` and `1`:
`Hess_C(D, k) = ⟨(3n+14)/(n+10) • t + w, k⟩`. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem aHessian_add_smul_right (C D k₁ k₂ : SymmetricCubic V) (a : ℝ) :
    aHessian C D (k₁ + a • k₂) = aHessian C D k₁ + a * aHessian C D k₂ := by
  have h := (hasDerivAt_gradPair_aHessian C D k₁).add
    ((hasDerivAt_gradPair_aHessian C D k₂).const_mul a)
  have h' : HasDerivAt (fun s : ℝ => gradPair (C + s • D) (k₁ + a • k₂))
      (aHessian C D k₁ + a * aHessian C D k₂) 0 := by
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    exact gradPair_add_smul _ _ _ a
  exact (hasDerivAt_gradPair_aHessian C D (k₁ + a • k₂)).unique h'

theorem aHessian_add_right (C D k₁ k₂ : SymmetricCubic V) :
    aHessian C D (k₁ + k₂) = aHessian C D k₁ + aHessian C D k₂ := by
  simpa using aHessian_add_smul_right C D k₁ k₂ 1

theorem aHessian_add_left (C D₁ D₂ k : SymmetricCubic V) :
    aHessian C (D₁ + D₂) k = aHessian C D₁ k + aHessian C D₂ k := by
  rw [aHessian_comm, aHessian_add_right, aHessian_comm C k, aHessian_comm C k]

/-- The Hessian eigenvalue on the trace directions, `(3n+14)/(n+10)`. -/
def traceEigenvalue (n : ℕ) : ℝ := (3 * (n : ℝ) + 14) / ((n : ℝ) + 10)

/-- **Spectral action of the Hessian.** At a floor cubic `C` in dimension `n ≥ 1`, if `r` is an
infinitesimal rotation, `t = τ*u` and `w` is orthogonal to both spaces, then
`Hess_C(r + t + w, k) = (3n+14)/(n+10) ⟨t,k⟩ + ⟨w,k⟩`: eigenvalues `0`, `(3n+14)/(n+10)`, `1`. -/
theorem aHessian_spectral (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) {r t w : SymmetricCubic V}
    (hr : r ∈ rotationSpace C) (ht : t ∈ traceSpace V) (hw : w ∈ complementSpace C)
    (k : SymmetricCubic V) :
    aHessian C (r + t + w) k =
      traceEigenvalue (Module.finrank ℝ V) * t.tensorPairing k + w.tensorPairing k := by
  obtain ⟨A, hA, rfl⟩ := mem_rotationSpace.mp hr
  obtain ⟨u, rfl⟩ := mem_traceSpace.mp ht
  rw [aHessian_add_left, aHessian_add_left, aHessian_rotation hn hfl hA,
    aHessian_traceAdjoint hn hfl, aHessian_complement hn hfl hw.1 hw.2, zero_add, traceEigenvalue]

/-- **The Hessian at a floor cubic, spectral theorem.** For a cubic `C` with `A(C) = A*` in dimension
`n ≥ 1`: the rotation space `{C.insert A : A skew}`, the trace space `{τ*u}` and their common
orthogonal complement are pairwise orthogonal; every cubic `D` is uniquely `r + t + w` with one part
in each; and `Hess_C(D, k) = ⟨(3n+14)/(n+10) • t + w, k⟩` for all `k`, so the Hessian acts as `0`,
`(3n+14)/(n+10)` and `1` on the three summands. -/
theorem hessian_spectral_theorem (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) :
    (∀ r ∈ rotationSpace C, ∀ t ∈ traceSpace V, r.tensorPairing t = 0) ∧
    (∀ r ∈ rotationSpace C, ∀ w ∈ complementSpace C, r.tensorPairing w = 0) ∧
    (∀ t ∈ traceSpace V, ∀ w ∈ complementSpace C, t.tensorPairing w = 0) ∧
    (∀ D : SymmetricCubic V, ∃! p : ↥(rotationSpace C) × ↥(traceSpace V) × ↥(complementSpace C),
      (p.1 : SymmetricCubic V) + p.2.1 + p.2.2 = D) ∧
    (∀ r ∈ rotationSpace C, ∀ t ∈ traceSpace V, ∀ w ∈ complementSpace C, ∀ k : SymmetricCubic V,
      aHessian C (r + t + w) k =
        (traceEigenvalue (Module.finrank ℝ V) • t + w).tensorPairing k) :=
  ⟨fun _ hr _ ht => rotation_orth_trace hn hfl hr ht,
    fun _ hr _ hw => rotation_orth_complement hr hw,
    fun _ ht _ hw => trace_orth_complement ht hw,
    existsUnique_decomposition hn hfl,
    fun _ hr _ ht _ hw k => by
      rw [aHessian_spectral hn hfl hr ht hw, tensorPairing_add_left, tensorPairing_smul_left]⟩

/-- The Hessian quadratic form on `r + t + w` is `(3n+14)/(n+10) ⟨t,t⟩ + ⟨w,w⟩`. -/
theorem aHessian_spectral_self (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) {r t w : SymmetricCubic V}
    (hr : r ∈ rotationSpace C) (ht : t ∈ traceSpace V) (hw : w ∈ complementSpace C) :
    aHessian C (r + t + w) (r + t + w) =
      traceEigenvalue (Module.finrank ℝ V) * t.tensorPairing t + w.tensorPairing w := by
  rw [aHessian_spectral hn hfl hr ht hw, tensorPairing_add_right, tensorPairing_add_right,
    tensorPairing_add_right, tensorPairing_add_right, tensorPairing_comm t r,
    rotation_orth_trace hn hfl hr ht, trace_orth_complement ht hw, tensorPairing_comm w r,
    rotation_orth_complement hr hw, tensorPairing_comm w t, trace_orth_complement ht hw]
  ring

end

end ThirteenPlanes
