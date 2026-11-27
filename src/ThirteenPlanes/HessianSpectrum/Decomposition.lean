module

public import ThirteenPlanes.HessianSpectrum.Basic

@[expose] public section

/-! The orthogonal decomposition of the space of symmetric cubics at a floor cubic.

At a cubic `C` with `A(C) = A*` (dimension `n ≥ 1`) the rotation space, the trace space and
their common orthogonal complement are pairwise orthogonal for the coefficient pairing, and every
cubic is uniquely the sum of one element of each. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The common orthogonal complement is orthogonal to the rotation space (for any `C`). -/
theorem rotation_orth_complement {C r w : SymmetricCubic V} (hr : r ∈ rotationSpace C)
    (hw : w ∈ complementSpace C) : r.tensorPairing w = 0 := by
  obtain ⟨A, hA, rfl⟩ := mem_rotationSpace.mp hr
  rw [tensorPairing_comm]; exact hw.2 A hA

/-- The common orthogonal complement is orthogonal to the trace space (for any `C`). -/
theorem trace_orth_complement {C t w : SymmetricCubic V} (ht : t ∈ traceSpace V)
    (hw : w ∈ complementSpace C) : t.tensorPairing w = 0 := by
  obtain ⟨u, rfl⟩ := mem_traceSpace.mp ht
  rw [tensorPairing_comm]; exact hw.1 u

/-- At a floor cubic the rotation space is orthogonal to the trace space. -/
theorem rotation_orth_trace (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) {r t : SymmetricCubic V}
    (hr : r ∈ rotationSpace C) (ht : t ∈ traceSpace V) : r.tensorPairing t = 0 := by
  obtain ⟨A, hA, rfl⟩ := mem_rotationSpace.mp hr
  obtain ⟨u, rfl⟩ := mem_traceSpace.mp ht
  have h1 := aHessian_rotation hn hfl hA (traceAdjoint u)
  rw [aHessian_comm, aHessian_traceAdjoint hn hfl] at h1
  have hc : (3 * (Module.finrank ℝ V : ℝ) + 14) / ((Module.finrank ℝ V : ℝ) + 10) ≠ 0 := by
    positivity
  rw [tensorPairing_comm]
  exact (mul_eq_zero.mp h1).resolve_left hc

/-- The complement space is a complement of `rotationSpace C ⊔ traceSpace V` (for any `C`). -/
theorem isCompl_complementSpace (C : SymmetricCubic V) :
    IsCompl (rotationSpace C ⊔ traceSpace V) (complementSpace C) := by
  rw [complementSpace_eq_orthogonal]
  set W := rotationSpace C ⊔ traceSpace V
  have sep : ∀ x : ↥W, (LinearMap.BilinForm.restrict tpForm W) x x = 0 → x = 0 := by
    intro x hx
    exact Subtype.ext ((tensorPairing_self_eq_zero_iff (x : SymmetricCubic V)).mp hx)
  have hnd : (LinearMap.BilinForm.restrict tpForm W).Nondegenerate :=
    ⟨fun x hx => sep x (hx x), fun y hy => sep y (hy y)⟩
  exact @LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate (SymmetricCubic V) ℝ _
    inferInstance inferInstance inferInstance tpForm W tpForm_isRefl hnd

/-- At a floor cubic the rotation space and the trace space meet only in zero. -/
theorem rotation_inf_trace (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) :
    rotationSpace C ⊓ traceSpace V = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact (tensorPairing_self_eq_zero_iff x).mp (rotation_orth_trace hn hfl hx.1 hx.2)

/-- Uniqueness of a decomposition into three pairwise orthogonal parts. -/
theorem eq_of_orthogonal_sum {r r' t t' w w' : SymmetricCubic V}
    (hrt : r.tensorPairing t = 0 ∧ r.tensorPairing t' = 0 ∧ r'.tensorPairing t = 0 ∧
      r'.tensorPairing t' = 0)
    (hrw : r.tensorPairing w = 0 ∧ r.tensorPairing w' = 0 ∧ r'.tensorPairing w = 0 ∧
      r'.tensorPairing w' = 0)
    (htw : t.tensorPairing w = 0 ∧ t.tensorPairing w' = 0 ∧ t'.tensorPairing w = 0 ∧
      t'.tensorPairing w' = 0)
    (h : r + t + w = r' + t' + w') : r = r' ∧ t = t' ∧ w = w' := by
  have hsum : (r - r') + (t - t') + (w - w') = 0 := by
    have : (r - r') + (t - t') + (w - w') = (r + t + w) - (r' + t' + w') := by abel
    rw [this, h]; exact sub_self (r' + t' + w')
  have key : ∀ x : SymmetricCubic V, x.tensorPairing ((r - r') + (t - t') + (w - w')) = 0 :=
    fun x => by rw [hsum]; simpa using tensorPairing_smul_right x (0 : SymmetricCubic V) 0
  have ex : ∀ x : SymmetricCubic V, x.tensorPairing ((r - r') + (t - t') + (w - w')) =
      x.tensorPairing r - x.tensorPairing r' + (x.tensorPairing t - x.tensorPairing t') +
        (x.tensorPairing w - x.tensorPairing w') := fun x => by
    rw [tensorPairing_add_right, tensorPairing_add_right, tensorPairing_sub_right,
      tensorPairing_sub_right, tensorPairing_sub_right]
  have pr : (r - r').tensorPairing (r - r') = 0 := by
    have := key (r - r'); rw [ex] at this
    simp only [tensorPairing_sub_left] at this
    rw [tensorPairing_sub_right, tensorPairing_sub_left, tensorPairing_sub_left]
    rw [hrt.1, hrt.2.1, hrt.2.2.1, hrt.2.2.2, hrw.1, hrw.2.1, hrw.2.2.1, hrw.2.2.2] at this
    linarith
  have pt : (t - t').tensorPairing (t - t') = 0 := by
    have := key (t - t'); rw [ex] at this
    simp only [tensorPairing_sub_left] at this
    rw [tensorPairing_sub_right, tensorPairing_sub_left, tensorPairing_sub_left]
    rw [tensorPairing_comm t r, tensorPairing_comm t r', tensorPairing_comm t' r,
      tensorPairing_comm t' r', hrt.1, hrt.2.1, hrt.2.2.1, hrt.2.2.2, htw.1, htw.2.1, htw.2.2.1,
      htw.2.2.2] at this
    linarith
  have pw : (w - w').tensorPairing (w - w') = 0 := by
    have := key (w - w'); rw [ex] at this
    simp only [tensorPairing_sub_left] at this
    rw [tensorPairing_sub_right, tensorPairing_sub_left, tensorPairing_sub_left]
    rw [tensorPairing_comm w r, tensorPairing_comm w r', tensorPairing_comm w' r,
      tensorPairing_comm w' r', tensorPairing_comm w t, tensorPairing_comm w t',
      tensorPairing_comm w' t, tensorPairing_comm w' t', hrw.1, hrw.2.1, hrw.2.2.1, hrw.2.2.2,
      htw.1, htw.2.1, htw.2.2.1, htw.2.2.2] at this
    linarith
  exact ⟨sub_eq_zero.mp ((tensorPairing_self_eq_zero_iff _).mp pr),
    sub_eq_zero.mp ((tensorPairing_self_eq_zero_iff _).mp pt),
    sub_eq_zero.mp ((tensorPairing_self_eq_zero_iff _).mp pw)⟩

/-- **Orthogonal direct sum.** At a cubic `C` with `A(C) = A*` in dimension `n ≥ 1`, every cubic
is uniquely `r + t + w` with `r` an infinitesimal rotation `C.insert A`, `t = τ*u`, and `w`
orthogonal to both spaces. -/
theorem existsUnique_decomposition (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) (D : SymmetricCubic V) :
    ∃! p : ↥(rotationSpace C) × ↥(traceSpace V) × ↥(complementSpace C),
      (p.1 : SymmetricCubic V) + p.2.1 + p.2.2 = D := by
  have hD : D ∈ (rotationSpace C ⊔ traceSpace V) ⊔ complementSpace C := by
    rw [(isCompl_complementSpace C).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hD
  obtain ⟨r, hr, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
  refine ⟨(⟨r, hr⟩, ⟨t, ht⟩, ⟨w, hw⟩), rfl, ?_⟩
  rintro ⟨⟨r', hr'⟩, ⟨t', ht'⟩, ⟨w', hw'⟩⟩ h
  have := eq_of_orthogonal_sum (r := r') (r' := r) (t := t') (t' := t) (w := w') (w' := w)
    ⟨rotation_orth_trace hn hfl hr' ht', rotation_orth_trace hn hfl hr' ht,
      rotation_orth_trace hn hfl hr ht', rotation_orth_trace hn hfl hr ht⟩
    ⟨rotation_orth_complement hr' hw', rotation_orth_complement hr' hw,
      rotation_orth_complement hr hw', rotation_orth_complement hr hw⟩
    ⟨trace_orth_complement ht' hw', trace_orth_complement ht' hw,
      trace_orth_complement ht hw', trace_orth_complement ht hw⟩ h
  obtain ⟨e1, e2, e3⟩ := this
  subst e1 e2 e3
  rfl

end

end ThirteenPlanes
