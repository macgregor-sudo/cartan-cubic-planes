module

public import ThirteenPlanes.AllCubicSquares

@[expose] public section

set_option backward.privateInPublic true

/-! Basis independence of the individual squares in the floor-plus-squares identity.

The squares `|v|²`, `|M̊|²`, `|Σ̊|²` and `|H|²` of `aFunction_sub_floor` are defined through a chosen
orthonormal basis. Each equals a basis-free expression (for `n ≥ 1`):
* `|v|² = ‖w‖²`, with `w` the trace vector `⟪w, x⟫ = tr L_x`;
* `|M̊|² = tr M² - x²/n`;
* `|Σ̊|² = |Σ|² - σ²/n`, with `σ = 2x + |v|²` and `|Σ|²` the Hilbert–Schmidt square of the bilinear form
  `Σ(x,y) = 2⟪M x, y⟫ + h(x,y,w)`;
* `|H|² = 3 tr M² + 6 P - 3σ²/(n(n+2)) - 6|Σ̊|²/(n+4)`.
Hence each square takes the same value in any two orthonormal bases. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open Quartic SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (e' : OrthonormalBasis κ ℝ V)

omit [DecidableEq ι] in
theorem sum_sq_linear_eq_norm (φ : V →ₗ[ℝ] ℝ) : ∑ i, φ (e i) ^ 2 = ‖riesz φ‖ ^ 2 := by
  rw [← e.sum_sq_inner_right]
  exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm, inner_riesz]

omit [DecidableEq ι] [DecidableEq κ] in
/-- `Σᵢ φ(eᵢ)²` does not depend on the orthonormal basis. -/
theorem sum_sq_linear (φ : V →ₗ[ℝ] ℝ) : ∑ i, φ (e i) ^ 2 = ∑ k, φ (e' k) ^ 2 := by
  rw [sum_sq_linear_eq_norm e, sum_sq_linear_eq_norm e']

omit [DecidableEq ι] [DecidableEq κ] in
/-- `Σᵢⱼ β(eᵢ,eⱼ)²` does not depend on the orthonormal basis. -/
theorem sum_sq_bilinear (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ∑ i, ∑ j, β (e i) (e j) ^ 2 = ∑ k, ∑ l, β (e' k) (e' l) ^ 2 :=
  calc ∑ i, ∑ j, β (e i) (e j) ^ 2 = ∑ i, ∑ l, β (e i) (e' l) ^ 2 :=
        Finset.sum_congr rfl fun i _ => sum_sq_linear e e' (β (e i))
    _ = ∑ l, ∑ i, β (e i) (e' l) ^ 2 := Finset.sum_comm
    _ = ∑ l, ∑ k, β (e' k) (e' l) ^ 2 :=
        Finset.sum_congr rfl fun l _ => sum_sq_linear e e' (β.flip (e' l))
    _ = ∑ k, ∑ l, β (e' k) (e' l) ^ 2 := Finset.sum_comm

namespace SymmetricCubic

/-- The trace vector `w`, with `⟪w, x⟫ = tr L_x`. -/
def trVector (h : SymmetricCubic V) : V := riesz ((LinearMap.trace ℝ V).comp h.L)

omit [DecidableEq ι] in
theorem traceVec_apply (h : SymmetricCubic V) (i : ι) : h.traceVec e i = ⟪e i, h.trVector⟫ := by
  rw [real_inner_comm, trVector, inner_riesz, LinearMap.comp_apply, trace_eq_sum_inner e]
  simp only [traceVec, trVec, coefficient, apply]
  exact Finset.sum_congr rfl fun a _ => real_inner_comm _ _

omit [DecidableEq ι] in
/-- `|v|² = ‖w‖²`. -/
theorem vinner_traceVec (h : SymmetricCubic V) :
    vinner (h.traceVec e) (h.traceVec e) = ‖h.trVector‖ ^ 2 := by
  rw [← e.sum_sq_inner_right]; simp only [vinner, traceVec_apply, sq]

/-- The bilinear form `Σ(x,y) = 2⟪M x, y⟫ + h(x,y,w)`, the contraction `S_xykk` of the quartic. -/
def contrForm (h : SymmetricCubic V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => 2 * ⟪h.doubleContraction x, y⟫ + h.apply x y h.trVector)
    (fun x x' y => by simp only [map_add, inner_add_left, apply_add₁]; ring)
    (fun a x y => by simp only [map_smul, real_inner_smul_left, apply_smul₁, smul_eq_mul]; ring)
    (fun x y y' => by simp only [inner_add_right, apply_add₂]; ring)
    (fun a x y => by simp only [real_inner_smul_right, apply_smul₂, smul_eq_mul]; ring)

omit [DecidableEq ι] in
theorem contr_sq4_eq (h : SymmetricCubic V) (i j : ι) :
    contr (sq4 (h.coefficient e)) i j = h.contrForm (e i) (e j) := by
  rw [contr_sq4 (coefficient_symm e h)]
  simp only [contrForm, LinearMap.mk₂_apply]
  congr 1
  · rw [inner_doubleContraction_eq_sum e]; rfl
  · rw [h.apply_swap₂₃, h.apply_swap₁₂]
    conv_rhs => rw [← e.sum_repr' h.trVector]
    rw [apply_sum₁ e]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show trVec (h.coefficient e) m = h.traceVec e m from rfl, traceVec_apply]
    simp only [coefficient]
    rw [h.apply_swap₁₂ (e m), h.apply_swap₂₃ (e i) (e m), mul_comm]

/-- The Hilbert–Schmidt square `|Σ|²` of the contraction form (computed in the standard basis). -/
def contrSq (h : SymmetricCubic V) : ℝ :=
  ∑ i, ∑ j, h.contrForm (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V j) ^ 2

/-- The full trace `σ = 2x + ‖w‖²`. -/
def fullTrace (h : SymmetricCubic V) : ℝ := 2 * h.tensorPairing h + ‖h.trVector‖ ^ 2

omit [DecidableEq ι] in
theorem minner_contr_sq4 (h : SymmetricCubic V) :
    minner (contr (sq4 (h.coefficient e))) (contr (sq4 (h.coefficient e))) = h.contrSq := by
  rw [contrSq, ← sum_sq_bilinear e]
  simp only [minner, contr_sq4_eq, sq]

omit [DecidableEq ι] in
theorem sig_sq4 (h : SymmetricCubic V) : sig (sq4 (h.coefficient e)) = h.fullTrace := by
  rw [sig, mtrace_contr_sq4 (coefficient_symm e h), fullTrace, ← tensorPairing_self_eq_strength e,
    ← vinner_traceVec e]; rfl

/-- `|M̊|² = tr M² - x²/n`. -/
theorem minner_mTraceless (hn : 0 < Module.finrank ℝ V) (h : SymmetricCubic V) :
    minner (h.mTraceless e) (h.mTraceless e) =
      h.doubleTraceSq - (h.tensorPairing h) ^ 2 / Module.finrank ℝ V := by
  have hd : dim ι ≠ 0 := by rw [dim_eq_finrank e]; exact_mod_cast hn.ne'
  have := Quartic.minner_traceless (mMat (h.coefficient e)) hd
  rw [← quadSum_eq_minner (coefficient_symm e h), ← doubleTraceSq_eq e, mtrace_mMat,
    ← tensorPairing_self_eq_strength e, dim_eq_finrank e] at this
  rw [mTraceless]; linarith

/-- `|Σ̊|² = |Σ|² - σ²/n`. -/
theorem minner_sigTraceless (hn : 0 < Module.finrank ℝ V) (h : SymmetricCubic V) :
    minner (h.sigTraceless e) (h.sigTraceless e) =
      h.contrSq - h.fullTrace ^ 2 / Module.finrank ℝ V := by
  have hd : dim ι ≠ 0 := by rw [dim_eq_finrank e]; exact_mod_cast hn.ne'
  have := Quartic.minner_traceless (contr (sq4 (h.coefficient e))) hd
  rw [minner_contr_sq4, show mtrace (contr (sq4 (h.coefficient e))) = sig (sq4 (h.coefficient e))
    from rfl, sig_sq4, dim_eq_finrank e] at this
  rw [sigTraceless, sig0]; linarith

/-- `|H|² = 3 tr M² + 6P - 3σ²/(n(n+2)) - 6|Σ̊|²/(n+4)`, with `|Σ̊|² = |Σ|² - σ²/n`. -/
theorem qinner_harmQuartic (hn : 0 < Module.finrank ℝ V) (h : SymmetricCubic V) :
    qinner (h.harmQuartic e) (h.harmQuartic e) =
      3 * h.doubleTraceSq + 6 * h.tetrahedron -
        3 * h.fullTrace ^ 2 / ((Module.finrank ℝ V : ℝ) * (Module.finrank ℝ V + 2)) -
        6 * (h.contrSq - h.fullTrace ^ 2 / Module.finrank ℝ V) / ((Module.finrank ℝ V : ℝ) + 4) := by
  have hne : Nonempty ι := by
    rw [Module.finrank_eq_card_basis e.toBasis] at hn
    exact Fintype.card_pos_iff.mp hn
  have hc := coefficient_symm e h
  have := qinner_self_decomp (sq4_symm hc)
  rw [qinner_sq4 hc, ← doubleTraceSq_eq e, ← tetrahedron_eq e, sig_sq4,
    show minner (sig0 (sq4 (h.coefficient e))) (sig0 (sq4 (h.coefficient e))) =
      minner (h.sigTraceless e) (h.sigTraceless e) from rfl, minner_sigTraceless e hn,
    dim_eq_finrank e] at this
  rw [harmQuartic]; linarith

/-! Basis independence. -/

private theorem isEmpty_of_finrank {τ : Type*} [Fintype τ] (e : OrthonormalBasis τ ℝ V) (hn : Module.finrank ℝ V = 0) : IsEmpty τ := by
  rw [Module.finrank_eq_card_basis e.toBasis] at hn
  exact Fintype.card_eq_zero_iff.mp hn

omit [DecidableEq ι] [DecidableEq κ] in
/-- **Basis independence of `|v|²`.** -/
theorem traceVec_sq_basis_indep (h : SymmetricCubic V) :
    vinner (h.traceVec e) (h.traceVec e) = vinner (h.traceVec e') (h.traceVec e') := by
  rw [vinner_traceVec, vinner_traceVec]

/-- **Basis independence of `|M̊|²`.** -/
theorem mTraceless_sq_basis_indep (h : SymmetricCubic V) :
    minner (h.mTraceless e) (h.mTraceless e) = minner (h.mTraceless e') (h.mTraceless e') := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ V) with h0 | hn
  · have := isEmpty_of_finrank e h0; have := isEmpty_of_finrank e' h0; simp [minner]
  · rw [minner_mTraceless e hn, minner_mTraceless e' hn]

/-- **Basis independence of `|Σ̊|²`.** -/
theorem sigTraceless_sq_basis_indep (h : SymmetricCubic V) :
    minner (h.sigTraceless e) (h.sigTraceless e) =
      minner (h.sigTraceless e') (h.sigTraceless e') := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ V) with h0 | hn
  · have := isEmpty_of_finrank e h0; have := isEmpty_of_finrank e' h0; simp [minner]
  · rw [minner_sigTraceless e hn, minner_sigTraceless e' hn]

/-- **Basis independence of `|H|²`.** -/
theorem harmQuartic_sq_basis_indep (h : SymmetricCubic V) :
    qinner (h.harmQuartic e) (h.harmQuartic e) = qinner (h.harmQuartic e') (h.harmQuartic e') := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ V) with h0 | hn
  · have := isEmpty_of_finrank e h0; have := isEmpty_of_finrank e' h0; simp [qinner]
  · rw [qinner_harmQuartic e hn, qinner_harmQuartic e' hn]

end SymmetricCubic

end

end ThirteenPlanes
