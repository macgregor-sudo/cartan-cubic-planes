module

public import ThirteenPlanes.PencilFlow.Hessian.Gradient

@[expose] public section

set_option backward.privateInPublic true

/-! The normalized harmonic round cubic `unitRoundCubic h c` attains the floor `A* = floorValue n`. -/

open Filter Set
open scoped BigOperators RealInnerProductSpace Topology

namespace ThirteenPlanes.PencilFlow.HessianBridge

noncomputable section

open SymmetricCubic Statements Quartic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem traceless_two_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ι → ι → ℝ) (i j : ι) :
    traceless (fun a b => 2 * B a b) i j = 2 * traceless B i j := by
  simp only [traceless, mtrace, ← Finset.mul_sum]
  ring

/-- **The unit round cubic is a floor cubic.** -/
theorem unitRound_floor [Nontrivial V] {h : SymmetricCubic V} {c : ℝ} (hT : h.TraceFree)
    (hR : ThirteenPlanes.IsRound h c) :
    aFunction (unitRoundCubic h c) = floorValue (Module.finrank ℝ V) := by
  set C := unitRoundCubic h c
  set n : ℝ := (Module.finrank ℝ V : ℝ)
  let e := stdOrthonormalBasis ℝ V
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hnpos : (0 : ℝ) < n := by simp only [n]; exact_mod_cast hn
  have hc := hR.positive
  set s := Real.sqrt (2 / (c * (n + 10)))
  have hs2 : s ^ 2 = 2 / (c * (n + 10)) := Real.sq_sqrt (by positivity)
  have hCdef : C = s • h := rfl
  -- the energy is radial
  have hEn : ∀ y : V, ‖C.squareMap y‖ ^ 2 = (s ^ 2 * c) * ‖y‖ ^ 4 := by
    intro y
    rw [hCdef, squareMap_smul, norm_smul, mul_pow, hR.square_norm, Real.norm_eq_abs, sq_abs]
    ring
  -- trace vector vanishes
  have htr : C.traceVec e = 0 := by
    funext i
    have h0 := hT (e i)
    rw [trace_eq_sum_inner e] at h0
    simp only [traceVec, trVec, coefficient, Pi.zero_apply, hCdef, apply_smul]
    rw [← Finset.mul_sum]
    have : ∑ a, h.apply (e i) (e a) (e a) = ∑ a, ⟪e a, h.L (e i) (e a)⟫ :=
      Finset.sum_congr rfl fun a _ => real_inner_comm _ _
    rw [this, h0, mul_zero]
  obtain ⟨hSig, hH⟩ := (energy_const_iff e hn C).mpr ⟨_, hEn⟩
  have hcs := coefficient_symm e C
  have hv0 : trVec (C.coefficient e) = 0 := htr
  -- traceless double contraction
  have hM : C.mTraceless e = 0 := by
    have hcontr : contr (sq4 (C.coefficient e)) = fun a b => 2 * mMat (C.coefficient e) a b := by
      funext a b
      rw [contr_sq4 hcs, hv0]
      simp
    funext i j
    have := congrFun (congrFun hSig i) j
    simp only [sigTraceless, sig0, hcontr, Pi.zero_apply] at this
    rw [traceless_two_mul] at this
    simp only [mTraceless, Pi.zero_apply]
    linarith
  -- strength from a unit vector
  obtain ⟨y, hy⟩ : ∃ y : V, ‖y‖ = 1 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨‖v‖⁻¹ • v, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hdec := energy_decomp e hn C y
  simp only at hdec
  rw [show C.sigTraceless e = 0 from hSig, show C.harmQuartic e = 0 from hH, htr, hEn y, hy] at hdec
  simp only [form2, form4, Pi.zero_apply, zero_mul, Finset.sum_const_zero, vinner, mul_zero,
    add_zero, zero_div, one_pow, mul_one] at hdec
  have hx : C.tensorPairing C = floorStrength n := by
    rw [hs2] at hdec
    simp only [floorStrength]
    have h10 : n + 10 ≠ 0 := by linarith
    have h2 : n + 2 ≠ 0 := by linarith
    field_simp at hdec ⊢
    nlinarith [hdec]
  exact (aFunction_eq_floor_iff_energy e hn C).mpr ⟨hx, htr, hM, _, hEn⟩

end

end ThirteenPlanes.PencilFlow.HessianBridge
