module

public import ThirteenPlanes.AllCubicSquares.Polar
public import ThirteenPlanes.Quartic

@[expose] public section

/-! The A-function over all real symmetric cubics: its floor plus five squares.

For a real symmetric cubic `h` on a real inner product space of dimension `n ≥ 1`, in any orthonormal
basis `e`, with `x = ⟨h,h⟩`, trace vector `v`, traceless double contraction `M̊`, traceless
contraction `Σ̊` of the symmetrized quartic tensor `S` and its totally traceless part `H`,

  `A(h) - A* = (n+10)/(8n(n+2)) (x - x*)² + |v|²(4x+|v|²)/(4n(n+2)) + |M̊|²/8
               + |Σ̊|²/(2(n+4)) + |H|²/12`,

with `x* = n(n+2)/(n+10)` and `A* = -x*/8`. Hence `A ≥ A*`, with equality exactly when `x = x*`,
`v = 0`, `M̊ = 0`, `Σ̊ = 0` and `H = 0`; the last two together say that the field energy `‖Q_h(y)‖²`
is a constant multiple of `‖y‖⁴`. The sphere-average form of the last two squares,
`Var₂ = |Σ̊|²/(8n(n+2)(n+4)²)` and `Var₄ = |H|²/(24n(n+2)(n+4)(n+6))`, is not proved here; the pointwise
harmonic splitting of the energy that it starts from is `energy_decomp`. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open Quartic

/-- The floor strength `x* = n(n+2)/(n+10)`. -/
def floorStrength (n : ℝ) : ℝ := n * (n + 2) / (n + 10)

/-- The floor `A* = -x*/8`. -/
def floorValue (n : ℝ) : ℝ := -floorStrength n / 8

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

namespace SymmetricCubic

/-- The trace vector `v_i = h_iaa` in the basis `e`. -/
def traceVec (h : SymmetricCubic V) : ι → ℝ := trVec (h.coefficient e)

/-- The traceless part `M̊` of the double contraction, in the basis `e`. -/
def mTraceless (h : SymmetricCubic V) : ι → ι → ℝ := traceless (mMat (h.coefficient e))

/-- The traceless part `Σ̊` of the contraction `S_ijkk` of the symmetrized quartic tensor. -/
def sigTraceless (h : SymmetricCubic V) : ι → ι → ℝ := sig0 (sq4 (h.coefficient e))

/-- The totally traceless part `H` of the symmetrized quartic tensor. -/
def harmQuartic (h : SymmetricCubic V) : ι → ι → ι → ι → ℝ := harm (sq4 (h.coefficient e))

end SymmetricCubic

open SymmetricCubic

omit [DecidableEq ι] in
include e in
theorem dim_eq_finrank : dim ι = (Module.finrank ℝ V : ℝ) := by
  rw [Module.finrank_eq_card_basis e.toBasis]; rfl

/-! Sums of squares. -/

theorem Quartic.minner_traceless (B : ι → ι → ℝ) (hn : dim ι ≠ 0) :
    minner B B = minner (traceless B) (traceless B) + mtrace B ^ 2 / dim ι := by
  have hd : ∀ i j : ι, dlt i j * dlt i j = dlt i j := fun i j => by
    unfold dlt; split_ifs <;> norm_num
  have : ∀ i j, traceless B i j * traceless B i j = B i j * B i j -
      2 * (mtrace B / dim ι) * (dlt i j * B i j) + (mtrace B / dim ι) ^ 2 * dlt i j := by
    intro i j; simp only [traceless, dlt]; split_ifs <;> ring
  simp only [minner, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_dlt_mul]
  simp only [dlt, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [show (Fintype.card ι : ℝ) = dim ι from rfl, show ∑ i, B i i = mtrace B from rfl]
  field_simp
  ring

omit [DecidableEq ι] in
theorem Quartic.minner_self_nonneg (B : ι → ι → ℝ) : 0 ≤ minner B B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

omit [DecidableEq ι] in
theorem Quartic.minner_self_eq_zero (B : ι → ι → ℝ) : minner B B = 0 ↔ B = 0 := by
  constructor
  · intro h
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_self_nonneg (B i j)).mp h
    funext i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (B i j)).mp
      (h1 i (Finset.mem_univ _)) j (Finset.mem_univ _)
    exact mul_self_eq_zero.mp h2
  · rintro rfl; simp [minner]

omit [DecidableEq ι] in
theorem Quartic.vinner_self_nonneg (u : ι → ℝ) : 0 ≤ vinner u u :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

omit [DecidableEq ι] in
theorem Quartic.vinner_self_eq_zero (u : ι → ℝ) : vinner u u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext i
    exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_self_nonneg (u i)).mp h i (Finset.mem_univ _))
  · rintro rfl; simp [vinner]

omit [DecidableEq ι] in
theorem Quartic.qinner_self_nonneg (T : ι → ι → ι → ι → ℝ) : 0 ≤ qinner T T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => mul_self_nonneg _

omit [DecidableEq ι] in
theorem Quartic.qinner_self_eq_zero (T : ι → ι → ι → ι → ℝ) : qinner T T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have nn : ∀ i j k, 0 ≤ ∑ l, T i j k l * T i j k l := fun _ _ _ =>
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    have nn2 : ∀ i j, 0 ≤ ∑ k, ∑ l, T i j k l * T i j k l := fun _ _ =>
      Finset.sum_nonneg fun _ _ => nn _ _ _
    have nn3 : ∀ i, 0 ≤ ∑ j, ∑ k, ∑ l, T i j k l * T i j k l := fun _ =>
      Finset.sum_nonneg fun _ _ => nn2 _ _
    funext i j k l
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => nn3 i).mp h i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => nn2 i j).mp h1 j (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => nn i j k).mp h2 k (Finset.mem_univ _)
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => mul_self_nonneg (T i j k l)).mp h3 l
      (Finset.mem_univ _)
    exact mul_self_eq_zero.mp h4
  · rintro rfl; simp [qinner]

/-! The identity, the bound and the equality case. -/

/-- **Five squares.** For every real symmetric cubic in dimension `n ≥ 1` and every orthonormal
basis, `A(h) - A*` is the sum of the five nonnegative terms
`(n+10)/(8n(n+2)) (x-x*)²`, `|v|²(4x+|v|²)/(4n(n+2))`, `|M̊|²/8`, `|Σ̊|²/(2(n+4))` and `|H|²/12`. -/
theorem aFunction_sub_floor (hn : 0 < Module.finrank ℝ V) (h : SymmetricCubic V) :
    let n : ℝ := Module.finrank ℝ V
    let x := h.tensorPairing h
    let w := vinner (h.traceVec e) (h.traceVec e)
    aFunction h - floorValue n =
      (n + 10) / (8 * n * (n + 2)) * (x - floorStrength n) ^ 2 +
        w * (4 * x + w) / (4 * n * (n + 2)) +
        minner (h.mTraceless e) (h.mTraceless e) / 8 +
        minner (h.sigTraceless e) (h.sigTraceless e) / (2 * (n + 4)) +
        qinner (h.harmQuartic e) (h.harmQuartic e) / 12 := by
  intro n x w
  simp only [x, w, SymmetricCubic.mTraceless, SymmetricCubic.sigTraceless,
    SymmetricCubic.harmQuartic, SymmetricCubic.traceVec]
  have hne : Nonempty ι := by
    rw [Module.finrank_eq_card_basis e.toBasis] at hn
    exact Fintype.card_pos_iff.mp hn
  have hdim : dim ι = n := dim_eq_finrank e
  have hpos : 0 < n := by rw [← hdim]; exact dim_pos
  have hc := coefficient_symm e h
  rw [aFunction_eq_quartic e, tensorPairing_self_eq_strength e h, qinner_self_decomp (sq4_symm hc),
    doubleTraceSq_eq_minner e, minner_traceless _ (by rw [hdim]; exact hpos.ne')]
  simp only [sig]
  rw [mtrace_contr_sq4 hc, mtrace_mMat, hdim]
  simp only [floorValue, floorStrength]
  have h2 : n + 2 ≠ 0 := by linarith
  have h4 : n + 4 ≠ 0 := by linarith
  have h10 : n + 10 ≠ 0 := by linarith
  field_simp
  ring

include e in
/-- The floor bound, proved in a given orthonormal basis. -/
theorem floorValue_le_aFunction_of_basis (hn : 0 < Module.finrank ℝ V) (h : SymmetricCubic V) :
    floorValue (Module.finrank ℝ V) ≤ aFunction h := by
  have key := aFunction_sub_floor e hn h
  simp only at key
  have hpos : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast hn
  have hx : 0 ≤ h.tensorPairing h := by
    rw [tensorPairing_self_eq_strength e]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg
      fun _ _ => mul_self_nonneg _
  have hw := vinner_self_nonneg (h.traceVec e)
  have t1 : 0 ≤ ((Module.finrank ℝ V : ℝ) + 10) / (8 * Module.finrank ℝ V *
      (Module.finrank ℝ V + 2)) * (h.tensorPairing h - floorStrength (Module.finrank ℝ V)) ^ 2 := by
    positivity
  have t2 : 0 ≤ vinner (h.traceVec e) (h.traceVec e) * (4 * h.tensorPairing h +
      vinner (h.traceVec e) (h.traceVec e)) / (4 * Module.finrank ℝ V * (Module.finrank ℝ V + 2)) := by
    apply div_nonneg (mul_nonneg hw (by linarith)); positivity
  have t3 := minner_self_nonneg (h.mTraceless e)
  have t4 : 0 ≤ minner (h.sigTraceless e) (h.sigTraceless e) / (2 * (Module.finrank ℝ V + 4)) :=
    div_nonneg (minner_self_nonneg _) (by positivity)
  have t5 := qinner_self_nonneg (h.harmQuartic e)
  linarith

/-- **Floor bound.** `A(h) ≥ A* = -n(n+2)/(8(n+10))` for every real symmetric cubic in dimension
`n ≥ 1`. -/
theorem floorValue_le_aFunction (hn : 0 < Module.finrank ℝ V) (h : SymmetricCubic V) :
    floorValue (Module.finrank ℝ V) ≤ aFunction h :=
  floorValue_le_aFunction_of_basis (stdOrthonormalBasis ℝ V) hn h

/-- **Equality case, algebraic form.** `A(h) = A*` exactly when `x = x*`, the trace vector vanishes,
`M` is scalar (`M̊ = 0`), and `Σ̊ = 0` and `H = 0`. -/
theorem aFunction_eq_floor_iff (hn : 0 < Module.finrank ℝ V) (h : SymmetricCubic V) :
    aFunction h = floorValue (Module.finrank ℝ V) ↔
      h.tensorPairing h = floorStrength (Module.finrank ℝ V) ∧ h.traceVec e = 0 ∧
        h.mTraceless e = 0 ∧ h.sigTraceless e = 0 ∧ h.harmQuartic e = 0 := by
  have key := aFunction_sub_floor e hn h
  simp only at key
  set n : ℝ := (Module.finrank ℝ V : ℝ)
  have hpos : (0 : ℝ) < n := by simp only [n]; exact_mod_cast hn
  have hx : 0 ≤ h.tensorPairing h := by
    rw [tensorPairing_self_eq_strength e]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg
      fun _ _ => mul_self_nonneg _
  set x := h.tensorPairing h
  set w := vinner (h.traceVec e) (h.traceVec e)
  have hw : 0 ≤ w := vinner_self_nonneg _
  have a1 : 0 < (n + 10) / (8 * n * (n + 2)) := by positivity
  have t1 : 0 ≤ (n + 10) / (8 * n * (n + 2)) * (x - floorStrength n) ^ 2 := by positivity
  have t2 : 0 ≤ w * (4 * x + w) / (4 * n * (n + 2)) := by
    apply div_nonneg (mul_nonneg hw (by linarith)); positivity
  have t3 := minner_self_nonneg (h.mTraceless e)
  have t4 : 0 ≤ minner (h.sigTraceless e) (h.sigTraceless e) / (2 * (n + 4)) :=
    div_nonneg (minner_self_nonneg _) (by positivity)
  have t5 := qinner_self_nonneg (h.harmQuartic e)
  constructor
  · intro hA
    rw [hA, sub_self] at key
    have z1 : (n + 10) / (8 * n * (n + 2)) * (x - floorStrength n) ^ 2 = 0 := by linarith
    have z2 : w * (4 * x + w) / (4 * n * (n + 2)) = 0 := by linarith
    have z3 : minner (h.mTraceless e) (h.mTraceless e) = 0 := by linarith
    have z4 : minner (h.sigTraceless e) (h.sigTraceless e) / (2 * (n + 4)) = 0 := by linarith
    have z5 : qinner (h.harmQuartic e) (h.harmQuartic e) = 0 := by linarith
    refine ⟨?_, ?_, (minner_self_eq_zero _).mp z3, ?_, (qinner_self_eq_zero _).mp z5⟩
    · have := (mul_eq_zero.mp z1).resolve_left a1.ne'
      nlinarith [sq_nonneg (x - floorStrength n)]
    · apply (vinner_self_eq_zero _).mp
      have hd : (4 * n * (n + 2)) ≠ 0 := by positivity
      have := (div_eq_zero_iff.mp z2).resolve_right hd
      rcases mul_eq_zero.mp this with h0 | h0
      · exact h0
      · linarith
    · apply (minner_self_eq_zero _).mp
      exact (div_eq_zero_iff.mp z4).resolve_right (by positivity)
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have : w = 0 := by simp only [w, h2, vinner, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    rw [h1, this, h3, h4, h5] at key
    simp [minner, qinner] at key
    linarith

/-- The field energy `‖Q_h(y)‖²` is a constant multiple of `‖y‖⁴` exactly when `Σ̊ = 0` and `H = 0`. -/
theorem energy_const_iff (hn : 0 < Module.finrank ℝ V) (h : SymmetricCubic V) :
    (h.sigTraceless e = 0 ∧ h.harmQuartic e = 0) ↔
      ∃ a : ℝ, ∀ y : V, ‖h.squareMap y‖ ^ 2 = a * ‖y‖ ^ 4 := by
  have hne : Nonempty ι := by
    rw [Module.finrank_eq_card_basis e.toBasis] at hn
    exact Fintype.card_pos_iff.mp hn
  have hnorm : ∀ y : V, vinner (fun i => ⟪e i, y⟫) (fun i => ⟪e i, y⟫) = ‖y‖ ^ 2 := by
    intro y; rw [← e.sum_sq_inner_right]; simp only [vinner, sq]
  rw [show h.sigTraceless e = sig0 (sq4 (h.coefficient e)) from rfl,
    show h.harmQuartic e = harm (sq4 (h.coefficient e)) from rfl,
    form4_const_iff (sq4_symm (coefficient_symm e h))]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a / 3, fun y => ?_⟩
    rw [norm_squareMap_sq_eq_form4 e, ha, hnorm]; ring
  · rintro ⟨a, ha⟩
    refine ⟨3 * a, fun φ => ?_⟩
    let y : V := e.repr.symm (WithLp.toLp 2 φ)
    have hy : (fun i => ⟪e i, y⟫) = φ := by
      funext i; rw [← e.repr_apply_apply]; simp [y]
    have := ha y
    rw [norm_squareMap_sq_eq_form4 e, hy, show ‖y‖ ^ 4 = (‖y‖ ^ 2) ^ 2 by ring, ← hnorm y,
      hy] at this
    linarith

/-- **Equality case, as in the paper.** `A(h) = A*` exactly when `x = x*`, the trace vector vanishes,
`M` is scalar, and the field energy is the same in every direction (`‖Q_h(y)‖² = a‖y‖⁴`). -/
theorem aFunction_eq_floor_iff_energy (hn : 0 < Module.finrank ℝ V) (h : SymmetricCubic V) :
    aFunction h = floorValue (Module.finrank ℝ V) ↔
      h.tensorPairing h = floorStrength (Module.finrank ℝ V) ∧ h.traceVec e = 0 ∧
        h.mTraceless e = 0 ∧ ∃ a : ℝ, ∀ y : V, ‖h.squareMap y‖ ^ 2 = a * ‖y‖ ^ 4 := by
  rw [aFunction_eq_floor_iff e hn, ← energy_const_iff e hn]

/-- The pointwise harmonic splitting of the field energy `U = ‖Q_h(y)‖²/8`:
`U = σ/(8n(n+2)) ‖y‖⁴ + Σ̊(φ,φ) ‖y‖²/(4(n+4)) + H(φ⁴)/24`, with `φ_i = ⟪e i, y⟫` and `σ = 2x + |v|²`. -/
theorem energy_decomp (hn : 0 < Module.finrank ℝ V) (h : SymmetricCubic V) (y : V) :
    let n : ℝ := Module.finrank ℝ V
    ‖h.squareMap y‖ ^ 2 / 8 =
      (2 * h.tensorPairing h + vinner (h.traceVec e) (h.traceVec e)) / (8 * n * (n + 2)) * ‖y‖ ^ 4 +
        form2 (h.sigTraceless e) (fun i => ⟪e i, y⟫) * ‖y‖ ^ 2 / (4 * (n + 4)) +
        form4 (h.harmQuartic e) (fun i => ⟪e i, y⟫) / 24 := by
  intro n
  simp only [SymmetricCubic.sigTraceless, SymmetricCubic.harmQuartic, SymmetricCubic.traceVec]
  have hdim : dim ι = n := dim_eq_finrank e
  have hpos : (0 : ℝ) < n := by simp only [n]; exact_mod_cast hn
  have hnorm : vinner (fun i => ⟪e i, y⟫) (fun i => ⟪e i, y⟫) = ‖y‖ ^ 2 := by
    rw [← e.sum_sq_inner_right]; simp only [vinner, sq]
  rw [norm_squareMap_sq_eq_form4 e, form4_decomp, hnorm, hdim]
  simp only [sig]
  rw [mtrace_contr_sq4 (coefficient_symm e h), ← tensorPairing_self_eq_strength e]
  have h2 : n + 2 ≠ 0 := by linarith
  have h4 : n + 4 ≠ 0 := by linarith
  field_simp
  ring

end

end ThirteenPlanes
