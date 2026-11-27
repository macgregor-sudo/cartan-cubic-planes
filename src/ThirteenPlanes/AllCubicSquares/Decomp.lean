module

public import ThirteenPlanes.Quartic.Tensor

@[expose] public section

/-! Harmonic decomposition of a fully symmetric quartic array.

For a fully symmetric `T` in dimension `n ≥ 1` with full trace `σ = T_iikk` and once-contracted
traceless part `Σ̊ = contr T - (σ/n) δ`,
`T = σ/(n(n+2)) Π + 1/(n+4) δ⊙Σ̊ + H` with `H` fully symmetric and of zero trace, and
`|T|² = 3σ²/(n(n+2)) + 6|Σ̊|²/(n+4) + |H|²`. On quartic forms,
`T(φ⁴) = 3σ/(n(n+2)) |φ|⁴ + 6/(n+4) Σ̊(φ,φ)|φ|² + H(φ⁴)`. -/

open BigOperators

namespace ThirteenPlanes

noncomputable section

namespace Quartic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full trace `σ = T_iikk`. -/
def sig (T : ι → ι → ι → ι → ℝ) : ℝ := mtrace (contr T)

/-- The traceless part `Σ̊` of the contraction `Σ_ij = T_ijkk`. -/
def sig0 (T : ι → ι → ι → ι → ℝ) : ι → ι → ℝ := traceless (contr T)

/-- The totally traceless part `H = T - σ/(n(n+2)) Π - 1/(n+4) δ⊙Σ̊`. -/
def harm (T : ι → ι → ι → ι → ℝ) (i j k l : ι) : ℝ :=
  T i j k l - sig T / (dim ι * (dim ι + 2)) * piT i j k l - 1 / (dim ι + 4) * dsym (sig0 T) i j k l

/-- `Π(φ,φ,φ,φ) = 3|φ|⁴`. -/
theorem form4_piT (φ : ι → ℝ) : form4 piT φ = 3 * vinner φ φ ^ 2 := by
  simp [form4, piT, dlt, add_mul, Finset.sum_add_distrib, vinner, sq, Finset.sum_mul_sum]
  have h1 : ∀ x y, φ x * φ y * φ x * φ y = φ x * φ x * (φ y * φ y) := fun x y => by ring
  have h2 : ∀ x y, φ x * φ y * φ y * φ x = φ x * φ x * (φ y * φ y) := fun x y => by ring
  have h3 : ∀ x y, φ x * φ x * φ y * φ y = φ x * φ x * (φ y * φ y) := fun x y => by ring
  simp only [h1, h2, h3]
  ring

/-- `(δ⊙B)(φ,φ,φ,φ) = 6 B(φ,φ)|φ|²`. -/
theorem form4_dsym (B : ι → ι → ℝ) (φ : ι → ℝ) : form4 (dsym B) φ = 6 * form2 B φ * vinner φ φ := by
  set G := ∑ x, ∑ y, ∑ z, B x y * (φ x * φ y) * (φ z * φ z) with hG
  have hR : 6 * form2 B φ * vinner φ φ = 6 * G := by
    rw [mul_assoc, hG, form2, vinner]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [hR]
  simp [form4, dsym, dlt, add_mul, Finset.sum_add_distrib]
  have k1 : ∑ x, ∑ y, ∑ z, B y z * (φ x * φ x * φ y * φ z) = G := by
    rw [sum3_rot]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have k2 : ∑ x, ∑ y, ∑ z, B y z * (φ x * φ y * φ x * φ z) = G := by
    rw [sum3_rot]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have k3 : ∑ x, ∑ y, ∑ z, B y z * (φ x * φ y * φ z * φ x) = G := by
    rw [sum3_rot]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have k4 : ∑ x, ∑ y, ∑ z, B x z * (φ x * φ y * φ y * φ z) = G := by
    rw [sum3_swap23]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have k5 : ∑ x, ∑ y, ∑ z, B x z * (φ x * φ y * φ z * φ y) = G := by
    rw [sum3_swap23]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have k6 : ∑ x, ∑ y, ∑ z, B x y * (φ x * φ y * φ z * φ z) = G :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  rw [k1, k2, k3, k4, k5, k6]
  ring

theorem dim_pos [Nonempty ι] : 0 < dim ι := by
  simp only [dim]; exact_mod_cast Fintype.card_pos

theorem contr_symm {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) : MSymm (contr T) := fun i j =>
  Finset.sum_congr rfl fun k _ => hT.s12 i j k k

theorem sig0_symm {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) : MSymm (sig0 T) :=
  traceless_symm (contr_symm hT)

theorem harm_symm {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) : QSymm (harm T) :=
  hT.combo piT_symm (dsym_symm (sig0_symm hT)) _ _

theorem harm_decomp (T : ι → ι → ι → ι → ℝ) (i j k l : ι) :
    T i j k l = sig T / (dim ι * (dim ι + 2)) * piT i j k l +
      1 / (dim ι + 4) * dsym (sig0 T) i j k l + harm T i j k l := by
  simp only [harm]; ring

/-- `H` has zero trace. -/
theorem contr_harm [Nonempty ι] {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) : contr (harm T) = 0 := by
  have hn := (dim_pos (ι := ι)).ne'
  funext i j
  have : contr (harm T) i j = contr T i j - sig T / (dim ι * (dim ι + 2)) * contr piT i j -
      1 / (dim ι + 4) * contr (dsym (sig0 T)) i j := by
    simp only [contr, harm, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [this, contr_piT, contr_dsym (sig0_symm hT), show mtrace (sig0 T) = 0 from mtrace_traceless hn]
  simp only [sig0, traceless, sig]
  have h2 : dim ι + 2 ≠ 0 := by linarith [dim_pos (ι := ι)]
  have h4 : dim ι + 4 ≠ 0 := by linarith [dim_pos (ι := ι)]
  change _ = (0 : ℝ)
  field_simp
  ring

theorem minner_sig0_contr [Nonempty ι] {T : ι → ι → ι → ι → ℝ} :
    minner (sig0 T) (contr T) = minner (sig0 T) (sig0 T) := by
  have h0 : mtrace (sig0 T) = 0 := mtrace_traceless (dim_pos (ι := ι)).ne'
  have : ∀ i j, contr T i j = sig0 T i j + sig T / dim ι * dlt i j := by
    intro i j; simp only [sig0, traceless, sig]; ring
  simp only [minner, this, mul_add, Finset.sum_add_distrib]
  have hz : ∑ i, ∑ j, sig0 T i j * (sig T / dim ι * dlt i j) = 0 := by
    simp only [dlt, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.sum_mul]
    rw [show ∑ i, sig0 T i i = mtrace (sig0 T) from rfl, h0, zero_mul]
  rw [hz, add_zero]

/-- The orthogonal decomposition `|T|² = 3σ²/(n(n+2)) + 6|Σ̊|²/(n+4) + |H|²`. -/
theorem qinner_self_decomp [Nonempty ι] {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) :
    qinner T T = 3 * sig T ^ 2 / (dim ι * (dim ι + 2)) +
      6 * minner (sig0 T) (sig0 T) / (dim ι + 4) + qinner (harm T) (harm T) := by
  have hn := dim_pos (ι := ι)
  have hH := harm_symm hT
  have hc := contr_harm hT
  have hT' : (fun i j k l => sig T / (dim ι * (dim ι + 2)) * piT i j k l +
      1 / (dim ι + 4) * dsym (sig0 T) i j k l + harm T i j k l) = T := by
    funext i j k l; exact (harm_decomp T i j k l).symm
  have e1 : qinner T T = sig T / (dim ι * (dim ι + 2)) * qinner piT T +
      1 / (dim ι + 4) * qinner (dsym (sig0 T)) T + qinner (harm T) T := by
    rw [← qinner_combo, hT']
  have e2 : qinner (harm T) T = qinner (harm T) (harm T) := by
    rw [qinner_comm]
    have : qinner T (harm T) = qinner (fun i j k l => sig T / (dim ι * (dim ι + 2)) * piT i j k l +
        1 / (dim ι + 4) * dsym (sig0 T) i j k l + harm T i j k l) (harm T) := by rw [hT']
    rw [this, qinner_combo, qinner_piT hH, qinner_dsym _ hH, hc]
    simp [mtrace, minner]
  rw [e1, e2, qinner_piT hT, qinner_dsym _ hT, minner_sig0_contr]
  simp only [sig]
  have h2 : dim ι + 2 ≠ 0 := by linarith
  have h4 : dim ι + 4 ≠ 0 := by linarith
  field_simp

theorem form4_combo (X Y Z : ι → ι → ι → ι → ℝ) (a b : ℝ) (φ : ι → ℝ) :
    form4 (fun i j k l => a * X i j k l + b * Y i j k l + Z i j k l) φ =
      a * form4 X φ + b * form4 Y φ + form4 Z φ := by
  simp only [form4, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- `T(φ⁴) = 3σ/(n(n+2)) |φ|⁴ + 6/(n+4) Σ̊(φ,φ) |φ|² + H(φ⁴)`. -/
theorem form4_decomp (T : ι → ι → ι → ι → ℝ) (φ : ι → ℝ) :
    form4 T φ = 3 * sig T / (dim ι * (dim ι + 2)) * vinner φ φ ^ 2 +
      6 / (dim ι + 4) * form2 (sig0 T) φ * vinner φ φ + form4 (harm T) φ := by
  have hT' : (fun i j k l => sig T / (dim ι * (dim ι + 2)) * piT i j k l +
      1 / (dim ι + 4) * dsym (sig0 T) i j k l + harm T i j k l) = T := by
    funext i j k l; exact (harm_decomp T i j k l).symm
  rw [← hT', form4_combo, form4_piT, form4_dsym, hT']
  ring

end Quartic

end

end ThirteenPlanes
