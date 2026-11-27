module

public import ThirteenPlanes.AllCubicSquares.Decomp
public import ThirteenPlanes.Quartic.Square

@[expose] public section

/-! Polarization for symmetric quartic arrays, and direction-independence.

A fully symmetric quartic array is determined by its quartic form. Hence, in dimension `n ≥ 1`, the
quartic form of a fully symmetric `T` is a constant multiple of `|φ|⁴` exactly when `Σ̊ = 0` and
`H = 0`. -/

open BigOperators

namespace ThirteenPlanes

noncomputable section

namespace Quartic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The four-linear form of a quartic array. -/
def F4 (T : ι → ι → ι → ι → ℝ) (a b c d : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, T i j k l * (a i * b j * c k * d l)

section Linear

variable (T : ι → ι → ι → ι → ℝ) (a b c d a' : ι → ℝ) (t : ℝ)

omit [DecidableEq ι]

theorem F4_lin1 : F4 T (fun i => a i + t * a' i) b c d = F4 T a b c d + t * F4 T a' b c d := by
  simp only [F4, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem F4_lin2 : F4 T b (fun i => a i + t * a' i) c d = F4 T b a c d + t * F4 T b a' c d := by
  simp only [F4, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem F4_lin3 : F4 T b c (fun i => a i + t * a' i) d = F4 T b c a d + t * F4 T b c a' d := by
  simp only [F4, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem F4_lin4 : F4 T b c d (fun i => a i + t * a' i) = F4 T b c d a + t * F4 T b c d a' := by
  simp only [F4, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end Linear

section Swap

variable {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) (a b c d : ι → ℝ)
include hT

omit [DecidableEq ι]

theorem F4_swap12 : F4 T a b c d = F4 T b a c d := by
  simp only [F4]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hT.s12 i j k l]; ring

theorem F4_swap23 : F4 T a b c d = F4 T a c b d := by
  simp only [F4]
  rw [sum4_swap23]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hT.s23 i k j l]; ring

theorem F4_swap34 : F4 T a b c d = F4 T a b d c := by
  simp only [F4]
  rw [sum4_swap34]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hT.s34 i j l k]; ring

end Swap

omit [DecidableEq ι] in
/-- The binomial expansion of the quartic form along a line. -/
theorem form4_line {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) (p q : ι → ℝ) (t : ℝ) :
    form4 T (fun i => p i + t * q i) = form4 T p + 4 * t * F4 T p p p q +
      6 * t ^ 2 * F4 T p p q q + 4 * t ^ 3 * F4 T p q q q + t ^ 4 * form4 T q := by
  change F4 T _ _ _ _ = F4 T p p p p + _ + _ + _ + _ * F4 T q q q q
  simp only [F4_lin1, F4_lin2, F4_lin3, F4_lin4]
  have s := F4_swap12 hT
  have u := F4_swap23 hT
  have w := F4_swap34 hT
  have c1 : F4 T q q p p = F4 T p p q q :=
    (u q q p p).trans ((s q p q p).trans ((w p q q p).trans (u p q p q)))
  have c2 : F4 T q p q p = F4 T p p q q := (s q p q p).trans ((w p q q p).trans (u p q p q))
  have c3 : F4 T q q q p = F4 T p q q q := (w q q q p).trans ((u q q p q).trans (s q p q q))
  have c4 : F4 T q p p q = F4 T p p q q := (s q p p q).trans (u p q p q)
  have c5 : F4 T q q p q = F4 T p q q q := (u q q p q).trans (s q p q q)
  have c6 : F4 T q p q q = F4 T p q q q := s q p q q
  have c7 : F4 T q p p p = F4 T p p p q := (s q p p p).trans ((u p q p p).trans (w p p q p))
  have c8 : F4 T p q p p = F4 T p p p q := (u p q p p).trans (w p p q p)
  have c9 : F4 T p p q p = F4 T p p p q := w p p q p
  have c10 : F4 T p q q p = F4 T p p q q := (w p q q p).trans (u p q p q)
  have c11 : F4 T p q p q = F4 T p p q q := u p q p q
  rw [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11]
  ring

omit [DecidableEq ι] in
/-- A fully symmetric quartic array with vanishing quartic form is zero. -/
theorem eq_zero_of_form4 {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) (h0 : ∀ φ, form4 T φ = 0) :
    T = 0 := by
  have step1 : ∀ p q, F4 T p p q q = 0 := by
    intro p q
    have e := fun t => form4_line hT p q t
    have h1 := e 1; have h2 := e (-1); have h3 := e 2
    rw [h0, h0, h0] at h1 h2 h3
    nlinarith
  have step2 : ∀ a b q, F4 T a b q q = 0 := by
    intro a b q
    have := step1 (fun i => a i + 1 * b i) q
    rw [F4_lin1, F4_lin2, F4_lin2, step1, step1] at this
    linarith [F4_swap12 hT a b q q]
  have step3 : ∀ a b c d, F4 T a b c d = 0 := by
    intro a b c d
    have := step2 a b (fun i => c i + 1 * d i)
    rw [F4_lin3, F4_lin4, F4_lin4, step2, step2] at this
    linarith [F4_swap34 hT a b c d]
  classical
  funext i j k l
  have := step3 (fun x => if x = i then 1 else 0) (fun x => if x = j then 1 else 0)
    (fun x => if x = k then 1 else 0) (fun x => if x = l then 1 else 0)
  simpa [F4] using this

/-- Direction-independence: the quartic form of `T` is a constant multiple of `|φ|⁴` exactly when
the traceless contraction `Σ̊` and the totally traceless part `H` vanish. -/
theorem form4_const_iff [Nonempty ι] {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) :
    (sig0 T = 0 ∧ harm T = 0) ↔ ∃ a : ℝ, ∀ φ, form4 T φ = a * vinner φ φ ^ 2 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨3 * sig T / (dim ι * (dim ι + 2)), fun φ => ?_⟩
    rw [form4_decomp, h1, h2]
    simp [form4, form2]
  · rintro ⟨a, ha⟩
    have hn := dim_pos (ι := ι)
    have hT' : QSymm (fun i j k l => T i j k l - a / 3 * piT i j k l - 0 * piT i j k l) :=
      hT.combo piT_symm piT_symm _ _
    have hz := eq_zero_of_form4 hT' fun φ => by
      have : form4 (fun i j k l => T i j k l - a / 3 * piT i j k l - 0 * piT i j k l) φ =
          form4 T φ - a / 3 * form4 piT φ := by
        simp only [form4, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
        ring
      rw [this, ha, form4_piT]; ring
    have hTe : T = fun i j k l => a / 3 * piT i j k l := by
      funext i j k l
      have := congrFun (congrFun (congrFun (congrFun hz i) j) k) l
      simp only [Pi.zero_apply] at this
      linarith
    subst hTe
    have hc : ∀ i j, contr (fun i j k l => a / 3 * piT (ι := ι) i j k l) i j =
        a / 3 * ((dim ι + 2) * dlt i j) := by
      intro i j; rw [← contr_piT]; simp only [contr, Finset.mul_sum]
    have hs : sig (fun i j k l => a / 3 * piT (ι := ι) i j k l) = a / 3 * (dim ι + 2) * dim ι := by
      simp only [sig, mtrace, hc, dlt_self, mul_one, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [show (Fintype.card ι : ℝ) = dim ι from rfl]; ring
    have h0 : sig0 (fun i j k l => a / 3 * piT (ι := ι) i j k l) = 0 := by
      funext i j
      simp only [sig0, traceless, hc, Pi.zero_apply]
      rw [show mtrace (contr fun i j k l => a / 3 * piT (ι := ι) i j k l) = _ from hs]
      field_simp; ring
    refine ⟨h0, ?_⟩
    funext i j k l
    simp only [harm, h0, hs, Pi.zero_apply]
    simp only [dsym, Pi.zero_apply, mul_zero, add_zero]
    have h2 : dim ι + 2 ≠ 0 := by linarith
    field_simp
    ring

end Quartic

end

end ThirteenPlanes
