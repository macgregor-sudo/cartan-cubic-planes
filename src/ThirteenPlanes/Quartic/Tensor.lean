module

public import ThirteenPlanes.Quartic.Defs

@[expose] public section

/-! Projector identities for quartic arrays.

For a fully symmetric quartic array `T`: `⟨Π, T⟩ = 3 tr(contr T)` and
`⟨δ ⊙ B, T⟩ = 6 ⟨B, contr T⟩`. With `contr Π = (n+2) δ` and `contr (δ ⊙ B) = (n+4) B + (tr B) δ` this
gives `|Π|² = 3n(n+2)`, `⟨Π, δ ⊙ B⟩ = 0` and `|δ ⊙ B|² = 6(n+4)|B|²` for traceless symmetric `B`. -/

open BigOperators

namespace ThirteenPlanes

noncomputable section

namespace Quartic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem dlt_comm (i j : ι) : dlt i j = dlt j i := by simp [dlt, eq_comm]

omit [Fintype ι] in
@[simp] theorem dlt_self (i : ι) : dlt i i = 1 := by simp [dlt]

theorem sum_dlt_mul (i : ι) (f : ι → ℝ) : ∑ j, dlt i j * f j = f i := by simp [dlt]

theorem sum_mul_dlt' (i : ι) (f : ι → ℝ) : ∑ j, dlt j i * f j = f i := by simp [dlt]

theorem sum_dlt_self : ∑ i : ι, dlt i i = dim ι := by simp [dim]

/-! Index bookkeeping. -/

omit [DecidableEq ι] in
theorem sum3_rot (f : ι → ι → ι → ℝ) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ y, ∑ z, ∑ x, f x y z := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

omit [DecidableEq ι] in
theorem sum3_swap23 (f : ι → ι → ι → ℝ) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ z, ∑ y, f x y z :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

namespace QSymm

variable {T : ι → ι → ι → ι → ℝ}

omit [Fintype ι] [DecidableEq ι]

theorem pair (hT : QSymm T) (a b c d : ι) : T a b c d = T c d a b :=
  (hT.s23 a b c d).trans <| (hT.s12 a c b d).trans <| (hT.s34 c a b d).trans (hT.s23 c a d b)

theorem s13 (hT : QSymm T) (a b c d : ι) : T a b c d = T c b a d := by
  rw [hT.s12 a b c d, hT.s23 b a c d, hT.s12 b c a d]

theorem s14 (hT : QSymm T) (a b c d : ι) : T a b c d = T d b c a := by
  rw [hT.s34 a b c d, hT.s23 a b d c, hT.s12 a d b c, hT.s23 d a b c, hT.s34 d b a c]

theorem s24 (hT : QSymm T) (a b c d : ι) : T a b c d = T a d c b := by
  rw [hT.s34 a b c d, hT.s23 a b d c, hT.s34 a d b c]

end QSymm

/-! Symmetry of `Π` and `δ ⊙ B`. -/

theorem piT_symm : QSymm (piT (ι := ι)) := by
  refine ⟨fun i j k l => ?_, fun i j k l => ?_, fun i j k l => ?_⟩ <;>
    simp only [piT, dlt_comm i j, dlt_comm i k, dlt_comm i l, dlt_comm j k, dlt_comm j l,
      dlt_comm k l] <;> ring

theorem dsym_symm {B : ι → ι → ℝ} (hB : MSymm B) : QSymm (dsym B) := by
  refine ⟨fun i j k l => ?_, fun i j k l => ?_, fun i j k l => ?_⟩ <;>
    simp only [dsym, dlt_comm j i, dlt_comm k i, dlt_comm l i, dlt_comm k j, dlt_comm l j,
      dlt_comm l k, hB j i, hB k i, hB l i, hB k j, hB l j, hB l k] <;> ring

theorem QSymm.combo {T X Y : ι → ι → ι → ι → ℝ} (hT : QSymm T) (hX : QSymm X) (hY : QSymm Y)
    (a b : ℝ) : QSymm (fun i j k l => T i j k l - a * X i j k l - b * Y i j k l) := by
  refine ⟨fun i j k l => ?_, fun i j k l => ?_, fun i j k l => ?_⟩
  · simp only [hT.s12 i j k l, hX.s12 i j k l, hY.s12 i j k l]
  · simp only [hT.s23 i j k l, hX.s23 i j k l, hY.s23 i j k l]
  · simp only [hT.s34 i j k l, hX.s34 i j k l, hY.s34 i j k l]

/-! Contractions. -/

theorem contr_piT (i j : ι) : contr (piT (ι := ι)) i j = (dim ι + 2) * dlt i j := by
  simp only [contr, piT, dlt, Finset.sum_add_distrib, dim]
  simp
  split_ifs <;> ring

theorem contr_dsym {B : ι → ι → ℝ} (hB : MSymm B) (i j : ι) :
    contr (dsym B) i j = (dim ι + 4) * B i j + mtrace B * dlt i j := by
  simp only [contr, dsym, Finset.sum_add_distrib, mtrace, dim]
  simp [dlt, hB j i]
  split_ifs <;> ring

theorem mtrace_traceless {B : ι → ι → ℝ} (hn : dim ι ≠ 0) : mtrace (traceless B) = 0 := by
  simp only [mtrace, traceless, Finset.sum_sub_distrib, dlt_self, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [show (Fintype.card ι : ℝ) = dim ι from rfl]
  field_simp
  ring

theorem traceless_symm {B : ι → ι → ℝ} (hB : MSymm B) : MSymm (traceless B) := by
  intro i j
  simp only [traceless, hB i j, dlt_comm i j]

/-! Inner products against fully symmetric arrays. -/

theorem qinner_piT {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) :
    qinner piT T = 3 * mtrace (contr T) := by
  simp [qinner, piT, dlt, add_mul, Finset.sum_add_distrib, mtrace, contr]
  have h1 : ∀ x y, T x y x y = T x x y y := fun x y => hT.s23 x y x y
  have h2 : ∀ x y, T x y y x = T x x y y := fun x y => (hT.s34 x y y x).trans (hT.s23 x y x y)
  simp only [h1, h2]
  ring

theorem qinner_dsym (B : ι → ι → ℝ) {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) :
    qinner (dsym B) T = 6 * minner B (contr T) := by
  simp only [qinner, dsym, dlt, add_mul, Finset.sum_add_distrib, minner, contr]
  simp
  have ha : ∀ x y z, T x x y z = T y z x x := fun x y z => hT.pair x x y z
  have hb : ∀ x y z, T x y x z = T y z x x := fun x y z =>
    (hT.s12 x y x z).trans <| (hT.s34 y x x z).trans (hT.s23 y x z x)
  have hc : ∀ x y z, T x y z x = T y z x x := fun x y z =>
    (hT.s12 x y z x).trans (hT.s23 y x z x)
  have hd : ∀ x y z, T x y y z = T x z y y := fun x y z =>
    (hT.s34 x y y z).trans (hT.s23 x y z y)
  have he : ∀ x y z, T x y z y = T x z y y := fun x y z => hT.s23 x y z y
  have k1 : ∑ x, ∑ y, ∑ z, B y z * T x x y z = minner B (contr T) := by
    rw [sum3_rot]; simp only [minner, contr, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun x _ => by rw [ha]
  have k2 : ∑ x, ∑ y, ∑ z, B y z * T x y x z = minner B (contr T) := by
    rw [sum3_rot]; simp only [minner, contr, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun x _ => by rw [hb]
  have k3 : ∑ x, ∑ y, ∑ z, B y z * T x y z x = minner B (contr T) := by
    rw [sum3_rot]; simp only [minner, contr, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun x _ => by rw [hc]
  have k4 : ∑ x, ∑ y, ∑ z, B x z * T x y y z = minner B (contr T) := by
    rw [sum3_swap23]; simp only [minner, contr, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun y _ => by rw [hd]
  have k5 : ∑ x, ∑ y, ∑ z, B x z * T x y z y = minner B (contr T) := by
    rw [sum3_swap23]; simp only [minner, contr, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun y _ => by rw [he]
  have k6 : ∑ x, ∑ y, ∑ z, B x y * T x y z z = minner B (contr T) := by
    simp only [minner, contr, Finset.mul_sum]
  rw [k1, k2, k3, k4, k5, k6]; simp only [minner, contr]
  ring

/-! Norms. -/

theorem qinner_piT_piT : qinner (piT (ι := ι)) piT = 3 * dim ι * (dim ι + 2) := by
  rw [qinner_piT piT_symm]
  simp only [mtrace, contr_piT, dlt_self, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [show (Fintype.card ι : ℝ) = dim ι from rfl]
  ring

theorem qinner_piT_dsym {B : ι → ι → ℝ} (hB : MSymm B) (h0 : mtrace B = 0) :
    qinner piT (dsym B) = 0 := by
  rw [qinner_piT (dsym_symm hB)]
  simp only [mtrace, contr_dsym hB, dlt_self, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [show ∑ i, B i i = mtrace B from rfl, h0]
  simp

theorem qinner_dsym_dsym {B : ι → ι → ℝ} (hB : MSymm B) (h0 : mtrace B = 0) :
    qinner (dsym B) (dsym B) = 6 * (dim ι + 4) * minner B B := by
  rw [qinner_dsym B (dsym_symm hB)]
  simp only [minner, contr_dsym hB, h0, zero_mul, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-! Linearity. -/

theorem qinner_comm (A B : ι → ι → ι → ι → ℝ) : qinner A B = qinner B A := by
  simp only [qinner, mul_comm]

theorem qinner_combo (X Y Z W : ι → ι → ι → ι → ℝ) (a b : ℝ) :
    qinner (fun i j k l => a * X i j k l + b * Y i j k l + Z i j k l) W =
      a * qinner X W + b * qinner Y W + qinner Z W := by
  simp only [qinner, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end Quartic

end

end ThirteenPlanes
