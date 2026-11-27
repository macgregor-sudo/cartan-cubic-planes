module

public import ThirteenPlanes.AlbertGrading.Grading.Complexification

@[expose] public section

set_option backward.privateInPublic true

/-! # The graded quartic identity `(5-quartic)`

For traceless `a, b, c, d` of the compact Albert algebra and of its complexification,
`⟨a∘b,c∘d⟩ + ⟨a∘c,b∘d⟩ + ⟨a∘d,b∘c⟩ = ½(⟨a,b⟩⟨c,d⟩ + ⟨a,c⟩⟨b,d⟩ + ⟨a,d⟩⟨b,c⟩)`.
The real case is the polarized square law of the traceless trace cubic
(`HasSquareLaw.polarized` with `nativeEqualCubic_squareLaw`); the complex case follows
by multilinearity. -/

namespace ThirteenPlanes.AlbertGrading.Grading

open Glennie RealInnerProductSpace

noncomputable section

private theorem inner_center (u v : Glennie.Albert) :
    Glennie.inner (Glennie.traceless u) (Glennie.traceless v) =
      Glennie.inner u v - Glennie.trace u * Glennie.trace v / 3 := by
  rw [Glennie.traceless, Glennie.traceless, Glennie.inner_sub_left, Glennie.inner_sub_right,
    Glennie.inner_sub_right, Glennie.inner_smul_left, Glennie.inner_smul_left,
    Glennie.inner_smul_right, Glennie.inner_smul_right, nativeInner_one_left,
    nativeInner_one_right, nativeInner_one_right, Glennie.trace_unit]
  ring

/-- The real quartic identity on traceless elements. -/
theorem real_quartic (a b c d : Glennie.Albert) (ha : Glennie.trace a = 0)
    (hb : Glennie.trace b = 0) (hc : Glennie.trace c = 0) (hd : Glennie.trace d = 0) :
    Glennie.inner (jordan a b) (jordan c d) + Glennie.inner (jordan a c) (jordan b d) +
        Glennie.inner (jordan a d) (jordan b c) =
      (Glennie.inner a b * Glennie.inner c d + Glennie.inner a c * Glennie.inner b d +
        Glennie.inner a d * Glennie.inner b c) / 2 := by
  let A : NativeTraceless := ⟨a, ha⟩
  let B : NativeTraceless := ⟨b, hb⟩
  let C : NativeTraceless := ⟨c, hc⟩
  let D : NativeTraceless := ⟨d, hd⟩
  have hp := HasSquareLaw.polarized nativeEqualCubic_squareLaw A B C D
  have hL (X Y Z W : NativeTraceless) :
      ⟪nativeEqualCubic.L X Y, nativeEqualCubic.L Z W⟫ =
        Glennie.inner (jordan X Y) (jordan Z W) -
          Glennie.inner (X : Glennie.Albert) Y * Glennie.inner (Z : Glennie.Albert) W / 3 := by
    change Glennie.inner (Glennie.traceless (jordan X Y)) (Glennie.traceless (jordan Z W)) = _
    rw [inner_center]
    rfl
  have hi (X Y : NativeTraceless) : ⟪X, Y⟫ = Glennie.inner (X : Glennie.Albert) Y := rfl
  rw [hL, hL, hL, hi, hi, hi, hi, hi, hi] at hp
  change _ - Glennie.inner a b * Glennie.inner c d / 3 +
      (_ - Glennie.inner a c * Glennie.inner b d / 3) +
      (_ - Glennie.inner a d * Glennie.inner b c / 3) = _ at hp
  linear_combination hp

namespace JC

/-- The defect of the quartic identity. -/
def quartic (a b c d : JC) : ℂ :=
  ip (mul a b) (mul c d) + ip (mul a c) (mul b d) + ip (mul a d) (mul b c) -
    (ip a b * ip c d + ip a c * ip b d + ip a d * ip b c) / 2

private theorem q_split₁ (x y : Glennie.Albert) (b c d : JC) :
    quartic (of x + Complex.I • of y) b c d = quartic (of x) b c d + Complex.I * quartic (of y) b c d := by
  simp only [quartic, mul_add_left, mul_smul_left, ip_add_left, ip_smul_left]; ring

private theorem q_split₂ (x y : Glennie.Albert) (a c d : JC) :
    quartic a (of x + Complex.I • of y) c d = quartic a (of x) c d + Complex.I * quartic a (of y) c d := by
  simp only [quartic, mul_add_left, mul_add_right, mul_smul_left, mul_smul_right, ip_add_left,
    ip_add_right, ip_smul_left, ip_smul_right]; ring

private theorem q_split₃ (x y : Glennie.Albert) (a b d : JC) :
    quartic a b (of x + Complex.I • of y) d = quartic a b (of x) d + Complex.I * quartic a b (of y) d := by
  simp only [quartic, mul_add_left, mul_add_right, mul_smul_left, mul_smul_right, ip_add_left,
    ip_add_right, ip_smul_left, ip_smul_right]; ring

private theorem q_split₄ (x y : Glennie.Albert) (a b c : JC) :
    quartic a b c (of x + Complex.I • of y) = quartic a b c (of x) + Complex.I * quartic a b c (of y) := by
  simp only [quartic, mul_add_left, mul_add_right, mul_smul_left, mul_smul_right, ip_add_left,
    ip_add_right, ip_smul_left, ip_smul_right]; ring

private theorem q_real (x₁ x₂ x₃ x₄ : Glennie.Albert) (h₁ : Glennie.trace x₁ = 0)
    (h₂ : Glennie.trace x₂ = 0) (h₃ : Glennie.trace x₃ = 0) (h₄ : Glennie.trace x₄ = 0) :
    quartic (of x₁) (of x₂) (of x₃) (of x₄) = 0 := by
  simp only [quartic, of_mul, ip_of]
  have h := real_quartic x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄
  have h' : ((Glennie.inner (jordan x₁ x₂) (jordan x₃ x₄) +
      Glennie.inner (jordan x₁ x₃) (jordan x₂ x₄) +
      Glennie.inner (jordan x₁ x₄) (jordan x₂ x₃) : ℝ) : ℂ) =
      (((Glennie.inner x₁ x₂ * Glennie.inner x₃ x₄ + Glennie.inner x₁ x₃ * Glennie.inner x₂ x₄ +
        Glennie.inner x₁ x₄ * Glennie.inner x₂ x₃) / 2 : ℝ) : ℂ) := by rw [h]
  push_cast at h'
  linear_combination h'

theorem tr_eq_zero_iff (z : JC) : tr z = 0 ↔ Glennie.trace z.re = 0 ∧ Glennie.trace z.im = 0 := by
  constructor
  · intro h
    exact ⟨congrArg Complex.re h, congrArg Complex.im h⟩
  · rintro ⟨h₁, h₂⟩
    apply Complex.ext
    · exact h₁
    · exact h₂

/-- The quartic identity `(5-quartic)` on the traceless part of the complexification. -/
theorem quartic_eq_zero (a b c d : JC) (ha : tr a = 0) (hb : tr b = 0) (hc : tr c = 0)
    (hd : tr d = 0) : quartic a b c d = 0 := by
  obtain ⟨ha₁, ha₂⟩ := (tr_eq_zero_iff a).mp ha
  obtain ⟨hb₁, hb₂⟩ := (tr_eq_zero_iff b).mp hb
  obtain ⟨hc₁, hc₂⟩ := (tr_eq_zero_iff c).mp hc
  obtain ⟨hd₁, hd₂⟩ := (tr_eq_zero_iff d).mp hd
  rw [eq_re_add_im a, eq_re_add_im b, eq_re_add_im c, eq_re_add_im d]
  simp only [q_split₁, q_split₂, q_split₃, q_split₄,
    q_real _ _ _ _ ha₁ hb₁ hc₁ hd₁, q_real _ _ _ _ ha₁ hb₁ hc₁ hd₂,
    q_real _ _ _ _ ha₁ hb₁ hc₂ hd₁, q_real _ _ _ _ ha₁ hb₁ hc₂ hd₂,
    q_real _ _ _ _ ha₁ hb₂ hc₁ hd₁, q_real _ _ _ _ ha₁ hb₂ hc₁ hd₂,
    q_real _ _ _ _ ha₁ hb₂ hc₂ hd₁, q_real _ _ _ _ ha₁ hb₂ hc₂ hd₂,
    q_real _ _ _ _ ha₂ hb₁ hc₁ hd₁, q_real _ _ _ _ ha₂ hb₁ hc₁ hd₂,
    q_real _ _ _ _ ha₂ hb₁ hc₂ hd₁, q_real _ _ _ _ ha₂ hb₁ hc₂ hd₂,
    q_real _ _ _ _ ha₂ hb₂ hc₁ hd₁, q_real _ _ _ _ ha₂ hb₂ hc₁ hd₂,
    q_real _ _ _ _ ha₂ hb₂ hc₂ hd₁, q_real _ _ _ _ ha₂ hb₂ hc₂ hd₂]
  ring

end JC

end

end ThirteenPlanes.AlbertGrading.Grading
