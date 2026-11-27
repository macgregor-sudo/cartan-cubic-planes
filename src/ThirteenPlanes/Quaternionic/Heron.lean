module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.LinearCombination

/-!
# The sharp scalar consequence of two complex autocorrelations

This is the algebraic inequality in the quaternionic MUB proof. Its inputs are
literal complex coefficients, their two zero autocorrelations and unit row
norms. Connecting them to an arbitrary native MUB triple and its actual
27-entry cubic weight is a separate theorem obligation. No MUB cardinality or
normal-form conclusion is asserted by this supporting module.
-/

@[expose] public section

namespace QuaternionicMUB.Heron

noncomputable section

/-- Heron's discriminant expressed through the squared side lengths. -/
def sideDiscriminant (u v w : ℝ) : ℝ :=
  2 * (u*v + v*w + w*u) - (u^2 + v^2 + w^2)

/-- The source discriminant when the squared sides are pairwise products. -/
def discriminant (x y z : ℝ) : ℝ :=
  2*x*y*z*(x+y+z) - (x^2*y^2 + y^2*z^2 + z^2*x^2)

/-- The signed area identity includes degenerate triangles and zero sides. -/
theorem sideDiscriminant_eq_square (u v w : ℂ) (h : u+v+w=0) :
    sideDiscriminant (Complex.normSq u) (Complex.normSq v) (Complex.normSq w) =
      4 * (u.re*v.im-u.im*v.re)^2 := by
  have hw : w = -(u+v) := by linear_combination h
  rw [hw]
  simp only [sideDiscriminant, Complex.normSq_apply, Complex.neg_re, Complex.neg_im,
    Complex.add_re, Complex.add_im]
  ring

/-- A zero complex autocorrelation implies the exact nonnegative discriminant. -/
theorem discriminant_nonneg_of_correlation (a b c : ℂ)
    (h : b * star a + a * star c + c * star b = 0) :
    0 ≤ discriminant (Complex.normSq a) (Complex.normSq b) (Complex.normSq c) := by
  have hs := sideDiscriminant_eq_square (b*star a) (a*star c) (c*star b) h
  have he : sideDiscriminant (Complex.normSq (b*star a))
      (Complex.normSq (a*star c)) (Complex.normSq (c*star b)) =
      discriminant (Complex.normSq a) (Complex.normSq b) (Complex.normSq c) := by
    simp only [Complex.normSq_mul, Complex.normSq_conj, Complex.star_def,
      sideDiscriminant, discriminant]
    ring
  rw [he] at hs
  rw [hs]
  positivity

/-- The elementary estimate behind the two-discriminant argument. -/
theorem product_le_abs_sum (P R : ℝ) (hR : |R| ≤ 1) : P*R ≤ |P+3*R| := by
  have hr := abs_le.mp hR
  rcases le_total 0 P with hP | hP
  · rcases le_total 0 R with hR0 | hR0
    · have hm := mul_nonneg hP (sub_nonneg.mpr hr.2)
      have ha := le_abs_self (P+3*R)
      nlinarith
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hP hR0) (abs_nonneg _)
  · rcases le_total 0 R with hR0 | hR0
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hP hR0) (abs_nonneg _)
    · have hm := mul_nonneg (neg_nonneg.mpr hP) (show 0 ≤ 1+R by linarith)
      have ha := neg_le_abs (P+3*R)
      nlinarith

/-- The sharp lower root, using both source discriminants. -/
theorem quadratic_lower_bound (x y z : ℝ)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1)
    (hp : 0 ≤ discriminant ((1+x)/2) ((1+y)/2) ((1+z)/2))
    (hm : 0 ≤ discriminant ((1-x)/2) ((1-y)/2) ((1-z)/2)) :
    3-2*Real.sqrt 3 ≤ x*y+y*z+z*x := by
  let P := x+y+z
  let Q := x*y+y*z+z*x
  let R := x*y*z
  have hxy : |x| * |y| ≤ 1 := calc
    _ ≤ 1* |y| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ ≤ 1 := by simpa using hy
  have hR : |R| ≤ 1 := calc
    _ = |x| * |y| * |z| := by simp only [R, abs_mul]
    _ ≤ 1* |z| := mul_le_mul_of_nonneg_right hxy (abs_nonneg _)
    _ ≤ 1 := by simpa using hz
  have hp_id : 16*discriminant ((1+x)/2) ((1+y)/2) ((1+z)/2) =
      4*P*R-Q^2+6*Q+3+4*(P+3*R) := by dsimp [P,Q,R,discriminant]; ring
  have hm_id : 16*discriminant ((1-x)/2) ((1-y)/2) ((1-z)/2) =
      4*P*R-Q^2+6*Q+3-4*(P+3*R) := by dsimp [P,Q,R,discriminant]; ring
  have hprod := product_le_abs_sum P R hR
  have hquad : Q^2-6*Q-3 ≤ 0 := by
    rcases le_total 0 (P+3*R) with h | h
    · rw [abs_of_nonneg h] at hprod
      nlinarith [hm_id]
    · rw [abs_of_nonpos h] at hprod
      nlinarith [hp_id]
  have hsq : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  change 3-2*Real.sqrt 3 ≤ Q
  by_contra! h
  have hfac : 0 < (3-Q-2*Real.sqrt 3)*(3-Q+2*Real.sqrt 3) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

/-- Exactly the source normalization `s=(3+Q)/6`. -/
theorem normalized_lower_bound (x y z : ℝ)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1)
    (hp : 0 ≤ discriminant ((1+x)/2) ((1+y)/2) ((1+z)/2))
    (hm : 0 ≤ discriminant ((1-x)/2) ((1-y)/2) ((1-z)/2)) :
    1-1/Real.sqrt 3 ≤ (3+(x*y+y*z+z*x))/6 := by
  have h := quadratic_lower_bound x y z hx hy hz hp hm
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hd : 1/Real.sqrt 3 = Real.sqrt 3/3 := by
    field_simp
    nlinarith
  rw [hd]
  linarith

/-- The exact autocorrelation expression in the Fourier normalization. -/
def correlation (a : Fin 3 → ℂ) : ℂ :=
  a 1 * star (a 0) + a 0 * star (a 2) + a 2 * star (a 1)

/-- Closed scalar result for the actual complex row coefficients, including zeros. -/
theorem lower_bound_of_autocorrelations (a b : Fin 3 → ℂ)
    (hu : ∀ i, Complex.normSq (a i)+Complex.normSq (b i)=1)
    (ha : correlation a=0) (hb : correlation b=0) :
    let z := fun i => Complex.normSq (a i)-Complex.normSq (b i)
    1-1/Real.sqrt 3 ≤ (3+(z 0*z 1+z 1*z 2+z 2*z 0))/6 := by
  dsimp only
  let z := fun i => Complex.normSq (a i)-Complex.normSq (b i)
  have hbound : ∀ i, |z i| ≤ 1 := by
    intro i
    apply abs_le.mpr
    dsimp [z]
    constructor <;> nlinarith [hu i, Complex.normSq_nonneg (a i), Complex.normSq_nonneg (b i)]
  have hplus : ∀ i, (1+z i)/2 = Complex.normSq (a i) := by
    intro i; dsimp [z]; linarith [hu i]
  have hminus : ∀ i, (1-z i)/2 = Complex.normSq (b i) := by
    intro i; dsimp [z]; linarith [hu i]
  apply normalized_lower_bound (z 0) (z 1) (z 2) (hbound 0) (hbound 1) (hbound 2)
  · rw [hplus, hplus, hplus]
    exact discriminant_nonneg_of_correlation (a 0) (a 1) (a 2) ha
  · rw [hminus, hminus, hminus]
    exact discriminant_nonneg_of_correlation (b 0) (b 1) (b 2) hb

end
end QuaternionicMUB.Heron
