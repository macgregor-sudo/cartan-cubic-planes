module

public import ThirteenPlanes.SignedProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

namespace ThirteenPlanes

noncomputable section

theorem chargeRoot_quadratic : chargeRoot ^ 2 + chargeRoot + 1 = 0 := by
  have h : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  unfold chargeRoot
  linear_combination (norm := ring_nf) Complex.I ^ 2 / 4 * h + 3 / 4 * Complex.I_sq

theorem chargeRoot_cube : chargeRoot ^ 3 = 1 := by
  linear_combination (chargeRoot - 1) * chargeRoot_quadratic

def chargePhase (a : ZMod 3) : ℂ := chargeRoot ^ a.val

theorem chargePhase_add (a b : ZMod 3) : chargePhase (a+b) = chargePhase a * chargePhase b := by
  unfold chargePhase
  rw [ZMod.val_add, ← pow_add]
  symm
  exact pow_eq_pow_mod _ chargeRoot_cube

abbrev WeylLabel := ZMod 3 × ZMod 3

def symplecticBracket (v w : WeylLabel) : ZMod 3 := v.1*w.2-v.2*w.1

/-- The matrix sends column j to row j+a with coefficient ω^(-ab+bj). -/
def weylMatrix (v : WeylLabel) : Matrix (ZMod 3) (ZMod 3) ℂ :=
  fun i j => if i = j+v.1 then chargePhase (-v.1*v.2+v.2*j) else 0

theorem weylMatrix_mul (v w : WeylLabel) :
    weylMatrix v * weylMatrix w = chargePhase (symplecticBracket v w) • weylMatrix (v+w) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (j+w.1)]
  · simp only [weylMatrix, Matrix.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, ite_true]
    have hi : j+w.1+v.1 = j+(v.1+w.1) := by abel
    by_cases hij : i=j+(v.1+w.1)
    · simp only [hi, hij, ↓reduceIte, ← chargePhase_add]
      congr 1
      unfold symplecticBracket
      linear_combination v.2*w.1 * (by decide : (3 : ZMod 3)=0)
    · simp [hi, hij]
  · intro k _ hk
    simp [weylMatrix, hk]
  · simp

@[simp] theorem chargePhase_zero : chargePhase 0 = 1 := by rfl

theorem chargePhase_neg (a : ZMod 3) : chargePhase (-a) = star (chargePhase a) := by
  have h : star chargeRoot = -1-chargeRoot := by
    apply Complex.ext <;> simp [chargeRoot] <;> ring
  fin_cases a
  · change 1 = star (1 : ℂ); simp
  · change chargeRoot^2 = star (chargeRoot^1)
    rw [pow_one, h]
    linear_combination chargeRoot_quadratic
  · change chargeRoot^1 = star (chargeRoot^2)
    rw [pow_one, star_pow, h]
    linear_combination -chargeRoot_quadratic

theorem weylMatrix_adjoint (v : WeylLabel) : (weylMatrix v).conjTranspose = weylMatrix (-v) := by
  ext i j
  change star (if j = i+v.1 then chargePhase (-v.1*v.2+v.2*i) else 0) = _
  by_cases hij : j = i+v.1
  · subst j
    simp only [weylMatrix, ↓reduceIte, Prod.fst_neg, Prod.snd_neg, add_neg_cancel_right,
      ← chargePhase_neg, neg_neg]
    congr 1
    linear_combination v.1*v.2*(by decide : (3 : ZMod 3)=0)
  · have hji : i ≠ j+(-v.1) := by intro h; apply hij; rw [h]; abel
    simp [weylMatrix, hij, hji]

theorem weylMatrix_trace (v : WeylLabel) :
    (weylMatrix v).trace = if v=0 then 3 else 0 := by
  obtain ⟨a,b⟩ := v
  by_cases ha : a=0
  · subst a
    change (∑ i : ZMod 3, if i=i+0 then chargePhase (-0*b+b*i) else 0) = _
    simp only [add_zero, ↓reduceIte, neg_zero, zero_mul, zero_add]
    change (∑ i : Fin 3, chargePhase (b * (show ZMod 3 from i))) = _
    rw [Fin.sum_univ_three]
    fin_cases b
    · change (1:ℂ) + 1 + 1 = 3; norm_num
    · change 1 + chargeRoot^1 + chargeRoot^2 = 0
      linear_combination chargeRoot_quadratic
    · change 1 + chargeRoot^2 + chargeRoot^1 = 0
      linear_combination chargeRoot_quadratic
  · have hv : ((a,b) : WeylLabel) ≠ 0 := fun h => ha (congrArg Prod.fst h)
    simp [Matrix.trace, Matrix.diag, weylMatrix, ha, hv]

end
end ThirteenPlanes
