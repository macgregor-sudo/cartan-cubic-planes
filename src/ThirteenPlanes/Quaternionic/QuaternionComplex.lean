module

public import ThirteenPlanes.Quaternionic.FourierScale

@[expose] public section

/-!
# Exact complex-pair algebra inside the native quaternions

These coordinate identities expose ordinary a+bj multiplication before the
Fourier phases are specialized. They are proved on the actual quaternion type.
-/
noncomputable section
namespace QuaternionicMUB

def quaternionComplexPart (q : Q) : ℂ := ⟨q.re,q.imI⟩
def quaternionJPart (q : Q) : ℂ := ⟨q.imJ,q.imK⟩
def quaternionOfComplexPair (a b : ℂ) : Q := ⟨a.re,a.im,b.re,b.im⟩

lemma quaternion_parts (q : Q) :
    quaternionOfComplexPair (quaternionComplexPart q) (quaternionJPart q)=q := by
  ext <;> rfl

lemma quaternionOfComplexPair_mul (a b c d : ℂ) :
    quaternionOfComplexPair a b*quaternionOfComplexPair c d=
      quaternionOfComplexPair (a*c-b*star d) (a*d+b*star c) := by
  ext <;>
    simp [quaternionOfComplexPair, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im,
      Complex.star_def] <;> ring

lemma quaternionOfComplexPair_star (a b : ℂ) :
    star (quaternionOfComplexPair a b)=quaternionOfComplexPair (star a) (-b) := by
  ext <;> simp [quaternionOfComplexPair, Complex.star_def]

lemma quaternionOfComplexPair_re (a b : ℂ) : (quaternionOfComplexPair a b).re=a.re := rfl

lemma quaternionOfComplexPair_normSq (a b : ℂ) :
    Quaternion.normSq (quaternionOfComplexPair a b)=Complex.normSq a+Complex.normSq b := by
  simp only [Quaternion.normSq_def', quaternionOfComplexPair, Complex.normSq_apply]
  ring

lemma quaternionComplex_mul (a b : ℂ) :
    quaternionOfComplexPair a 0*quaternionOfComplexPair b 0=
      quaternionOfComplexPair (a*b) 0 := by
  rw [quaternionOfComplexPair_mul]
  simp

lemma quaternionComplex_star (a : ℂ) :
    star (quaternionOfComplexPair a 0)=quaternionOfComplexPair (star a) 0 := by
  rw [quaternionOfComplexPair_star, neg_zero]

/-- The literal complex part of p w q*, including the second complex component
with its necessary conjugated phase. -/
lemma quaternion_complex_edge (z w : ℂ) (p q : Q) :
    (quaternionOfComplexPair z 0*p*quaternionOfComplexPair w 0*star q).re=
      (z*(quaternionComplexPart p*star (quaternionComplexPart q)*w+
        quaternionJPart p*star (quaternionJPart q)*star w)).re := by
  conv_lhs => rw [← quaternion_parts p, ← quaternion_parts q]
  rw [quaternionOfComplexPair_mul, quaternionOfComplexPair_mul,
    quaternionOfComplexPair_star, quaternionOfComplexPair_mul]
  simp only [mul_zero, zero_mul, sub_zero, add_zero, star_zero, zero_sub,
    star_neg, neg_neg, sub_neg_eq_add, quaternionOfComplexPair_re]
  congr 1
  ring

end QuaternionicMUB
