module

public import ThirteenPlanes.AlbertGrading.Cubic.Orbit

@[expose] public section

/-! # (S2), abstract form: regrouping a graded cubic into the 52 collinear triples

Let `D(a,b,c)` be complex coefficients on triples of nonzero grades, vanishing off `a+b+c = 0`,
symmetric, conjugated by `k ↦ -k`, with `D(k,k,k) = 3`, and let `Z_k` be coordinates with
`Z_{-k} = Z̄_k`. Then `Re Σ_{a,b,c} D(a,b,c) Z_a Z_b Z_c = 3 Σ_k Re Z_k³ - 18 Σ_t T_t`, the second
sum over the 52 collinear triples `t`, with `T_t = Re(-(2/3) D(g,h,k) Z_g Z_h Z_k)` at any zero-sum
representative `(g,h,k)` of `t`. The expression is independent of the representative and
applies both to the abstract grading and to Tits's model. 
-/

namespace ThirteenPlanes.AlbertGrading.Cubic

open Grading

noncomputable section

/-- Coefficient functions on triples of nonzero grades. -/
abbrev Coeff := NonzeroCharge → NonzeroCharge → NonzeroCharge → ℂ

/-- The hypotheses of the regrouping. -/
structure CubicData (D : Coeff) (Z : NonzeroCharge → ℂ) : Prop where
  zero : ∀ a b c : NonzeroCharge, a.val + b.val + c.val ≠ 0 → D a b c = 0
  swap12 : ∀ a b c, D a b c = D b a c
  swap23 : ∀ a b c, D a b c = D a c b
  neg : ∀ a b c, D (oppositeCharge a) (oppositeCharge b) (oppositeCharge c) = star (D a b c)
  diag : ∀ k, D k k k = 3
  coord : ∀ k, Z (oppositeCharge k) = star (Z k)

/-- The term `Re(-(2/3) D(g,h,k) Z_g Z_h Z_k)` for `D = ⟨u∘u,u⟩`. -/
def tT (D : Coeff) (Z : NonzeroCharge → ℂ) (x : Triple) : ℝ :=
  ((-(2 / 3 : ℂ)) * D x.1 x.2.1 x.2.2 * Z x.1 * Z x.2.1 * Z x.2.2).re

open Classical in
/-- The summand of a set of points at a chosen representative. -/
def tV (D : Coeff) (Z : NonzeroCharge → ℂ) (t : Finset SignedPlaneIndex) : ℝ :=
  if h : (tripleReps t).Nonempty then tT D Z h.some else 0

/-- The full triple sum. -/
def fullSum (D : Coeff) (Z : NonzeroCharge → ℂ) : ℂ :=
  ∑ x : Triple, D x.1 x.2.1 x.2.2 * Z x.1 * Z x.2.1 * Z x.2.2

variable {D : Coeff} {Z : NonzeroCharge → ℂ}

theorem tT_orbit (hD : CubicData D Z) {a b c : NonzeroCharge} {y : Triple}
    (hy : y ∈ orbitOf a b c) : tT D Z y = tT D Z (a, b, c) := by
  have hn : ∀ a b c : NonzeroCharge,
      tT D Z (oppositeCharge a, oppositeCharge b, oppositeCharge c) = tT D Z (a, b, c) := by
    intro a b c
    simp only [tT, hD.neg, hD.coord]
    rw [show (-(2 / 3 : ℂ)) * star (D a b c) * star (Z a) * star (Z b) * star (Z c) =
      star ((-(2 / 3 : ℂ)) * D a b c * Z a * Z b * Z c) by simp [star_mul']]
    exact Complex.conj_re _
  have hp : ∀ a b c : NonzeroCharge, tT D Z (a, c, b) = tT D Z (a, b, c) ∧
      tT D Z (b, a, c) = tT D Z (a, b, c) ∧ tT D Z (b, c, a) = tT D Z (a, b, c) ∧
      tT D Z (c, a, b) = tT D Z (a, b, c) ∧ tT D Z (c, b, a) = tT D Z (a, b, c) := by
    intro a b c
    simp only [tT]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> congr 1
    · rw [hD.swap23 a c b]; ring
    · rw [hD.swap12 b a c]; ring
    · rw [hD.swap12 b c a, hD.swap23 c b a, hD.swap12 c a b, hD.swap23 a c b]; ring
    · rw [hD.swap12 c a b, hD.swap23 a c b]; ring
    · rw [hD.swap12 c b a, hD.swap23 b c a, hD.swap12 b a c]; ring
  simp only [orbitOf, Finset.mem_insert, Finset.mem_singleton] at hy
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp a b c
  obtain ⟨q1, q2, q3, q4, q5⟩ := hp (oppositeCharge a) (oppositeCharge b) (oppositeCharge c)
  have q0 := hn a b c
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact q0
  · rw [q1, q0]
  · rw [q2, q0]
  · rw [q3, q0]
  · rw [q4, q0]
  · rw [q5, q0]

/-- Members of a collinear triple's representatives have three distinct points. -/
theorem proper_of_mem_reps {t : Finset SignedPlaneIndex} (ht : t ∈ signedCollinearTriples)
    {x : Triple} (hx : x ∈ repsF t) :
    pointOfNZ x.1 ≠ pointOfNZ x.2.1 ∧ pointOfNZ x.1 ≠ pointOfNZ x.2.2 ∧
      pointOfNZ x.2.1 ≠ pointOfNZ x.2.2 := by
  rw [repsF, Finset.mem_filter] at hx
  have hc := card_eq_three_of_mem ht
  rw [← hx.2.2] at hc
  exact card_three_distinct hc

theorem repsF_eq_orbit {t : Finset SignedPlaneIndex} (ht : t ∈ signedCollinearTriples)
    {x : Triple} (hx : x ∈ repsF t) : repsF t = orbitOf x.1 x.2.1 x.2.2 := by
  obtain ⟨h1, h2, h3⟩ := proper_of_mem_reps ht hx
  have hx' := hx
  rw [repsF, Finset.mem_filter] at hx'
  rw [← hx'.2.2]
  exact repsF_eq_orbitOf hx'.2.1 h1 h2 h3

/-- Representative independence. -/
theorem tT_eq_tV (hD : CubicData D Z) {t : Finset SignedPlaneIndex}
    (ht : t ∈ signedCollinearTriples) {x : Triple} (hx : x ∈ tripleReps t) :
    tT D Z x = tV D Z t := by
  have hne : (tripleReps t).Nonempty := ⟨x, hx⟩
  rw [tV, dite_eq_left hne]
  have hx' := mem_repsF.mpr hx
  have hs := mem_repsF.mpr hne.some_mem
  rw [repsF_eq_orbit ht hx'] at hs
  rw [tT_orbit hD hs]

theorem sum_reps (hD : CubicData D Z) {t : Finset SignedPlaneIndex}
    (ht : t ∈ signedCollinearTriples) :
    ∑ x ∈ repsF t, tT D Z x = 12 * tV D Z t := by
  by_cases hne : (repsF t).Nonempty
  · obtain ⟨x, hx⟩ := hne
    rw [Finset.sum_congr rfl fun y hy => tT_eq_tV hD ht (mem_repsF.mp hy), Finset.sum_const,
      repsF_eq_orbit ht hx]
    obtain ⟨h1, h2, h3⟩ := proper_of_mem_reps ht hx
    rw [orbitOf_card h1 h2 h3]
    simp
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have he : ¬ (tripleReps t).Nonempty := by
      rintro ⟨x, hx⟩
      have := mem_repsF.mpr hx
      rw [hne] at this
      simp at this
    rw [hne, tV, dite_eq_right he]
    simp

/-! ## Collinearity of proper zero-sum triples -/

theorem signedGrade_eq_iff' (p q : SignedPlaneIndex) (s t : Bool) :
    signedGrade p s = signedGrade q t ↔ p = q ∧ s = t := by
  change signedPlaneGradeEquiv (p, s) = signedPlaneGradeEquiv (q, t) ↔ _
  rw [Equiv.apply_eq_iff_eq, Prod.mk.injEq]

theorem ptset_mem_of_proper {a b c : NonzeroCharge} (hs : a.val + b.val + c.val = 0)
    (hab : pointOfNZ a ≠ pointOfNZ b) (hac : pointOfNZ a ≠ pointOfNZ c)
    (hbc : pointOfNZ b ≠ pointOfNZ c) : ptset (a, b, c) ∈ signedCollinearTriples := by
  show ({pointOfNZ a, pointOfNZ b, pointOfNZ c} : Finset SignedPlaneIndex) ∈ signedCollinearTriples
  have ea := grade_point_sign a
  have eb := grade_point_sign b
  have ec := grade_point_sign c
  generalize pointOfNZ a = p at *
  generalize pointOfNZ b = q at *
  generalize pointOfNZ c = r at *
  rw [mem_signedCollinearTriples_iff p q r hab hac hbc,
    signedCollinear_iff_unique_completion p q r hab hac hbc]
  -- a completion with first sign false
  have hcomp : ∃ s : Bool × Bool, signedCompletesZero p q r s := by
    cases hsa : sgnOf a
    · refine ⟨(sgnOf b, sgnOf c), ?_⟩
      unfold signedCompletesZero
      rw [hsa] at ea
      simp only [eb, ec]
      rw [← signedGrade_false p, ea]; exact hs
    · refine ⟨(!sgnOf b, !sgnOf c), ?_⟩
      unfold signedCompletesZero
      rw [hsa] at ea
      simp only [signedGrade_not, eb, ec, opp_val]
      have : p.val = oppositeCharge a := by
        rw [← signedGrade_false p, ← oppositeCharge_opposite (signedGrade p false),
          ← signedGrade_not, Bool.not_false, ea]
      rw [this, opp_val]; linear_combination -hs
  obtain ⟨s, hs0⟩ := hcomp
  refine ⟨s, hs0, fun u hu => ?_⟩
  unfold signedCompletesZero at hs0 hu
  have hr := sign_rigid (a := signedGrade p false) (b := signedGrade q s.1) (c := signedGrade r s.2)
    (a' := signedGrade p false) (b' := signedGrade q u.1) (c' := signedGrade r u.2) hs0 hu rfl
    (by simp only [pointOfNZ_signedGrade]) (by simp only [pointOfNZ_signedGrade])
  rcases hr with h | h
  · simp only [Prod.mk.injEq, signedGrade_eq_iff', true_and] at h
    exact Prod.ext h.1 h.2
  · exact absurd (Prod.mk.inj h).1.symm (opp_ne_self _)

/-! ## The regrouping -/

/-- `Re Σ D Z Z Z = 3 Σ_k Re Z_k³ - 18 Σ_{52 triples} T_t`. -/
theorem fullSum_re (hD : CubicData D Z) :
    (fullSum D Z).re = 3 * ∑ k, (Z k ^ 3).re - 18 * ∑ t ∈ signedCollinearTriples, tV D Z t := by
  classical
  set F : Triple → ℂ := fun x => D x.1 x.2.1 x.2.2 * Z x.1 * Z x.2.1 * Z x.2.2 with hF
  let Dg : Triple → Prop := fun x => x.1 = x.2.1 ∧ x.1 = x.2.2
  have split := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset Triple) Dg F
  -- diagonal
  have hdiag : ∑ x ∈ Finset.univ.filter Dg, F x = ∑ k, 3 * Z k ^ 3 := by
    have he : Finset.univ.filter Dg = Finset.univ.image (fun k : NonzeroCharge => (k, k, k)) := by
      ext ⟨a, b, c⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq, Dg]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨a, rfl, rfl, rfl⟩
      · rintro ⟨k, rfl, rfl, rfl⟩; exact ⟨rfl, rfl⟩
    rw [he, Finset.sum_image (fun k _ l _ h => (Prod.mk.inj h).1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hF, hD.diag]; ring
  -- off the diagonal only zero-sum triples count
  have hoff : ∑ x ∈ Finset.univ.filter (fun x => ¬ Dg x), F x =
      ∑ t ∈ signedCollinearTriples, ∑ x ∈ repsF t, F x := by
    rw [← Finset.sum_filter_of_ne (p := ZeroSum) (fun x _ hx => by
      by_contra h; exact hx (by simp only [hF, hD.zero _ _ _ h, zero_mul]))]
    rw [← Finset.sum_fiberwise_of_maps_to (g := ptset) (t := signedCollinearTriples)]
    · refine Finset.sum_congr rfl fun t ht => Finset.sum_congr ?_ fun _ _ => rfl
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, repsF]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨?_, h1⟩, h2⟩
        have hx : x ∈ repsF t := by rw [repsF, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h1, h2⟩
        obtain ⟨e1, -, -⟩ := proper_of_mem_reps ht hx
        rintro ⟨hd, -⟩; exact e1 (congrArg pointOfNZ hd)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨h1, h2, h3⟩ := proper_of_zeroSum hx.2 hx.1
      exact ptset_mem_of_proper hx.2 h1 h2 h3
  have hfull : fullSum D Z = ∑ k, 3 * Z k ^ 3 +
      ∑ t ∈ signedCollinearTriples, ∑ x ∈ repsF t, F x := by
    rw [← hdiag, ← hoff, split]; rfl
  rw [hfull, Complex.add_re, Complex.re_sum, Complex.re_sum]
  have h1 : ∀ k, (3 * Z k ^ 3).re = 3 * (Z k ^ 3).re := fun k => by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
  have h2 : ∀ t ∈ signedCollinearTriples, (∑ x ∈ repsF t, F x).re = -18 * tV D Z t := by
    intro t ht
    rw [Complex.re_sum]
    have : ∀ x, (F x).re = -(3 / 2) * tT D Z x := by
      intro x
      simp only [hF, tT]
      rw [show (-(2 / 3 : ℂ)) * D x.1 x.2.1 x.2.2 * Z x.1 * Z x.2.1 * Z x.2.2 =
        ((-(2 / 3) : ℝ) : ℂ) * (D x.1 x.2.1 x.2.2 * Z x.1 * Z x.2.1 * Z x.2.2) by push_cast; ring,
        Complex.re_ofReal_mul]
      ring
    simp only [this, ← Finset.mul_sum, sum_reps hD ht]
    ring
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_congr rfl h2, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

end

end ThirteenPlanes.AlbertGrading.Cubic
