module

public import ThirteenPlanes.AlbertGrading.Grading.PhaseCube

@[expose] public section

set_option backward.privateInPublic true

/-! # Points, signs and zero-sum triples of nonzero grades

Bookkeeping for graded cubic expansion: a nonzero grade `k ∈ 𝔽₃³` is a point of `PG(2,3)` (`pointOfNZ`) with a sign; a zero-sum triple of nonzero grades is either `(k,k,k)` or
consists of three distinct collinear points, and the zero-sum triples over a fixed collinear
triple of points are the twelve reorderings of `(g,h,k)` and `(-g,-h,-k)`. -/

namespace ThirteenPlanes.AlbertGrading.Cubic

open Grading

noncomputable section

/-- An ordered triple of nonzero grades. -/
abbrev Triple := NonzeroCharge × NonzeroCharge × NonzeroCharge

/-- The sign of a nonzero grade relative to its point's representative. -/
def sgnOf (k : NonzeroCharge) : Bool := (signedPlaneGradeEquiv.symm k).2

theorem grade_point_sign (k : NonzeroCharge) : signedGrade (pointOfNZ k) (sgnOf k) = k :=
  signedPlaneGradeEquiv.apply_symm_apply k

theorem pointOfNZ_signedGrade (p : SignedPlaneIndex) (s : Bool) : pointOfNZ (signedGrade p s) = p := by
  unfold pointOfNZ signedGrade; rw [Equiv.symm_apply_apply]

theorem sgnOf_signedGrade (p : SignedPlaneIndex) (s : Bool) : sgnOf (signedGrade p s) = s := by
  unfold sgnOf signedGrade; rw [Equiv.symm_apply_apply]

theorem pointOfNZ_opp (k : NonzeroCharge) : pointOfNZ (oppositeCharge k) = pointOfNZ k := by
  conv_lhs => rw [← grade_point_sign k, ← signedGrade_not]
  exact pointOfNZ_signedGrade _ _

theorem opp_ne_self (k : NonzeroCharge) : oppositeCharge k ≠ k := by
  intro h; exact charge_neg_ne_self k.property (congrArg Subtype.val h)

/-- Two nonzero grades on the same point are equal or opposite. -/
theorem eq_or_opp_of_point {a b : NonzeroCharge} (h : pointOfNZ b = pointOfNZ a) :
    b = a ∨ b = oppositeCharge a := by
  rw [← grade_point_sign a, ← grade_point_sign b, h]
  cases hs : sgnOf a <;> cases ht : sgnOf b
  · exact Or.inl rfl
  · right; rw [← signedGrade_not]; rfl
  · right; rw [← signedGrade_not]; rfl
  · exact Or.inl rfl

@[simp] theorem opp_val (k : NonzeroCharge) : (oppositeCharge k).val = -k.val := rfl

/-- The ordered point triple of a triple of grades, as an unordered set. -/
def ptset (x : Triple) : Finset SignedPlaneIndex :=
  {pointOfNZ x.1, pointOfNZ x.2.1, pointOfNZ x.2.2}

/-- Zero sum. -/
def ZeroSum (x : Triple) : Prop := x.1.val + x.2.1.val + x.2.2.val = 0

instance : DecidablePred ZeroSum := fun _ => inferInstanceAs (Decidable (_ = _))

/-- The three points of a triple are pairwise distinct. -/
def Proper (x : Triple) : Prop :=
  pointOfNZ x.1 ≠ pointOfNZ x.2.1 ∧ pointOfNZ x.1 ≠ pointOfNZ x.2.2 ∧ pointOfNZ x.2.1 ≠ pointOfNZ x.2.2

/-- The finite set of zero-sum representatives of a set of points (`tripleReps` as a finset). -/
def repsF (t : Finset SignedPlaneIndex) : Finset Triple :=
  Finset.univ.filter fun x => ZeroSum x ∧ ptset x = t

theorem mem_repsF {t : Finset SignedPlaneIndex} {x : Triple} : x ∈ repsF t ↔ x ∈ tripleReps t := by
  simp only [repsF, Finset.mem_filter, Finset.mem_univ, true_and]; rfl

/-! ## Three distinct points -/

theorem card_three_distinct {p q r : SignedPlaneIndex} (h : ({p, q, r} : Finset _).card = 3) :
    p ≠ q ∧ p ≠ r ∧ q ≠ r := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · subst e
    rw [Finset.insert_eq_of_mem (Finset.mem_insert_self p _)] at h
    have := Finset.card_le_two (a := p) (b := r); omega
  · subst e
    rw [Finset.insert_eq_of_mem (by simp : p ∈ ({q, p} : Finset SignedPlaneIndex))] at h
    have := Finset.card_le_two (a := q) (b := p); omega
  · subst e
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self q)] at h
    have := Finset.card_le_two (a := p) (b := q); omega

theorem card_eq_three_of_mem {t : Finset SignedPlaneIndex} (ht : t ∈ signedCollinearTriples) :
    t.card = 3 := by
  simp only [signedCollinearTriples, Finset.mem_biUnion, Finset.mem_powersetCard] at ht
  obtain ⟨_, _, _, h⟩ := ht
  exact h

/-- A reordering of three distinct elements. -/
theorem perm_of_eq {α : Type*} [DecidableEq α] {p q r p' q' r' : α} (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (h : ({p', q', r'} : Finset α) = {p, q, r}) :
    (p' = p ∧ q' = q ∧ r' = r) ∨ (p' = p ∧ q' = r ∧ r' = q) ∨ (p' = q ∧ q' = p ∧ r' = r) ∨
      (p' = q ∧ q' = r ∧ r' = p) ∨ (p' = r ∧ q' = p ∧ r' = q) ∨ (p' = r ∧ q' = q ∧ r' = p) := by
  have hp' : p' ∈ ({p, q, r} : Finset α) := h ▸ by simp
  have hq' : q' ∈ ({p, q, r} : Finset α) := h ▸ by simp
  have hr' : r' ∈ ({p, q, r} : Finset α) := h ▸ by simp
  have hp : p ∈ ({p', q', r'} : Finset α) := h.symm ▸ by simp
  have hq : q ∈ ({p', q', r'} : Finset α) := h.symm ▸ by simp
  have hr : r ∈ ({p', q', r'} : Finset α) := h.symm ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp' hq' hr' hp hq hr
  rcases hp' with rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl <;>
    rcases hr' with rfl | rfl | rfl <;> simp_all [eq_comm]

/-! ## Signs -/

private theorem zero_of_two (c : Charge) (h : c + c = 0) : c = 0 := by
  rw [charge_add_self] at h
  exact neg_eq_zero.mp h

/-- Two zero-sum triples on the same ordered points agree up to a global sign. -/
theorem sign_rigid {a b c a' b' c' : NonzeroCharge} (hs : a.val + b.val + c.val = 0)
    (hs' : a'.val + b'.val + c'.val = 0) (ha : pointOfNZ a' = pointOfNZ a)
    (hb : pointOfNZ b' = pointOfNZ b) (hc : pointOfNZ c' = pointOfNZ c) :
    (a', b', c') = (a, b, c) ∨ (a', b', c') = (oppositeCharge a, oppositeCharge b, oppositeCharge c) := by
  rcases eq_or_opp_of_point ha with h1 | h1 <;> rcases eq_or_opp_of_point hb with h2 | h2 <;>
    rcases eq_or_opp_of_point hc with h3 | h3 <;> rw [h1, h2, h3] at hs' ⊢ <;> try simp only [opp_val] at hs'
  · exact Or.inl rfl
  · exfalso; apply c.property; apply zero_of_two; linear_combination hs - hs'
  · exfalso; apply b.property; apply zero_of_two; linear_combination hs - hs'
  · exfalso; apply a.property; apply zero_of_two; linear_combination hs + hs'
  · exfalso; apply a.property; apply zero_of_two; linear_combination hs - hs'
  · exfalso; apply b.property; apply zero_of_two; linear_combination hs + hs'
  · exfalso; apply c.property; apply zero_of_two; linear_combination hs + hs'
  · exact Or.inr rfl

end

end ThirteenPlanes.AlbertGrading.Cubic
