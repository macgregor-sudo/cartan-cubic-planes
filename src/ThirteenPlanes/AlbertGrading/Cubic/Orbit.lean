module

public import ThirteenPlanes.AlbertGrading.Cubic.Points

@[expose] public section

/-! # The twelve representatives of a collinear triple

For a zero-sum triple `(a,b,c)` of nonzero grades on three distinct points, the zero-sum triples
with the same three points are exactly the six reorderings of `(a,b,c)` and of `(-a,-b,-c)`,
and these twelve are distinct. -/

namespace ThirteenPlanes.AlbertGrading.Cubic

open Grading

noncomputable section

/-- The twelve reorderings of `(a,b,c)` and `(-a,-b,-c)`. -/
def orbitOf (a b c : NonzeroCharge) : Finset Triple :=
  {(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a),
   (oppositeCharge a, oppositeCharge b, oppositeCharge c),
   (oppositeCharge a, oppositeCharge c, oppositeCharge b),
   (oppositeCharge b, oppositeCharge a, oppositeCharge c),
   (oppositeCharge b, oppositeCharge c, oppositeCharge a),
   (oppositeCharge c, oppositeCharge a, oppositeCharge b),
   (oppositeCharge c, oppositeCharge b, oppositeCharge a)}

theorem opp_inj {a b : NonzeroCharge} : oppositeCharge a = oppositeCharge b ↔ a = b := by
  constructor
  · intro h; rw [← oppositeCharge_opposite a, h, oppositeCharge_opposite]
  · rintro rfl; rfl

theorem ne_of_point_ne {a b : NonzeroCharge} (h : pointOfNZ a ≠ pointOfNZ b) : a ≠ b :=
  fun e => h (congrArg pointOfNZ e)

theorem ne_opp_of_point_ne {a b : NonzeroCharge} (h : pointOfNZ a ≠ pointOfNZ b) :
    a ≠ oppositeCharge b := fun e => h (by rw [e, pointOfNZ_opp])

theorem orbitOf_card {a b c : NonzeroCharge} (hab : pointOfNZ a ≠ pointOfNZ b)
    (hac : pointOfNZ a ≠ pointOfNZ c) (hbc : pointOfNZ b ≠ pointOfNZ c) :
    (orbitOf a b c).card = 12 := by
  have e1 := ne_of_point_ne hab
  have e2 := ne_of_point_ne hac
  have e3 := ne_of_point_ne hbc
  have e4 := ne_opp_of_point_ne hab
  have e5 := ne_opp_of_point_ne hac
  have e6 := ne_opp_of_point_ne hbc
  have e7 := ne_opp_of_point_ne (Ne.symm hab)
  have e8 := ne_opp_of_point_ne (Ne.symm hac)
  have e9 := ne_opp_of_point_ne (Ne.symm hbc)
  have f1 := opp_ne_self a
  have f2 := opp_ne_self b
  have f3 := opp_ne_self c
  have g1 := e1.symm; have g2 := e2.symm; have g3 := e3.symm; have g4 := e4.symm
  have g5 := e5.symm; have g6 := e6.symm; have g7 := e7.symm; have g8 := e8.symm
  have g9 := e9.symm; have k1 := f1.symm; have k2 := f2.symm; have k3 := f3.symm
  simp [orbitOf, Finset.card_insert_of_notMem, opp_inj, e4, e5, e6, e7, e8, e9,
    g1, g2, g3, k1, k2, k3]

/-- Same points and zero sum: the reorderings of `±(a,b,c)`. -/
theorem repsF_eq_orbitOf {a b c : NonzeroCharge} (hs : a.val + b.val + c.val = 0)
    (hab : pointOfNZ a ≠ pointOfNZ b) (hac : pointOfNZ a ≠ pointOfNZ c)
    (hbc : pointOfNZ b ≠ pointOfNZ c) :
    repsF (ptset (a, b, c)) = orbitOf a b c := by
  ext ⟨a', b', c'⟩
  rw [repsF, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, ZeroSum, ptset]
  constructor
  · intro hh
    have hs' := hh.1
    have hp := hh.2
    have h2 : a.val + c.val + b.val = 0 := by linear_combination hs
    have h3 : b.val + a.val + c.val = 0 := by linear_combination hs
    have h4 : b.val + c.val + a.val = 0 := by linear_combination hs
    have h5 : c.val + a.val + b.val = 0 := by linear_combination hs
    have h6 : c.val + b.val + a.val = 0 := by linear_combination hs
    rcases perm_of_eq hab hac hbc hp with ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩ |
        ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩
    · rcases sign_rigid hs hs' q1 q2 q3 with e | e <;> rw [e] <;> simp [orbitOf]
    · rcases sign_rigid h2 hs' q1 q2 q3 with e | e <;> rw [e] <;> simp [orbitOf]
    · rcases sign_rigid h3 hs' q1 q2 q3 with e | e <;> rw [e] <;> simp [orbitOf]
    · rcases sign_rigid h4 hs' q1 q2 q3 with e | e <;> rw [e] <;> simp [orbitOf]
    · rcases sign_rigid h5 hs' q1 q2 q3 with e | e <;> rw [e] <;> simp [orbitOf]
    · rcases sign_rigid h6 hs' q1 q2 q3 with e | e <;> rw [e] <;> simp [orbitOf]
  · intro hm
    simp only [orbitOf, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      refine ⟨?_, ?_⟩ <;> (try simp only [opp_val, pointOfNZ_opp]) <;>
      first
        | (linear_combination hs) | (linear_combination -hs)
        | (ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)

/-- A zero-sum triple is either diagonal or has three distinct points. -/
theorem proper_of_zeroSum {a b c : NonzeroCharge} (hs : a.val + b.val + c.val = 0)
    (hd : ¬ (a = b ∧ a = c)) :
    pointOfNZ a ≠ pointOfNZ b ∧ pointOfNZ a ≠ pointOfNZ c ∧ pointOfNZ b ≠ pointOfNZ c := by
  have two : ∀ x y : Charge, x + x + y = 0 → y = x := by
    intro x y h; rw [charge_add_self] at h; exact (neg_add_eq_zero.mp h).symm
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rcases eq_or_opp_of_point e.symm with h | h <;> rw [h] at hs
    · exact hd ⟨h.symm, (Subtype.ext (two _ _ hs)).symm⟩
    · exact c.property (by simp only [opp_val] at hs; linear_combination hs)
  · rcases eq_or_opp_of_point e.symm with h | h <;> rw [h] at hs
    · exact hd ⟨(Subtype.ext (two a.val b.val (by linear_combination hs))).symm, h.symm⟩
    · exact b.property (by simp only [opp_val] at hs; linear_combination hs)
  · rcases eq_or_opp_of_point e.symm with h | h <;> rw [h] at hs
    · have hab : a = b := Subtype.ext (two b.val a.val (by linear_combination hs))
      exact hd ⟨hab, hab.trans h.symm⟩
    · exact a.property (by simp only [opp_val] at hs; linear_combination hs)

end

end ThirteenPlanes.AlbertGrading.Cubic
