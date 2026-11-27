module

public import ThirteenPlanes.SignedSupport

@[expose] public section

/-! # Three incidence facts of `PG(2,3)` used by the re-cut argument

Points and lines are the `SignedPlaneIndex` labels, incidence `signedPointOnLine`. -/

namespace ThirteenPlanes.AlbertGrading.Recut

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Through every point of a line passes another line. -/
theorem exists_other_line : ∀ l r : SignedPlaneIndex, signedPointOnLine r l →
    ∃ m : SignedPlaneIndex, m ≠ l ∧ signedPointOnLine r m := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Two distinct lines meet in exactly one point. -/
theorem meet_card : ∀ l m : SignedPlaneIndex, l ≠ m →
    (Finset.univ.filter (fun p => signedPointOnLine p l ∧ signedPointOnLine p m)).card = 1 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Two points lie on a common line. -/
theorem exists_common_line : ∀ p q : SignedPlaneIndex,
    ∃ m : SignedPlaneIndex, signedPointOnLine p m ∧ signedPointOnLine q m := by
  decide

theorem eq_of_on_two_lines {l m p p' : SignedPlaneIndex} (hlm : l ≠ m)
    (hpl : signedPointOnLine p l) (hpm : signedPointOnLine p m)
    (hp'l : signedPointOnLine p' l) (hp'm : signedPointOnLine p' m) : p = p' := by
  have h := meet_card l m hlm
  exact Finset.card_le_one.mp h.le p (by simp [hpl, hpm]) p' (by simp [hp'l, hp'm])

/-- For a point `r` of `l` there are three distinct points off `l` which are collinear with each
other and with `r` (the other points of a second line through `r`). -/
theorem exists_off_line_triple {l r : SignedPlaneIndex} (hr : signedPointOnLine r l) :
    ∃ q q' q'' : SignedPlaneIndex, ¬ signedPointOnLine q l ∧ ¬ signedPointOnLine q' l ∧
      ¬ signedPointOnLine q'' l ∧ q ≠ q' ∧ q ≠ q'' ∧ q' ≠ q'' ∧
      signedCollinear q q' r ∧ signedCollinear q q' q'' := by
  obtain ⟨m, hml, hrm⟩ := exists_other_line l r hr
  have hcard : ((signedLinePoints m).erase r).card = 3 := by
    rw [Finset.card_erase_of_mem (by simp [signedLinePoints, hrm]), signedLinePoints_card]
  obtain ⟨q, q', q'', hqq', hqq'', hq'q'', hset⟩ := Finset.card_eq_three.mp hcard
  have mem (x : SignedPlaneIndex) (hx : x ∈ ({q, q', q''} : Finset SignedPlaneIndex)) :
      x ≠ r ∧ signedPointOnLine x m := by
    rw [← hset] at hx
    simpa [signedLinePoints] using hx
  have off (x : SignedPlaneIndex) (hx : x ∈ ({q, q', q''} : Finset SignedPlaneIndex)) :
      ¬ signedPointOnLine x l := by
    intro hxl
    exact (mem x hx).1 (eq_of_on_two_lines hml (mem x hx).2 hxl hrm hr)
  have hq : q ∈ ({q, q', q''} : Finset SignedPlaneIndex) := by simp
  have hq' : q' ∈ ({q, q', q''} : Finset SignedPlaneIndex) := by simp
  have hq'' : q'' ∈ ({q, q', q''} : Finset SignedPlaneIndex) := by simp
  exact ⟨q, q', q'', off q hq, off q' hq', off q'' hq'', hqq', hqq'', hq'q'',
    ⟨m, (mem q hq).2, (mem q' hq').2, hrm⟩, ⟨m, (mem q hq).2, (mem q' hq').2, (mem q'' hq'').2⟩⟩

end ThirteenPlanes.AlbertGrading.Recut
