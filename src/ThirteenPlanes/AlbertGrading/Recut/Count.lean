module

public import ThirteenPlanes.AlbertGrading.Recut.Shares

@[expose] public section

/-! # A re-cut system has 52 positive shares iff `φ` permutes the four planes of `ℓ` -/

namespace ThirteenPlanes.AlbertGrading.Recut

open ThirteenPlanes.RoundCubics

noncomputable section

section Generic

variable {P : SignedPlaneIndex → Fin 3 → Glennie.Albert} (hF : ∀ p, Glennie.Frame (P p))
  (hU : ∀ p q, p ≠ q → ∀ a b, Glennie.inner (P p a) (P q b) = 1 / 3)
  {l : SignedPlaneIndex}
  (hclosed : ∀ x y, x ∈ lineQ P l → y ∈ lineQ P l → Glennie.jordan x y ∈ lineQ P l)
  {φ : lineQ P l ≃ₗ[ℝ] lineQ P l} (hφ : IsSubalgebraAutomorphism (lineQ P l) φ)
  (hmix : ∀ p q r r' : SignedPlaneIndex, p ≠ q → r ≠ r' → r ≠ p → r ≠ q → r' ≠ p → r' ≠ q →
    signedCollinear p q r → signedCollinear p q r' →
    mixedProductSpace nativeEqualCubic (nativeFramePlane (P p)) (nativeFramePlane (P q)) =
      nativeFramePlane (P r) ⊔ nativeFramePlane (P r'))
  (hshare : ∀ p q r : SignedPlaneIndex, p ≠ q → p ≠ r → q ≠ r →
    shareOfThreePlanes nativeEqualCubic (nativeFramePlane (P p)) (nativeFramePlane (P q))
      (nativeFramePlane (P r)) = if signedCollinear p q r then 1 else 0)

include hF hφ in
theorem permutesG_iff : PermutesG P l φ ↔
    ∃ σ : {p : SignedPlaneIndex // signedPointOnLine p l} ≃
        {p : SignedPlaneIndex // signedPointOnLine p l},
      ∀ p, nativeFramePlane (P (σ p).val) = nativeFramePlane (recutG (lineQ P l) φ P l p.val) := by
  have key (σ : {p : SignedPlaneIndex // signedPointOnLine p l} ≃
      {p : SignedPlaneIndex // signedPointOnLine p l}) (p : {p // signedPointOnLine p l}) :
      (∀ x, x ∈ planeA (P (σ p).val) ↔
        ∃ y : lineQ P l, (y : Glennie.Albert) ∈ planeA (P p.val) ∧ (φ y : Glennie.Albert) = x) ↔
      nativeFramePlane (P (σ p).val) = nativeFramePlane (recutG (lineQ P l) φ P l p.val) := by
    rw [← planeA_eq_iff, SetLike.ext_iff]
    simp only [mem_planeA_recutG hF hφ p.property]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun p => (key σ p).mp (hσ p)⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun p => (key σ p).mpr (hσ p)⟩

include hF hU hclosed hφ hmix hshare in
/-- Rotation of four planes on a graded line (ii), first sentence, for the generic re-cut. -/
theorem recutG_card_iff (c : TightNativeCode) (e : Fin 13 ≃ SignedPlaneIndex)
    (hc : ∀ i, c.point i = recutG (lineQ P l) φ P l (e i)) :
    (positivePlaneTriples nativeEqualCubic c.decomposition).card = 52 ↔ PermutesG P l φ := by
  set R := recutG (lineQ P l) φ P l with hRdef
  have hRF : ∀ p, Glennie.Frame (R p) := (recutG_frames hF hU hclosed hφ).1
  have hcP (i : Fin 13) : c.decomposition.plane i = nativeFramePlane (R (e i)) := by
    change nativeFramePlane (c.point i) = _
    rw [hc]
  have hsparse := thirteenPlane_positive_eq_fifty_two_iff nativeRoundCubic (code_closed c)
  rw [hsparse, permutesG_iff hF hφ]
  constructor
  · intro binary
    -- for every point `r` of `l` some re-cut plane on `l` equals `P_r`
    have claim : ∀ r : {r : SignedPlaneIndex // signedPointOnLine r l},
        ∃ k : {k : SignedPlaneIndex // signedPointOnLine k l},
          nativeFramePlane (R k.val) = nativeFramePlane (P r.val) := by
      rintro ⟨r, hr⟩
      obtain ⟨q, q', q'', hq, hq', hq'', hqq', hqq'', hq'q'', hcolr, hcol''⟩ :=
        exists_off_line_triple hr
      have hrq : r ≠ q := by rintro rfl; exact hq hr
      have hrq' : r ≠ q' := by rintro rfl; exact hq' hr
      have hrq'' : r ≠ q'' := by rintro rfl; exact hq'' hr
      let g := codeOf P hF hU e
      have hgP (k : Fin 13) : g.decomposition.plane k = nativeFramePlane (P (e k)) := rfl
      let i := e.symm q
      let j := e.symm q'
      have hij : i ≠ j := e.symm.injective.ne hqq'
      have hei : e i = q := e.apply_symm_apply q
      have hej : e j = q' := e.apply_symm_apply q'
      have hRq : R q = P q := recutG_off hq
      have hRq' : R q' = P q' := recutG_off hq'
      let dC := fun k => planeShare nativeEqualCubic c.decomposition i j k
      let dG := fun k => planeShare nativeEqualCubic g.decomposition i j k
      have hC2 := planeShare_pair_sum nativeRoundCubic (code_closed c) hij
      have hG2 := planeShare_pair_sum nativeRoundCubic (code_closed g) hij
      rw [Finset.sum_filter] at hC2 hG2
      have hdiff (k : Fin 13) :
          ((if k ≠ i ∧ k ≠ j then dC k else 0) - if k ≠ i ∧ k ≠ j then dG k else 0) =
            if signedPointOnLine (e k) l then dC k - dG k else 0 := by
        by_cases hk : signedPointOnLine (e k) l
        · have hki : k ≠ i := by rintro rfl; exact hq (hei ▸ hk)
          have hkj : k ≠ j := by rintro rfl; exact hq' (hej ▸ hk)
          rw [if_pos ⟨hki, hkj⟩, if_pos ⟨hki, hkj⟩, if_pos hk]
        · have hRk : R (e k) = P (e k) := recutG_off hk
          have hsame : dC k = dG k := by
            show planeShare nativeEqualCubic c.decomposition i j k =
              planeShare nativeEqualCubic g.decomposition i j k
            rw [planeShare_eq_shareOfThreePlanes, planeShare_eq_shareOfThreePlanes, hcP, hcP, hcP,
              hgP, hgP, hgP, hei, hej, hRq, hRq', hRk]
          rw [if_neg hk, hsame, sub_self]
      have hsum0 : ∑ k : Fin 13, (if signedPointOnLine (e k) l then dC k - dG k else 0) = 0 := by
        simp only [← hdiff, Finset.sum_sub_distrib]
        change (∑ k, if k ≠ i ∧ k ≠ j then dC k else 0) -
          (∑ k, if k ≠ i ∧ k ≠ j then dG k else 0) = 0
        rw [hC2, hG2, sub_self]
      by_contra hno
      push Not at hno
      have hzero (k : Fin 13) (hk : signedPointOnLine (e k) l) : dC k = 0 := by
        have hki : k ≠ i := by rintro rfl; exact hq (hei ▸ hk)
        have hkj : k ≠ j := by rintro rfl; exact hq' (hej ▸ hk)
        rcases binary i j k hij hki hkj with h0 | h1
        · exact h0
        · exfalso
          apply hno ⟨e k, hk⟩
          have hle := (planeShare_bounds nativeEqualCubic c.decomposition i j k).2.1.mp h1
          rw [hcP, hcP, hcP, hei, hej, hRq, hRq',
            hmix q q' r q'' hqq' hrq'' hrq hrq' hqq''.symm hq'q''.symm hcolr hcol''] at hle
          have hle' := le_of_le_sup_of_isOrtho hle
            (recut_plane_orthogonal_off hF hU hclosed hφ hk hq'')
            (graded_planes_orthogonal hF hU hrq'')
          exact Submodule.eq_of_le_of_finrank_eq hle'
            ((nativeFramePlane_dimension (hRF _)).trans (nativeFramePlane_dimension (hF r)).symm)
      have hsumG : ∑ k : Fin 13, (if signedPointOnLine (e k) l then dG k else 0) = 0 := by
        have hterm (k : Fin 13) : (if signedPointOnLine (e k) l then dG k else 0) =
            -(if signedPointOnLine (e k) l then dC k - dG k else 0) := by
          by_cases hk : signedPointOnLine (e k) l
          · rw [if_pos hk, if_pos hk, hzero k hk]; ring
          · rw [if_neg hk, if_neg hk, neg_zero]
        rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_neg_distrib, hsum0, neg_zero]
      have hnonneg (k : Fin 13) : 0 ≤ (if signedPointOnLine (e k) l then dG k else 0) := by
        split_ifs
        · exact (planeShare_bounds nativeEqualCubic g.decomposition i j k).1.1
        · exact le_rfl
      have hone : (if signedPointOnLine (e (e.symm r)) l then dG (e.symm r) else 0) = 1 := by
        rw [e.apply_symm_apply, if_pos hr]
        show planeShare nativeEqualCubic g.decomposition i j (e.symm r) = 1
        rw [planeShare_eq_shareOfThreePlanes, hgP, hgP, hgP, hei, hej, e.apply_symm_apply, hshare q q' r hqq' hrq.symm hrq'.symm, if_pos hcolr]
      have hle := Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ (e.symm r))
      rw [hone, hsumG] at hle
      norm_num at hle
    choose g hg using claim
    have ginj : Function.Injective g := by
      intro r r' hrr
      apply Subtype.ext
      apply graded_planes_injective hF hU
      rw [← hg r, ← hg r', hrr]
    have hb : Function.Bijective g := Finite.injective_iff_bijective.mp ginj
    refine ⟨(Equiv.ofBijective g hb).symm, fun p => ?_⟩
    have hp : g ((Equiv.ofBijective g hb).symm p) = p := Equiv.ofBijective_apply_symm_apply g hb p
    rw [← hg, hp]
  · rintro ⟨σ, hσ⟩
    classical
    let τ : SignedPlaneIndex → SignedPlaneIndex := fun p =>
      if h : signedPointOnLine p l then (σ ⟨p, h⟩).val else p
    have hτ (p : SignedPlaneIndex) : nativeFramePlane (R p) = nativeFramePlane (P (τ p)) := by
      by_cases h : signedPointOnLine p l
      · simp only [τ, dif_pos h]
        exact (hσ ⟨p, h⟩).symm
      · simp only [τ, dif_neg h, hRdef, recutG_off h]
    have hτinj : Function.Injective τ := by
      intro p p' hpp
      by_cases h : signedPointOnLine p l <;> by_cases h' : signedPointOnLine p' l
      · simp only [τ, dif_pos h, dif_pos h'] at hpp
        exact congrArg Subtype.val (σ.injective (Subtype.ext hpp))
      · simp only [τ, dif_pos h, dif_neg h'] at hpp
        exact absurd (hpp ▸ (σ ⟨p, h⟩).property) h'
      · simp only [τ, dif_neg h, dif_pos h'] at hpp
        exact absurd (hpp.symm ▸ (σ ⟨p', h'⟩).property) h
      · simpa only [τ, dif_neg h, dif_neg h'] using hpp
    intro i j k hij hki hkj
    have ne (a b : Fin 13) (hab : a ≠ b) : τ (e a) ≠ τ (e b) := hτinj.ne (e.injective.ne hab)
    rw [planeShare_eq_shareOfThreePlanes, hcP, hcP, hcP, hτ, hτ, hτ,
      hshare _ _ _ (ne i j hij) (ne i k hki.symm) (ne j k hkj.symm)]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

end Generic

end

end ThirteenPlanes.AlbertGrading.Recut
