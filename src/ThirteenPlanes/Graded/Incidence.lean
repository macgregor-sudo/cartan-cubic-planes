module

public import ThirteenPlanes.Graded.Frames
public import ThirteenPlanes.Shares.Support
public import ThirteenPlanes.Shares.ThreePlanes

@[expose] public section

set_option backward.privateInPublic true

/-! The exact projection shares and mixed products of the native graded planes. -/

namespace ThirteenPlanes.Graded

open scoped BigOperators RealInnerProductSpace
open RoundCubics

noncomputable section

theorem nativeRound : IsRound nativeEqualCubic (1 / 6) :=
  ⟨by norm_num, fun x => by rw [nativeEqualCubic_squareLaw]; ring⟩

/-- Nonzero cubic restriction is projective collinearity on distinct native planes. -/
theorem native_plane_support_iff (p q r : SignedPlaneIndex)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∃ (x : plane p) (y : plane q) (z : plane r),
      nativeEqualCubic.apply x y z ≠ 0) ↔ signedCollinear p q r := by
  let e (t : SignedPlaneIndex) : signedPlane t ≃ₗᵢ[ℝ] plane t :=
    signedNativeEquiv.submoduleMap (signedPlane t)
  have he (t : SignedPlaneIndex) (x : signedPlane t) :
      ((e t x : plane t) : NativeTraceless) = signedNativeEquiv x := rfl
  rw [← signedEqualCubic_plane_support_iff_collinear p q r hpq hpr hqr]
  constructor
  · rintro ⟨x, y, z, hn⟩
    obtain ⟨x, rfl⟩ := (e p).surjective x
    obtain ⟨y, rfl⟩ := (e q).surjective y
    obtain ⟨z, rfl⟩ := (e r).surjective z
    exact ⟨x, y, z, by simpa only [he, signedEqualCubic_eq_native] using hn⟩
  · rintro ⟨x, y, z, hn⟩
    exact ⟨e p x, e q y, e r z, by simpa only [he, ← signedEqualCubic_eq_native] using hn⟩

private def pairLines (p q : SignedPlaneIndex) : Finset SignedPlaneIndex :=
  Finset.univ.filter (fun l => signedPointOnLine p l ∧ signedPointOnLine q l)

private theorem pairLines_card (p q : SignedPlaneIndex) (hpq : p ≠ q) :
    (pairLines p q).card = 1 := by
  have h : ∀ q, p ≠ q → (pairLines p q).card = 1 := by
    fin_cases p <;> decide
  exact h q hpq

/-- The actual unique projective line determined by two different grades up to sign. -/
theorem unique_joining_line (p q : SignedPlaneIndex) (hpq : p ≠ q) :
    ∃! l : SignedPlaneIndex, signedPointOnLine p l ∧ signedPointOnLine q l := by
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp (pairLines_card p q hpq)
  have hh (k : SignedPlaneIndex) : k = l ↔ signedPointOnLine p k ∧ signedPointOnLine q k := by
    simpa [pairLines] using show k ∈ ({l} : Finset _) ↔ k ∈ pairLines p q by rw [hl]
  exact ⟨l, (hh l).mp rfl, fun k hk => (hh k).mpr hk⟩

private theorem planeShare_zero_of_not_collinear {p q r : SignedPlaneIndex}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (h : ¬ signedCollinear p q r) :
    planeShare nativeEqualCubic decomposition p q r = 0 := by
  apply (planeShare_bounds nativeEqualCubic decomposition p q r).2.2.mpr
  apply (Submodule.isOrtho_iff_le.mpr ?_).symm
  rw [mixedProductSpace_eq_span]
  apply Submodule.map₂_le.mpr
  intro x hx y hy
  change nativeEqualCubic.L (x : NativeTraceless) (y : NativeTraceless) ∈ (plane r)ᗮ
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hz' : nativeEqualCubic.apply (x : NativeTraceless) (y : NativeTraceless) z = 0 := by
    by_contra hz'
    exact h ((native_plane_support_iff p q r hpq hpr hqr).mp ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩, hz'⟩)
  change ⟪z, nativeEqualCubic.L (x : NativeTraceless) (y : NativeTraceless)⟫ = 0
  rw [real_inner_comm]
  exact hz'

/-- The other two points on the unique projective line through (p,q). -/
private def otherLinePoints (p q l : SignedPlaneIndex) : Finset SignedPlaneIndex :=
  ((signedLinePoints l).erase p).erase q

private theorem otherLinePoints_card {p q l : SignedPlaneIndex} (hpq : p ≠ q)
    (hp : signedPointOnLine p l) (hq : signedPointOnLine q l) :
    (otherLinePoints p q l).card = 2 := by
  have hp' : p ∈ signedLinePoints l := by simpa [signedLinePoints] using hp
  have hq' : q ∈ (signedLinePoints l).erase p := by simp [signedLinePoints, hpq.symm, hq]
  unfold otherLinePoints
  rw [Finset.card_erase_of_mem hq', Finset.card_erase_of_mem hp', signedLinePoints_card]

/-- The native half-trace share is one on collinear triples and zero on the other triples. -/
theorem share_eq_collinearity (p q r : SignedPlaneIndex)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    planeShare nativeEqualCubic decomposition p q r = if signedCollinear p q r then 1 else 0 := by
  obtain ⟨l, ⟨hp, hq⟩, unique⟩ := unique_joining_line p q hpq
  let K := otherLinePoints p q l
  let S := fun k => planeShare nativeEqualCubic decomposition p q k
  have hmem (k : SignedPlaneIndex) : k ∈ K ↔ k ≠ p ∧ k ≠ q ∧ signedCollinear p q k := by
    have hi : signedPointOnLine k l ↔ signedCollinear p q k := by
      constructor
      · exact fun h => ⟨l, hp, hq, h⟩
      · rintro ⟨l', hp', hq', hk'⟩
        rwa [unique l' ⟨hp', hq'⟩] at hk'
    simp only [K, otherLinePoints, Finset.mem_erase, signedLinePoints, Finset.mem_filter,
      Finset.mem_univ, true_and, hi]
    tauto
  have hz (k : SignedPlaneIndex) (hkp : k ≠ p) (hkq : k ≠ q) (h : k ∉ K) : S k = 0 :=
    planeShare_zero_of_not_collinear hpq hkp.symm hkq.symm (fun hcol =>
      h ((hmem k).mpr ⟨hkp, hkq, hcol⟩))
  have hsum : ∑ k ∈ K, S k = 2 := by
    rw [← planeShare_pair_sum (planes := decomposition) nativeRound closedPlanes hpq]
    apply Finset.sum_subset
    · intro k hk
      have hh := (hmem k).mp hk
      simp [hh.1, hh.2.1]
    · intro k hk hkn
      have hh := (Finset.mem_filter.mp hk).2
      exact hz k hh.1 hh.2 hkn
  have hd : ∑ k ∈ K, (1 - S k) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, otherLinePoints_card hpq hp hq, hsum]
    norm_num
  have hfull (k : SignedPlaneIndex) (hk : k ∈ K) : S k = 1 := by
    have hn (k : SignedPlaneIndex) (_ : k ∈ K) : 0 ≤ 1 - S k :=
      sub_nonneg.mpr (planeShare_bounds nativeEqualCubic decomposition p q k).1.2
    exact (sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hn).mp hd k hk)).symm
  by_cases hcol : signedCollinear p q r
  · rw [ite_eq_left hcol]
    exact hfull r ((hmem r).mpr ⟨hpr.symm, hqr.symm, hcol⟩)
  · rw [ite_eq_right hcol]
    exact planeShare_zero_of_not_collinear hpq hpr hqr hcol

/-- The native mixed-product span is exactly the sum of the two other line planes. -/
theorem mixedProduct_eq_two_line_planes {p q r s : SignedPlaneIndex}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hps : p ≠ s) (hqs : q ≠ s)
    (hrs : r ≠ s) (hr : signedCollinear p q r) (hs : signedCollinear p q s) :
    mixedProductSpace nativeEqualCubic (plane p) (plane q) = plane r ⊔ plane s := by
  have hsub (k : SignedPlaneIndex) (hpk : p ≠ k) (hqk : q ≠ k) (hk : signedCollinear p q k) :
      plane k ≤ mixedProductSpace nativeEqualCubic (plane p) (plane q) := by
    apply (planeShare_bounds nativeEqualCubic decomposition p q k).2.1.mp
    rw [share_eq_collinearity p q k hpq hpk hqk, ite_eq_left hk]
  apply (Submodule.eq_of_le_of_finrank_eq (sup_le (hsub r hpr hqr hr) (hsub s hps hqs hs)) ?_).symm
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (plane r) (plane s)
  rw [(plane_orthogonal hrs).disjoint.eq_bot, finrank_bot, add_zero, plane_finrank, plane_finrank] at hd
  have hm : Module.finrank ℝ (mixedProductSpace nativeEqualCubic (plane p) (plane q)) = 4 :=
    mixedProductSpace_finrank nativeRound (plane_orthogonal hpq) (closedPlanes p) (closedPlanes q)
      (plane_finrank p) (plane_finrank q)
  exact hd.trans hm.symm

private def pointLabels : Fin 13 ≃ SignedPlaneIndex :=
  (Fintype.equivFinOfCardEq signedPlaneIndex_card).symm

/-- A labelled version of the native graded system for counting unordered shares. -/
def labelledDecomposition : PlaneDecomposition NativeTraceless (Fin 13) :=
  nativeCode.decomposition

theorem labelled_plane_eq (i : Fin 13) :
    labelledDecomposition.plane i = decomposition.plane (pointLabels i) :=
  nativeFramePlane_point (pointLabels i)

theorem labelledClosedPlanes : IsClosedPlaneSystem nativeEqualCubic labelledDecomposition := by
  intro i
  rw [labelled_plane_eq]
  exact closedPlanes (pointLabels i)

/-- The concrete graded native frames attain 52 positive shares. -/
theorem native_graded_support_fifty_two :
    (positivePlaneTriples nativeEqualCubic labelledDecomposition).card = 52 := by
  apply (thirteenPlane_positive_eq_fifty_two_iff nativeRound labelledClosedPlanes).mpr
  intro i j k hij hki hkj
  have he : planeShare nativeEqualCubic labelledDecomposition i j k =
      planeShare nativeEqualCubic decomposition (pointLabels i) (pointLabels j) (pointLabels k) := by
    rw [planeShare_eq_shareOfThreePlanes, planeShare_eq_shareOfThreePlanes,
      labelled_plane_eq, labelled_plane_eq, labelled_plane_eq]
  rw [he, share_eq_collinearity
    (pointLabels i) (pointLabels j) (pointLabels k) (pointLabels.injective.ne hij)
    (pointLabels.injective.ne hki.symm) (pointLabels.injective.ne hkj.symm)]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The minimum is attained by an actual family of thirteen native frames. -/
theorem native_frames_exist_fifty_two_shares :
    ∃ code : TightNativeCode, (positivePlaneTriples nativeEqualCubic code.decomposition).card = 52 :=
  ⟨nativeCode, native_graded_support_fifty_two⟩

/-- The native Albert cubic has an actual orthogonal closed system with minimum share support. -/
theorem native_exists_fifty_two_shares :
    ∃ P : PlaneDecomposition NativeTraceless (Fin 13),
      IsClosedPlaneSystem nativeEqualCubic P ∧ (positivePlaneTriples nativeEqualCubic P).card = 52 :=
  ⟨labelledDecomposition, labelledClosedPlanes, native_graded_support_fifty_two⟩

end

end ThirteenPlanes.Graded
