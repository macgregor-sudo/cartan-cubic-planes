module

public import ThirteenPlanes.AlbertGrading.Recut.Image

@[expose] public section

set_option backward.privateInPublic true

/-! # re-cut systems

The target `Targets.OtherSystems` is proved from the facts of the ternary grading theorem listed in
`Section5.GradedFacts`, by instantiating the generic re-cut theorems of `Frames`, `Count` and
`Image` at the graded frames of an arbitrary ternary grading group. -/

namespace ThirteenPlanes.AlbertGrading.Recut

open ThirteenPlanes.RoundCubics

noncomputable section

/-- "`φ` permutes the planes of `l`" for an arbitrary copy `Q` of the qutrit of `l`. -/
def PermutesQ (Q : Submodule ℝ Glennie.Albert) (φ : Q ≃ₗ[ℝ] Q)
    (P : SignedPlaneIndex → Fin 3 → Glennie.Albert) (l : SignedPlaneIndex) : Prop :=
  ∃ σ : {p : SignedPlaneIndex // signedPointOnLine p l} ≃
      {p : SignedPlaneIndex // signedPointOnLine p l},
    ∀ p x, x ∈ planeA (P (σ p).val) ↔
      ∃ y : Q, (y : Glennie.Albert) ∈ planeA (P p.val) ∧ (φ y : Glennie.Albert) = x

/-- The generic statement for every subspace equal to `lineQ P l`. -/
theorem recut_generic {P : SignedPlaneIndex → Fin 3 → Glennie.Albert}
    (hF : ∀ p, Glennie.Frame (P p))
    (hU : ∀ p q, p ≠ q → ∀ a b, Glennie.inner (P p a) (P q b) = 1 / 3)
    (hclosedAll : ∀ m : SignedPlaneIndex, ∀ x y, x ∈ lineQ P m → y ∈ lineQ P m →
      Glennie.jordan x y ∈ lineQ P m)
    (hmix : ∀ p q r r' : SignedPlaneIndex, p ≠ q → r ≠ r' → r ≠ p → r ≠ q → r' ≠ p → r' ≠ q →
      signedCollinear p q r → signedCollinear p q r' →
      mixedProductSpace nativeEqualCubic (nativeFramePlane (P p)) (nativeFramePlane (P q)) =
        nativeFramePlane (P r) ⊔ nativeFramePlane (P r'))
    (hshare : ∀ p q r : SignedPlaneIndex, p ≠ q → p ≠ r → q ≠ r →
      shareOfThreePlanes nativeEqualCubic (nativeFramePlane (P p)) (nativeFramePlane (P q))
        (nativeFramePlane (P r)) = if signedCollinear p q r then 1 else 0)
    (l : SignedPlaneIndex) (Q : Submodule ℝ Glennie.Albert) (hQ : Q = lineQ P l)
    (φ : Q ≃ₗ[ℝ] Q) (hφ : IsSubalgebraAutomorphism Q φ) :
    ((∀ p, Glennie.Frame (recutG Q φ P l p)) ∧
      (∀ p q, p ≠ q → ∀ a b, Glennie.inner (recutG Q φ P l p a) (recutG Q φ P l q b) = 1 / 3) ∧
      (∀ e : Fin 13 ≃ SignedPlaneIndex, ∃ c : TightNativeCode,
        ∀ i, c.point i = recutG Q φ P l (e i))) ∧
    (∀ (c : TightNativeCode) (e : Fin 13 ≃ SignedPlaneIndex),
      (∀ i, c.point i = recutG Q φ P l (e i)) →
      ((positivePlaneTriples nativeEqualCubic c.decomposition).card = 52 ↔ PermutesQ Q φ P l)) ∧
    (¬ PermutesQ Q φ P l →
      ¬ ∃ ψ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert, IsJordanAutomorphism ψ ∧
        CarriesG P ψ (recutG Q φ P l)) := by
  subst hQ
  obtain ⟨hRF, hRU⟩ := recutG_frames hF hU (hclosedAll l) hφ
  exact ⟨⟨hRF, hRU, fun e => ⟨codeOf _ hRF hRU e, fun _ => rfl⟩⟩,
    fun c e hc => recutG_card_iff hF hU (hclosedAll l) hφ hmix hshare c e hc,
    recutG_not_image hF hU hclosedAll hφ hmix hshare⟩

private theorem rep_ne_neg {p q : SignedPlaneIndex} : q.val.val ≠ -p.val.val := by
  intro h
  have hq := q.property
  rw [h] at hq
  exact ((oppositeCharge_isRepresentative_iff p.val).mp hq) p.property

private theorem rep_ne {p q : SignedPlaneIndex} (hpq : p ≠ q) : q.val.val ≠ p.val.val := by
  intro h
  exact hpq (Subtype.ext (Subtype.ext h.symm))

/-- Rotation of four planes on a graded line, both clauses, from the facts of the ternary grading theorem it uses. -/
theorem otherSystems (hG : GradingData.GradedFacts) : Statements.OtherSystems := by
  intro ρ hρ u P0 hP0 l φ hφ
  obtain ⟨hii, hiii, hiv, hivs, hv⟩ := hG ρ hρ
  let P : SignedPlaneIndex → Fin 3 → Glennie.Albert := fun p => P0 p.val.val
  have hF (p : SignedPlaneIndex) : Glennie.Frame (P p) := (hP0 _ p.val.property).2.2.1
  have hplane (p : SignedPlaneIndex) :
      nativeFramePlane (P p) = pointPlane ρ p ∧ gradedPlaneJ ρ p.val.val = planeA (P p) := by
    have hg := hP0 _ p.val.property
    obtain ⟨p', hfr, hpl, hker⟩ := hii _ p.val.property (u _) hg.1 hg.2.1
    have hpp : p' = P p := by
      funext a
      have h := (hfr.2 a).trans (hg.2.2.2 a).symm
      exact congrArg JC.re h
    rw [hpp] at hpl
    refine ⟨hpl, ?_⟩
    rw [planeA, hpl, gradedPlane, Submodule.map_comap_eq, Submodule.range_subtype]
    exact (inf_eq_right.mpr hker).symm
  have hPl (p : SignedPlaneIndex) : pointPlane ρ p = nativeFramePlane (P p) := (hplane p).1.symm
  have hJ (p : SignedPlaneIndex) : gradedPlaneJ ρ p.val.val = planeA (P p) := (hplane p).2
  have hU (p q : SignedPlaneIndex) (hpq : p ≠ q) (a b : Fin 3) :
      Glennie.inner (P p a) (P q b) = 1 / 3 :=
    hiii u P0 hP0 _ _ p.val.property q.val.property (rep_ne hpq) rep_ne_neg a b
  have hQ (m : SignedPlaneIndex) : lineAlgebraOf ρ m = lineQ P m := by
    simp only [lineAlgebraOf, lineQ, hJ]
  have hclosedAll (m : SignedPlaneIndex) (x y : Glennie.Albert) (hx : x ∈ lineQ P m)
      (hy : y ∈ lineQ P m) : Glennie.jordan x y ∈ lineQ P m := by
    rw [← hQ] at hx hy ⊢
    exact hv m x y hx hy
  have hmix : ∀ p q r r' : SignedPlaneIndex, p ≠ q → r ≠ r' → r ≠ p → r ≠ q → r' ≠ p →
      r' ≠ q → signedCollinear p q r → signedCollinear p q r' →
      mixedProductSpace nativeEqualCubic (nativeFramePlane (P p)) (nativeFramePlane (P q)) =
        nativeFramePlane (P r) ⊔ nativeFramePlane (P r') := by
    intro p q r r' h1 h2 h3 h4 h5 h6 h7 h8
    have h := hiv p q r r' h1 h2 h3 h4 h5 h6 h7 h8
    rwa [hPl, hPl, hPl, hPl] at h
  have hshare : ∀ p q r : SignedPlaneIndex, p ≠ q → p ≠ r → q ≠ r →
      shareOfThreePlanes nativeEqualCubic (nativeFramePlane (P p)) (nativeFramePlane (P q))
        (nativeFramePlane (P r)) = if signedCollinear p q r then 1 else 0 := by
    intro p q r h1 h2 h3
    have h := hivs p q r h1 h2 h3
    rwa [hPl, hPl, hPl] at h
  obtain ⟨hi, hii', hiii'⟩ :=
    recut_generic hF hU hclosedAll hmix hshare l (lineAlgebraOf ρ l) (hQ l) φ hφ
  have hperm : PermutesLinePlanes ρ l φ ↔ PermutesQ (lineAlgebraOf ρ l) φ P l := by
    simp only [PermutesLinePlanes, PermutesQ, hJ]
  have hcar (ψ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert) :
      CarriesGradedTo ρ ψ (recutFrame ρ l φ P0) ↔
        CarriesG P ψ (recutG (lineAlgebraOf ρ l) φ P l) := by
    simp only [CarriesGradedTo, CarriesG, hJ]
    rfl
  refine ⟨hi, fun c e hc => (hii' c e hc).trans hperm.symm, fun hnot => ?_⟩
  rintro ⟨ψ, hψ, hψc⟩
  exact hiii' (fun h => hnot (hperm.mpr h)) ⟨ψ, hψ, (hcar ψ).mp hψc⟩

end

end ThirteenPlanes.AlbertGrading.Recut
