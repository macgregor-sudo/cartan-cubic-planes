module

public import ThirteenPlanes.AlbertGrading.Grading.GradedIncidence
public import ThirteenPlanes.Cartan.AlbertInvariant
public import ThirteenPlanes.ClosedBlocks.Transport

@[expose] public section

set_option backward.privateInPublic true

/-! An unchanged affine complement determines the four original graded line planes. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading RoundCubics

noncomputable section

private theorem completing_points_on_line (l a b : SignedPlaneIndex) (hab : a ≠ b)
    (ha : signedPointOnLine a l) (hb : signedPointOnLine b l) :
    ∃ r s : SignedPlaneIndex, r ≠ s ∧ r ≠ a ∧ r ≠ b ∧ s ≠ a ∧ s ≠ b ∧
      signedPointOnLine r l ∧ signedPointOnLine s l := by
  let S := (signedLinePoints l).erase a
  let T := S.erase b
  have ha' : a ∈ signedLinePoints l := by simpa [signedLinePoints] using ha
  have hb' : b ∈ S := by simp [S, signedLinePoints, hab.symm, hb]
  have hcard : T.card = 2 := by
    change (S.erase b).card = 2
    rw [Finset.card_erase_of_mem hb']
    change ((signedLinePoints l).erase a).card - 1 = 2
    rw [Finset.card_erase_of_mem ha', signedLinePoints_card]
  obtain ⟨r, s, hrs, hT⟩ := Finset.card_eq_two.mp hcard
  have hr : r ∈ T := by rw [hT]; simp
  have hs : s ∈ T := by rw [hT]; simp
  have unpack (x : SignedPlaneIndex) (hx : x ∈ T) :
      x ≠ b ∧ x ≠ a ∧ signedPointOnLine x l := by
    simpa [T, S, signedLinePoints] using hx
  obtain ⟨hrb, hra, hrl⟩ := unpack r hr
  obtain ⟨hsb, hsa, hsl⟩ := unpack s hs
  exact ⟨r, s, hrs, hra, hrb, hsa, hsb, hrl, hsl⟩

private theorem two_completing_points (a b : SignedPlaneIndex) (hab : a ≠ b) :
    ∃ r s : SignedPlaneIndex, r ≠ s ∧ r ≠ a ∧ r ≠ b ∧ s ≠ a ∧ s ≠ b ∧
      signedCollinear a b r ∧ signedCollinear a b s := by
  obtain ⟨l, ⟨ha, hb⟩, _⟩ := Graded.unique_joining_line a b hab
  obtain ⟨r, s, hrs, hra, hrb, hsa, hsb, hrl, hsl⟩ := completing_points_on_line l a b hab ha hb
  exact ⟨r, s, hrs, hra, hrb, hsa, hsb, ⟨l, ha, hb, hrl⟩, ⟨l, ha, hb, hsl⟩⟩

private theorem offLine_pair_for_point (l r : SignedPlaneIndex) (hr : signedPointOnLine r l) :
    ∃ a b s : SignedPlaneIndex, a ≠ b ∧ r ≠ s ∧ r ≠ a ∧ r ≠ b ∧ s ≠ a ∧ s ≠ b ∧
      ¬ signedPointOnLine a l ∧ ¬ signedPointOnLine b l ∧ ¬ signedPointOnLine s l ∧
      signedCollinear a b r ∧ signedCollinear a b s := by
  have hc : (signedLinePoints l).card < (Finset.univ : Finset SignedPlaneIndex).card := by
    rw [signedLinePoints_card, Finset.card_univ, signedPlaneIndex_card]
    decide
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hal : ¬ signedPointOnLine a l := by simpa [signedLinePoints] using ha
  have har : a ≠ r := fun e => hal (e.symm ▸ hr)
  obtain ⟨m, ⟨ham, hrm⟩, _⟩ := Graded.unique_joining_line a r har
  obtain ⟨b, s, hbs, hba, hbr, hsa, hsr, hbm, hsm⟩ :=
    completing_points_on_line m a r har ham hrm
  have outside (x : SignedPlaneIndex) (hx : x ≠ r) (hxm : signedPointOnLine x m) :
      ¬ signedPointOnLine x l := by
    intro hxl
    obtain ⟨n, _, huniq⟩ := Graded.unique_joining_line x r hx
    have e : m = l := (huniq m ⟨hxm, hrm⟩).trans (huniq l ⟨hxl, hr⟩).symm
    exact hal (e ▸ ham)
  exact ⟨a, b, s, hba.symm, hsr.symm, har.symm, hbr.symm, hsa, hbs.symm,
    hal, outside b hbr hbm, outside s hsr hsm, ⟨m, ham, hbm, hrm⟩, ⟨m, ham, hbm, hsm⟩⟩

section Metric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem mixedProductSpace_map_isometry (d : SymmetricCubic V) (G : V ≃ₗᵢ[ℝ] V)
    (hG : d = d.pullback G.toLinearMap) (U W : Submodule ℝ V) :
    (mixedProductSpace d U W).map G.toLinearMap =
      mixedProductSpace d (U.map G.toLinearMap) (W.map G.toLinearMap) := by
  simp only [mixedProductSpace_eq_span]
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.map₂_le.mpr
    intro x hx y hy
    change G (d.L x y) ∈ Submodule.map₂ d.L (U.map G.toLinearMap) (W.map G.toLinearMap)
    rw [Peirce.pullback_intertwines_product G hG]
    exact Submodule.apply_mem_map₂ d.L ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  · apply Submodule.map₂_le.mpr
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨d.L x y, Submodule.apply_mem_map₂ d.L hx hy,
      Peirce.pullback_intertwines_product G hG x y⟩

omit [FiniteDimensional ℝ V] in
private theorem isOrtho_sup_cancel {A P Q : Submodule ℝ V} (hoP : P.IsOrtho A) (hoQ : Q.IsOrtho A)
    (heq : P ⊔ A = Q ⊔ A) : P = Q := by
  have h := congrArg (· ⊓ Aᗮ) heq
  rw [sup_inf_assoc_of_le _ (Submodule.isOrtho_iff_le.mp hoP),
    sup_inf_assoc_of_le _ (Submodule.isOrtho_iff_le.mp hoQ),
    Submodule.inf_orthogonal_eq_bot, sup_bot_eq, sup_bot_eq] at h
  exact h

end Metric

/-- The actual compact Albert action preserves the native cubic. -/
theorem albertTracelessAction_preserves_cubic (G : Glennie.CompactAutomorphism) :
    nativeEqualCubic = nativeEqualCubic.pullback (albertTracelessAction G).toLinearMap := by
  apply SymmetricCubic.ext
  intro x y z
  rw [SymmetricCubic.pullback_apply]
  change Glennie.inner (Glennie.traceless (Glennie.jordan x.val y.val)) z.val =
    Glennie.inner (Glennie.traceless (Glennie.jordan (G.equiv x.val) (G.equiv y.val))) (G.equiv z.val)
  rw [← G.map_jordan, ← G.map_traceless, G.inner_map]

/-- If a family agrees with the native graded planes off one projective line
and is a cubic-isometric reindexing of the original family, its planes on that
line must be a permutation of the four original line planes. -/
theorem recutLine_permuted_of_planeConjugacy {ρ : TernaryAction} (hρ : IsTernaryGrading ρ)
    (l : SignedPlaneIndex) (Q : SignedPlaneIndex → Submodule ℝ NativeTraceless)
    (hoff : ∀ p, ¬ signedPointOnLine p l → Q p = pointPlane ρ p)
    (G : NativeTraceless ≃ₗᵢ[ℝ] NativeTraceless)
    (hG : nativeEqualCubic = nativeEqualCubic.pullback G.toLinearMap)
    (e : Equiv.Perm SignedPlaneIndex)
    (hconj : ∀ p, (pointPlane ρ p).map G.toLinearMap = Q (e p)) :
    ∃ σ : Equiv.Perm {p // signedPointOnLine p l},
      ∀ p : {p // signedPointOnLine p l}, Q p.val = pointPlane ρ (σ p).val := by
  classical
  let P := pointPlane ρ
  have hp : Pairwise fun a b => (P a).IsOrtho (P b) := pointPlane_orthogonal hρ
  have hQmap (a : SignedPlaneIndex) : Q a = (P (e.symm a)).map G.toLinearMap := by
    have h := (hconj (e.symm a)).symm
    rwa [e.apply_symm_apply] at h
  have hqo : Pairwise fun a b => (Q a).IsOrtho (Q b) := by
    intro a b hab
    rw [hQmap a, hQmap b]
    exact isOrtho_map_isometry G (hp (e.symm.injective.ne hab))
  have hpbot (r : SignedPlaneIndex) : P r ≠ ⊥ := by
    intro hb
    have hh := pointPlane_finrank hρ r
    change Module.finrank ℝ (P r) = 2 at hh
    rw [hb, finrank_bot] at hh
    omega
  have hcover (r : SignedPlaneIndex) (hr : signedPointOnLine r l) :
      ∃ j : SignedPlaneIndex, signedPointOnLine j l ∧ Q j = P r := by
    obtain ⟨a, b, s, hab, hrs, hra, hrb, hsa, hsb, hal, hbl, hsl, hcolr, hcols⟩ :=
      offLine_pair_for_point l r hr
    have old : mixedProductSpace nativeEqualCubic (P a) (P b) = P r ⊔ P s :=
      graded_mixed hρ a b r s hab hrs hra hrb hsa hsb hcolr hcols
    let u := e.symm a
    let v := e.symm b
    have huv : u ≠ v := e.symm.injective.ne hab
    obtain ⟨j₀, k₀, hjk, hju, hjv, hku, hkv, hcj, hck⟩ := two_completing_points u v huv
    have base : mixedProductSpace nativeEqualCubic (P u) (P v) = P j₀ ⊔ P k₀ :=
      graded_mixed hρ u v j₀ k₀ huv hjk hju hjv hku hkv hcj hck
    have hmap := congrArg (Submodule.map G.toLinearMap) base
    rw [mixedProductSpace_map_isometry nativeEqualCubic G hG,
      Submodule.map_sup, hconj, hconj, hconj, hconj] at hmap
    have heu : e u = a := e.apply_symm_apply a
    have hev : e v = b := e.apply_symm_apply b
    rw [heu, hev, hoff a hal, hoff b hbl, old] at hmap
    let j := e j₀
    let k := e k₀
    have hjk' : j ≠ k := e.injective.ne hjk
    have hs : s = j ∨ s = k := by
      by_contra! hs
      have hle : Q s ≤ Q j ⊔ Q k := by
        rw [hoff s hsl, ← hmap]
        exact le_sup_right
      have hperp : (Q s).IsOrtho (Q j ⊔ Q k) :=
        Submodule.isOrtho_sup_right.mpr ⟨hqo hs.1, hqo hs.2⟩
      have hzero : Q s ≤ (Q s)ᗮ := hle.trans (Submodule.isOrtho_iff_le.mp hperp.symm)
      have hbot : Q s = ⊥ := by
        have hle' : Q s ≤ Q s ⊓ (Q s)ᗮ := le_inf le_rfl hzero
        rw [Submodule.inf_orthogonal_eq_bot] at hle'
        exact le_bot_iff.mp hle'
      exact hpbot s ((hoff s hsl).symm.trans hbot)
    have remaining (j k : SignedPlaneIndex) (hjk : j ≠ k) (hsj : s = j)
        (hjoin : P r ⊔ P s = Q j ⊔ Q k) :
        signedPointOnLine k l ∧ Q k = P r := by
      subst j
      have hjoin' : P r ⊔ P s = Q k ⊔ P s := by
        rw [hjoin, hoff s hsl, sup_comm]
      have hkos : (Q k).IsOrtho (P s) := by
        have hs' : Q s = P s := hoff s hsl
        rw [← hs']
        exact hqo hjk.symm
      have heq := (isOrtho_sup_cancel (hp hrs) hkos hjoin').symm
      refine ⟨?_, heq⟩
      by_contra hk
      have he : P k = P r := (hoff k hk).symm.trans heq
      have hkr : k ≠ r := fun e => hk (e.symm ▸ hr)
      have horth : (P k).IsOrtho (P r) := hp hkr
      rw [he] at horth
      have hbot := horth.disjoint.eq_bot
      rw [inf_idem] at hbot
      exact hpbot r hbot
    rcases hs with hsj | hsk
    · exact ⟨k, remaining j k hjk' hsj hmap⟩
    · exact ⟨j, remaining k j hjk'.symm hsk (hmap.trans (sup_comm _ _))⟩
  let L := {p : SignedPlaneIndex // signedPointOnLine p l}
  have H (p : L) : ∃ q : L, Q q.val = P p.val := by
    obtain ⟨q, hq, heq⟩ := hcover p.val p.property
    exact ⟨⟨q, hq⟩, heq⟩
  choose f hf using H
  have hinj : Function.Injective f := by
    intro p q hpq
    by_contra hne
    have hv : p.val ≠ q.val := fun h => hne (Subtype.ext h)
    have h : (P p.val).IsOrtho (P q.val) := hp hv
    have he : P p.val = P q.val := (hf p).symm.trans
      ((congrArg (fun r : L => Q r.val) hpq).trans (hf q))
    rw [he] at h
    have hbot := h.disjoint.eq_bot
    rw [inf_idem] at hbot
    exact hpbot q.val hbot
  let E : L ≃ L := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨E.symm, fun p => ?_⟩
  have hh := hf (E.symm p)
  change Q (E (E.symm p)).val = _ at hh
  rwa [E.apply_symm_apply] at hh

end

end ThirteenPlanes.Cartan
