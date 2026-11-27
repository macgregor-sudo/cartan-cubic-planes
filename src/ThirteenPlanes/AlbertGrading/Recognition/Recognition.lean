module

public import ThirteenPlanes.AlbertGrading.Recognition.Lines

@[expose] public section

/-!
# recognition in `J_T`

The set `M` of the lines `ℂe`, `ℂu_f`, `ℂσu_f` has at most 27
members. It contains `ℂ ι₀(D_v)` (the eigenframes) and `ℂ ι₁(1)`, `ℂ ι₂(1)` (the exterior frame).
The product `ι₀(D_v) ∘ ι₁(1) = -½ ι₁(D_v)` and the hypothesis put the nine lines `ℂ ι₁(D_v)` in `M`,
and `σ` the nine lines `ℂ ι₂(D_v)`. These are 27 distinct lines, so `M` is the set of lines `ℂu_g`;
`frame_of_line` (the relations `u∘u = σu`, `u∘σu = e` and Fourier inversion) finishes.
The hypothesis is used only for the four pairs (eigenframe, exterior frame).
-/

open scoped Matrix BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

theorem titsBasis_exterior :
    titsBasis (chargeFrom 0 2) = ((0 : Mat3 ℂ), (0 : Mat3 ℂ), (1 : Mat3 ℂ)) := by
  have hw : weylD (0, 0) = 1 := by simp [weylD]
  simp only [titsBasis, chargeFrom_third, chargeFrom_first, chargeFrom_second, Prod.fst_zero,
    Prod.snd_zero, iota, hw, show (2 : ZMod 3) ≠ 0 by decide, show (2 : ZMod 3) ≠ 1 by decide,
    if_false, if_true, ite_true, ite_false]
  simp only [if_false, if_true, ite_true, ite_false, ↓reduceIte]
  rfl

theorem exterior_range :
    Set.range exteriorPoint = Set.range (gradedFrame (chargeFrom 0 2)) :=
  range_eq_of_line exteriorPoint_isFrame (l := 1)
    (by rw [exteriorPoint_contrast, titsBasis_exterior, one_smul])

theorem eigen_ne_exterior (v : WeylLabel) :
    Set.range (weylEigenframe v) ≠ Set.range exteriorPoint := by
  intro h
  obtain ⟨b, hb⟩ : exteriorPoint 0 ∈ Set.range (weylEigenframe v) := h ▸ Set.mem_range_self 0
  have := congrArg (fun x => (CompactTits.coordinates x).2.1 0 0) hb
  simp only [weylEigenframe, gradedFrame_coordinates, gradedCoords, titsBasis, iota, Pi.neg_apply,
    chargeFrom_third, neg_zero, firstTitsOne, show (0 : ZMod 3) ≠ 1 by decide, if_false,
    Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, exteriorPoint_coordinates,
    Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, chargePhase_zero,
    mul_one] at this
  norm_num at this

theorem chargeFrom_ne_zero {v : WeylLabel} (hv : v ≠ 0) (k : ZMod 3) : chargeFrom v k ≠ 0 := by
  intro h
  apply hv
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [chargeFrom_first, chargeFrom_second, Pi.zero_apply] at h0 h1
  exact Prod.ext h0 h1

theorem indep_visible_hidden {v : WeylLabel} (hv : v ≠ 0) :
    ¬ F3Dependent (chargeFrom v 0) (chargeFrom 0 1) := by
  rintro ⟨a, b, hab, h⟩
  have h2 := congrFun h 2
  simp only [Pi.add_apply, Pi.smul_apply, chargeFrom_third, smul_eq_mul, mul_zero, mul_one,
    zero_add, Pi.zero_apply] at h2
  subst h2
  rcases hab with ha | hb
  · apply chargeFrom_ne_zero hv 0
    have h' : a • chargeFrom v 0 = 0 := by simpa using h
    have := congrArg (fun x => a⁻¹ • x) h'
    simpa [smul_smul, inv_mul_cancel₀ ha] using this
  · exact hb rfl

theorem recognition : Statements.Recognition := by
  classical
  intro F hF hEig hExt hProd
  set M : Finset (FirstTits ℂ) := insert firstTitsOne
    ((Finset.univ.image fun i => titsContrast (F i)) ∪
      (Finset.univ.image fun i => compactInvolution (titsContrast (F i)))) with hMdef
  have hM1 : ∀ i, titsContrast (F i) ∈ M := fun i =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hM2 : ∀ i, compactInvolution (titsContrast (F i)) ∈ M := fun i =>
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hσone : compactInvolution firstTitsOne = firstTitsOne := by
    rw [← titsBasis_zero, titsBasis_involution, neg_zero]
  have hMlines : ∀ m, m ∈ titsContrastLines F → m ∈ M := by
    rintro m ((h | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · rw [Set.mem_singleton_iff.mp h]; exact Finset.mem_insert_self _ _
    · exact hM1 i
    · exact hM2 i
  have hσM : ∀ m ∈ M, compactInvolution m ∈ M := by
    intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · rw [hσone]; exact Finset.mem_insert_self _ _
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
      exact hM2 i
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
      rw [compactInvolution_involutive]
      exact hM1 i
  let InM : FirstTits ℂ → Prop := fun w => ∃ m ∈ M, ∃ c : ℂ, c ≠ 0 ∧ w = c • m
  have hInM : ∀ m ∈ M, InM m := fun m hm => ⟨m, hm, 1, one_ne_zero, (one_smul _ _).symm⟩
  have hσ : ∀ w, InM w → InM (compactInvolution w) := by
    rintro w ⟨m, hm, c, hc, rfl⟩
    exact ⟨_, hσM m hm, star c, star_ne_zero.mpr hc, compactInvolution_complex_smul c m⟩
  have hscale : ∀ w (c : ℂ), c ≠ 0 → InM (c • w) → InM w := by
    rintro w c hc ⟨m, hm, d, hd, h⟩
    refine ⟨m, hm, c⁻¹ * d, mul_ne_zero (inv_ne_zero hc) hd, ?_⟩
    rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hpair : ∀ i x, x ∈ ({titsContrast (F i), compactInvolution (titsContrast (F i))} :
      Set (FirstTits ℂ)) → x ∈ M := by
    rintro i x (rfl | rfl)
    exacts [hM1 i, hM2 i]
  -- the exterior frame
  obtain ⟨j0, hj0⟩ := hExt
  have hne02 : chargeFrom 0 2 ≠ 0 := by
    intro h
    have := congrFun h 2
    simp only [chargeFrom_third, Pi.zero_apply] at this
    exact absurd this (by decide)
  obtain ⟨y, hy, ζ', hζ', hye⟩ :=
    contrast_of_range (hF j0) hne02 (hj0.trans exterior_range)
  have hneg02 : -chargeFrom 0 2 = chargeFrom 0 1 := by
    rw [← chargeFrom_neg, neg_zero]; rfl
  have hσy : compactInvolution y = star ζ' • titsBasis (chargeFrom 0 1) := by
    rw [hye, compactInvolution_complex_smul, titsBasis_involution, hneg02]
  have hσymem : compactInvolution y ∈
      ({titsContrast (F j0), compactInvolution (titsContrast (F j0))} : Set (FirstTits ℂ)) := by
    rcases hy with rfl | rfl
    · exact Or.inr rfl
    · rw [compactInvolution_involutive]; exact Or.inl rfl
  -- the eigenframes
  have heig : ∀ v : WeylLabel, v ≠ 0 → ∃ i, ∃ x ∈ ({titsContrast (F i),
      compactInvolution (titsContrast (F i))} : Set (FirstTits ℂ)), ∃ ζ : ℂ, ζ ≠ 0 ∧
        x = ζ • titsBasis (chargeFrom v 0) ∧ Set.range (F i) = Set.range (weylEigenframe v) := by
    intro v hv
    obtain ⟨i, hi⟩ := hEig v hv
    obtain ⟨x, hx, ζ, hζ, hxe⟩ := contrast_of_range (hF i) (chargeFrom_ne_zero hv 0) hi
    exact ⟨i, x, hx, ζ, hζ, hxe, hi⟩
  -- the nine lines `ℂ ι₁(D_v)`, `v ≠ 0`
  have hone : ∀ v : WeylLabel, v ≠ 0 → InM (titsBasis (chargeFrom v 1)) := by
    intro v hv
    obtain ⟨i, x, hx, ζ, hζ, hxe, hi⟩ := heig v hv
    have hdiff : Set.range (F i) ≠ Set.range (F j0) := by
      rw [hi, hj0]; exact eigen_ne_exterior v
    obtain ⟨c, hc, m, hm, hprod⟩ := hProd i j0 hdiff x hx _ hσymem
    rw [hxe, hσy, firstTitsJordanProduct_smul_smul,
      titsBasis_product_independent v 0 0 1 (indep_visible_hidden hv), smul_smul,
      ← chargeFrom_add, add_zero, zero_add] at hprod
    refine hscale _ _ ?_ ⟨m, hMlines m hm, c, hc, hprod⟩
    refine mul_ne_zero (mul_ne_zero hζ (star_ne_zero.mpr hζ')) (mul_ne_zero (by norm_num)
      (chargePhase_ne_zero' _))
  have hall : ∀ g : Charge, InM (titsBasis g) := by
    intro g
    obtain ⟨⟨k, v⟩, rfl⟩ := chargeComponentEquiv.surjective g
    change InM (titsBasis (chargeFrom v k))
    rcases (show ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 2 by decide) k with rfl | rfl | rfl
    · by_cases hv : v = 0
      · subst hv
        rw [chargeFrom_zero, titsBasis_zero]
        exact hInM _ (Finset.mem_insert_self _ _)
      · obtain ⟨i, x, hx, ζ, hζ, hxe, -⟩ := heig v hv
        exact hscale _ ζ hζ (hxe ▸ hInM x (hpair i x hx))
    · by_cases hv : v = 0
      · subst hv
        exact hscale _ _ (star_ne_zero.mpr hζ') (hσy ▸ hInM _ (hpair j0 _ hσymem))
      · exact hone v hv
    · by_cases hv : v = 0
      · subst hv
        exact hscale _ ζ' hζ' (hye ▸ hInM y (hpair j0 y hy))
      · have h := hσ _ (hone (-v) (neg_ne_zero.mpr hv))
        rwa [titsBasis_involution, ← chargeFrom_neg, neg_neg,
          show (-1 : ZMod 3) = 2 by decide] at h
  -- counting the lines
  let Φ : Charge → Submodule ℂ (FirstTits ℂ) := fun g => Submodule.span ℂ {titsBasis g}
  have hΦinj : Function.Injective Φ := by
    intro g h hgh
    have hmem : titsBasis g ∈ Φ h := hgh ▸ Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have := congrArg (coef g) hc
    rw [map_smul, coef_titsBasis, coef_titsBasis, if_pos rfl] at this
    by_contra hne
    rw [if_neg hne, smul_zero] at this
    exact zero_ne_one this
  let Lines := M.image fun m => Submodule.span ℂ {m}
  have hsub : Finset.univ.image Φ ⊆ Lines := by
    intro L hL
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨m, hm, c, hc, he⟩ := hall g
    refine Finset.mem_image.mpr ⟨m, hm, ?_⟩
    change Submodule.span ℂ {m} = Submodule.span ℂ {titsBasis g}
    rw [he, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]
  have hcard : (Finset.univ.image Φ).card = 27 := by
    rw [Finset.card_image_of_injective _ hΦinj, Finset.card_univ]
    show Fintype.card (Fin 3 → ZMod 3) = 27
    simp
  have hLines : Lines.card ≤ 27 := by
    refine (Finset.card_image_le).trans ((Finset.card_insert_le _ _).trans ?_)
    have := Finset.card_union_le (Finset.univ.image fun i => titsContrast (F i))
      (Finset.univ.image fun i => compactInvolution (titsContrast (F i)))
    have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin 13)))
      (f := fun i => titsContrast (F i))
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin 13)))
      (f := fun i => compactInvolution (titsContrast (F i)))
    simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
    omega
  have heq : Finset.univ.image Φ = Lines :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro i
  have hi : Submodule.span ℂ {titsContrast (F i)} ∈ Lines := Finset.mem_image_of_mem _ (hM1 i)
  rw [← heq] at hi
  obtain ⟨g, -, hg⟩ := Finset.mem_image.mp hi
  have hmem : titsContrast (F i) ∈ Φ g := by
    change titsContrast (F i) ∈ Submodule.span ℂ {titsBasis g}
    rw [show Submodule.span ℂ {titsBasis g} = Submodule.span ℂ {titsContrast (F i)} from hg]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨g, ?_, range_eq_of_line (hF i) hl.symm⟩
  rintro rfl
  have ht := contrast_trace (hF i)
  rw [← hl, map_smul, tr1_titsBasis, if_pos rfl, smul_eq_mul] at ht
  have hl0 : l = 0 := by linear_combination ht / 3
  apply contrast_ne_zero (hF i)
  rw [← hl, hl0, zero_smul]

end

end ThirteenPlanes.AlbertGrading
