module

public import ThirteenPlanes.AlbertGrading.Contrast.Transport

@[expose] public section

/-!
# the contrast table of a quartet in a qutrit

The isomorphism preserves traces (`iso_unit_trace`), so the four
frames go to four unbiased frames of `Herm₃(ℂ)`; `FrameProperties.QutritFourFrames` (the four-plane theorem (iii)
in frame form) moves them to the eigenframes of the `D_v`; the complex extension carries each
contrast to `ζ D_v` with `ζ ∈ μ₃` (the Fourier contrast identities (i)); `(5-weyl-jordan)` gives the products.
Dependent pairs follow from the Fourier contrast identities (i) alone.
-/

open scoped Matrix

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Contrast Contrast.AlbertC Graded

namespace Contrast

theorem mu3_ne_zero {ζ : ℂ} (h : ζ ∈ mu3) : ζ ≠ 0 := by
  obtain ⟨a, rfl⟩ := (mem_mu3_iff ζ).mp h
  intro h0
  have := chargePhase_mul_neg a
  rw [h0, zero_mul] at this
  exact zero_ne_one this

theorem mu3_star {ζ : ℂ} (h : ζ ∈ mu3) : star ζ ∈ mu3 := by
  obtain ⟨a, rfl⟩ := (mem_mu3_iff ζ).mp h
  rw [← chargePhase_neg]
  exact chargePhase_mem_mu3 _

theorem mu3_star_mul {ζ : ℂ} (h : ζ ∈ mu3) : star ζ * ζ = 1 := by
  obtain ⟨a, rfl⟩ := (mem_mu3_iff ζ).mp h
  rw [mul_comm]
  exact chargePhase_mul_star a

theorem mu3_mul {ζ ξ : ℂ} (h : ζ ∈ mu3) (h' : ξ ∈ mu3) : ζ * ξ ∈ mu3 := by
  obtain ⟨a, rfl⟩ := (mem_mu3_iff ζ).mp h
  obtain ⟨b, rfl⟩ := (mem_mu3_iff ξ).mp h'
  rw [← chargePhase_add]
  exact chargePhase_mem_mu3 _

theorem sign_pm {s t : ZMod 3} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) {a b : WeylLabel}
    (h : s • a = t • b ∨ s • a = -(t • b)) : a = b ∨ a = -b := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp only [one_smul, neg_one_smul, neg_neg] at h <;> rcases h with h | h <;>
    first
    | exact Or.inl h
    | exact Or.inr h
    | exact Or.inl (neg_injective h)
    | exact Or.inr (by rw [← h, neg_neg])
    | exact Or.inr (neg_injective (by rw [h, neg_neg]))

end Contrast

/-- Qutrit contrast table, with the four-plane theorem (iii) (frame form) as the one Section 3 hypothesis. -/
theorem qutritContrastTable (h3 : FrameProperties.QutritFourFrames) : Statements.QutritContrastTable := by
  classical
  intro Q h1 hQ hiso F hF hmem hunb
  obtain ⟨E, hE⟩ := hiso
  obtain ⟨hunit, htr⟩ := iso_unit_trace Q h1 E hE
  -- The four frames in the matrix model.
  set G : Fin 4 → Fin 3 → FullHermitian3 := fun i a => E.symm ⟨F i a, hmem i a⟩ with hG
  have hEG : ∀ i a, (E (G i a)).val = F i a := by intro i a; simp [hG]
  have hGframe : ∀ i, HermFrame (G i) := fun i =>
    { trace_one := fun a => by rw [← htr, hEG]; exact (hF i).trace_one a
      idempotent := fun a => E.injective (Subtype.ext (by rw [hE, hEG, (hF i).idempotent]))
      orthogonal := fun a b hab => E.injective (Subtype.ext (by
        rw [hE, hEG, hEG, (hF i).orthogonal a b hab, map_zero]; rfl))
      sum_unit := E.injective (Subtype.ext (by
        rw [map_add, map_add, Submodule.coe_add, Submodule.coe_add, hEG, hEG, hEG,
          (hF i).sum_unit, hunit])) }
  have hGunb : ∀ i j, i ≠ j → HermUnbiased (G i) (G j) := fun i j hij a b => by
    rw [← htr, hE, hEG, hEG]; exact hunb i j hij a b
  obtain ⟨U, hUmem, π, σ, hUG⟩ := h3 G hGframe hGunb
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hUmem
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hUmem
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective Q.subtype (Submodule.ker_subtype Q)
  have hg' : ∀ q : Q, g q = q := fun q => LinearMap.congr_fun hg q
  -- Images of the contrasts.
  have hcon : ∀ i, ∃ (ζ : ℂ) (s : ZMod 3), ζ ∈ mu3 ∧ (s = 1 ∨ s = -1) ∧
      transC E U g (contrast (F i)) = ζ • weylMatrix (s • weylLinePoint (π i)) := by
    intro i
    have h0 : transC E U g (contrast (F i)) = ∑ a : Fin 3, chargePhase (outcome a) •
        weylEigenMatrix (weylLinePoint (π i)) (outcome (σ i a)) := by
      simp only [contrast, transC_sum, transC_smul, transC_ofReal]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [transR_mem E U g hg' (hmem i a)]
      exact congrArg _ (congrArg zIdx (hUG i a))
    obtain ⟨b, s, hs, hperm⟩ :=
      fourier_perm (fun c => weylEigenMatrix (weylLinePoint (π i)) (outcome c)) (σ i)
    refine ⟨chargePhase b, s, chargePhase_mem_mu3 b, hs, ?_⟩
    rw [h0, hperm]
    rcases hs with rfl | rfl
    · simp only [one_mul, one_smul]
      rw [weyl_contrast_one]
    · rw [weyl_contrast_neg, neg_one_smul]
  choose ζ s hζ hs hΦ using hcon
  set lab : Fin 4 → WeylLabel := fun i => s i • weylLinePoint (π i) with hlab
  have lab_ne : ∀ i, lab i ≠ 0 := by
    intro i h
    rcases hs i with h' | h' <;> simp only [hlab, h', one_smul, neg_one_smul, neg_eq_zero] at h <;>
      exact line_ne_zero _ h
  have lab_inj : ∀ i j, (lab i = lab j ∨ lab i = -lab j) → i = j := fun i j h =>
    π.injective (line_unique _ _ (sign_pm (hs i) (hs j) h))
  have lab_cover : ∀ v : WeylLabel, v ≠ 0 → ∃ i, v = lab i ∨ v = -lab i := by
    intro v hv
    obtain ⟨k, hk⟩ := line_cover v hv
    refine ⟨π.symm k, ?_⟩
    have hl : lab (π.symm k) = s (π.symm k) • weylLinePoint k := by
      simp only [hlab, Equiv.apply_symm_apply]
    rw [hl]
    rcases hs (π.symm k) with h' | h' <;> rw [h'] <;> simp only [one_smul, neg_one_smul, neg_neg]
    · exact hk
    · exact hk.symm
  -- The labelling.
  set u : WeylLabel → AlbertC := fun v =>
    if v = 0 then ofReal 1 else
      if h : ∃ i, lab i = v then contrast (F h.choose) else
        if h' : ∃ i, -lab i = v then conj (contrast (F h'.choose)) else 0 with hu
  have u_zero : u 0 = ofReal 1 := by simp [hu]
  have u_lab : ∀ i, u (lab i) = contrast (F i) := by
    intro i
    have hex : ∃ j, lab j = lab i := ⟨i, rfl⟩
    have hc : hex.choose = i := lab_inj _ _ (Or.inl hex.choose_spec)
    simp only [hu, if_neg (lab_ne i), dif_pos hex, hc]
  have u_neg_lab : ∀ i, u (-lab i) = conj (contrast (F i)) := by
    intro i
    have hne : -lab i ≠ 0 := neg_ne_zero.mpr (lab_ne i)
    have hnex : ¬ ∃ j, lab j = -lab i := by
      rintro ⟨j, hj⟩
      have hji : j = i := lab_inj _ _ (Or.inr hj)
      subst hji
      exact lab_ne j (label_eq_neg_self _ hj)
    have hex : ∃ j, -lab j = -lab i := ⟨i, rfl⟩
    have hc : hex.choose = i := lab_inj _ _ (Or.inl (neg_injective hex.choose_spec))
    simp only [hu, if_neg hne, dif_neg hnex, dif_pos hex, hc]
  have u_cases : ∀ v, v = 0 ∨ ∃ i, v = lab i ∨ v = -lab i := by
    intro v
    by_cases hv : v = 0
    · exact Or.inl hv
    · exact Or.inr (lab_cover v hv)
  have u_neg : ∀ v, u (-v) = conj (u v) := by
    intro v
    rcases u_cases v with rfl | ⟨i, rfl | rfl⟩
    · rw [neg_zero, u_zero, conj_ofReal]
    · rw [u_neg_lab, u_lab]
    · rw [neg_neg, u_lab, u_neg_lab, conj_conj]
  have u_inQ : ∀ v, InQ Q (u v) := by
    intro v
    rcases u_cases v with rfl | ⟨i, rfl | rfl⟩
    · rw [u_zero]; exact InQ.ofReal h1
    · rw [u_lab]; exact InQ.of_contrast (hmem i)
    · rw [u_neg_lab]; exact (InQ.of_contrast (hmem i)).conj
  have hone : transC E U g (ofReal 1) = weylMatrix 0 := by
    have hsymm : E.symm ⟨1, h1⟩ = ⟨1, Matrix.isHermitian_one⟩ := by
      apply E.injective; apply Subtype.ext
      rw [LinearEquiv.apply_symm_apply, hunit]
    rw [transC_ofReal, transR_mem E U g hg' h1, hsymm, weylMatrix_zero]
    change zIdx (U * 1 * star U) = 1
    rw [Matrix.mul_one, hU', zIdx_one]
  have u_img : ∀ v, ∃ ξ ∈ mu3, transC E U g (u v) = ξ • weylMatrix v := by
    intro v
    rcases u_cases v with rfl | ⟨i, rfl | rfl⟩
    · exact ⟨1, Or.inl rfl, by rw [u_zero, hone, one_smul]⟩
    · exact ⟨ζ i, hζ i, by rw [u_lab, hΦ]⟩
    · refine ⟨star (ζ i), mu3_star (hζ i), ?_⟩
      rw [u_neg_lab, transC_conj E U g hg' (InQ.of_contrast (hmem i)), hΦ,
        Matrix.conjTranspose_smul, weylMatrix_adjoint]
  have u_sq : ∀ v, v ≠ 0 →
      jordan (u v) (u v) = conj (u v) ∧ jordan (u v) (conj (u v)) = ofReal 1 := by
    intro v hv
    rcases u_cases v with h | ⟨i, rfl | rfl⟩
    · exact absurd h hv
    · rw [u_lab]; exact ⟨contrast_sq (hF i), contrast_mul_conj (hF i)⟩
    · rw [u_neg_lab]
      exact ⟨by rw [← conj_jordan, contrast_sq (hF i)],
        by rw [conj_conj, jordan_comm, contrast_mul_conj (hF i)]⟩
  refine ⟨u, lab, u_zero, u_neg, fun i => ⟨lab_ne i, u_lab i⟩, lab_cover, ?_⟩
  intro v w
  by_cases hd : Dependent v w
  · refine ⟨1, one_ne_zero, ?_, fun _ => rfl, fun h => absurd hd h⟩
    rw [one_smul]
    rcases dependent_cases v w hd with rfl | rfl | rfl | rfl
    · rw [u_zero, jordan_one_left, zero_add]
    · rw [u_zero, jordan_one_right, add_zero]
    · by_cases hv : w = 0
      · subst hv; rw [add_zero, u_zero, jordan_one_left]
      · rw [(u_sq w hv).1, label_add_self, u_neg]
    · by_cases hv : v = 0
      · subst hv; rw [neg_zero, add_zero, u_zero, jordan_one_left]
      · rw [u_neg, (u_sq v hv).2, add_neg_cancel, u_zero]
  · have hb : symplecticBracket v w ≠ 0 := fun h => hd ((dependent_iff v w).mpr h)
    obtain ⟨ζv, hζv, hv'⟩ := u_img v
    obtain ⟨ζw, hζw, hw'⟩ := u_img w
    obtain ⟨ζs, hζs, hs'⟩ := u_img (v + w)
    have hmem3 : ζv * ζw * star ζs ∈ mu3 := mu3_mul (mu3_mul hζv hζw) (mu3_star hζs)
    refine ⟨-(1 / 2) * (ζv * ζw * star ζs),
      mul_ne_zero (by norm_num) (mu3_ne_zero hmem3), ?_, fun h => absurd h hd,
      fun _ => ⟨ζv * ζw * star ζs, hmem3, rfl⟩⟩
    have hin : InQ Q (jordan (u v) (u w) - (-(1 / 2) * (ζv * ζw * star ζs)) • u (v + w)) :=
      (InQ.jordan hQ (u_inQ v) (u_inQ w)).sub ((u_inQ _).smul _)
    have h0 : transC E U g (jordan (u v) (u w) - (-(1 / 2) * (ζv * ζw * star ζs)) • u (v + w)) = 0 := by
      rw [transC_sub, transC_jordan E U g hg' hU hE hQ (u_inQ v) (u_inQ w), transC_smul, hv', hw',
        hs', symZ_smul, weyl_sym, if_neg hb, smul_smul, smul_smul, ← sub_smul]
      have hst := mu3_star_mul hζs
      have hz : ζv * ζw * -(1 / 2 : ℂ) - -(1 / 2) * (ζv * ζw * star ζs) * ζs = 0 := by
        linear_combination ((1 / 2 : ℂ) * ζv * ζw) * hst
      rw [hz, zero_smul]
    exact sub_eq_zero.mp (transC_injective E U g hg' hU hin h0)

end

end ThirteenPlanes.AlbertGrading
