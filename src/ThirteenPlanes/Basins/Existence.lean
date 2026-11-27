module

public import ThirteenPlanes.Basins.Bounds
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

/-! Global forward existence and uniqueness for the homogeneous one-loop flow.

Mathlib provides local Picard–Lindelöf and Grönwall uniqueness, but no continuation theorem.
We truncate the field outside a box that contains the a priori region `R ≤ C + 1`, solve the
globally Lipschitz truncated problem on every `[0, n]`, glue by uniqueness, and use the a priori
bound to show that the glued solution never leaves the box, where the two fields agree. -/

open Set Filter Topology Metric
open scoped NNReal

namespace ThirteenPlanes

noncomputable section

/-- Clamp a real number to `[-ρ, ρ]`. -/
def clampAbs (ρ a : ℝ) : ℝ := max (-ρ) (min ρ a)

theorem abs_clampAbs_le {ρ : ℝ} (hρ : 0 ≤ ρ) (a : ℝ) : |clampAbs ρ a| ≤ ρ := by
  unfold clampAbs
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clampAbs_of_abs_le {ρ a : ℝ} (h : |a| ≤ ρ) : clampAbs ρ a = a := by
  unfold clampAbs
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

theorem dist_clampAbs_le (ρ a b : ℝ) : dist (clampAbs ρ a) (clampAbs ρ b) ≤ dist a b := by
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  unfold clampAbs
  simp only [Real.dist_eq]
  rw [abs_le]
  constructor <;> simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- Clamp both coordinates to `[-ρ, ρ]`. -/
def clampBox (ρ : ℝ) (u : ℝ × ℝ) : ℝ × ℝ := (clampAbs ρ u.1, clampAbs ρ u.2)

theorem dist_clampBox_le (ρ : ℝ) (u v : ℝ × ℝ) : dist (clampBox ρ u) (clampBox ρ v) ≤ dist u v := by
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_le_max (dist_clampAbs_le ρ _ _) (dist_clampAbs_le ρ _ _)

theorem clampBox_mem {ρ : ℝ} (hρ : 0 ≤ ρ) (u : ℝ × ℝ) : clampBox ρ u ∈ closedBall (0 : ℝ × ℝ) ρ := by
  rw [mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le (abs_clampAbs_le hρ _) (abs_clampAbs_le hρ _)

theorem clampBox_of_mem {ρ : ℝ} {u : ℝ × ℝ} (h : u ∈ closedBall (0 : ℝ × ℝ) ρ) :
    clampBox ρ u = u := by
  rw [mem_closedBall, dist_zero_right, Prod.norm_def] at h
  exact Prod.ext (clampAbs_of_abs_le (le_trans (le_max_left _ _) h))
    (clampAbs_of_abs_le (le_trans (le_max_right _ _) h))

theorem hasDerivWithinAt_Ici_of_Icc {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {T t : ℝ}
    (h : HasDerivWithinAt f f' (Icc 0 T) t) (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt f f' (Ici t) t :=
  h.mono_of_mem_nhdsWithin (mem_of_superset (inter_mem_nhdsWithin (Ici t) (Iic_mem_nhds htT))
    fun _ hr ↦ ⟨le_trans ht hr.1, hr.2⟩)

/-- A globally Lipschitz, bounded autonomous field has a forward solution on `[0, ∞)` from every
initial point. -/
theorem exists_forward_of_lipschitz {g : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0} {L : ℝ}
    (hg : LipschitzWith K g) (hL : ∀ u, ‖g u‖ ≤ L) (x₀ : ℝ × ℝ) :
    ∃ y : ℝ → ℝ × ℝ, y 0 = x₀ ∧ ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt y (g (y t)) (Ici 0) t := by
  set L' : ℝ≥0 := Real.toNNReal L
  have hPL : ∀ n : ℕ, IsPicardLindelof (fun _ ↦ g)
      (⟨0, ⟨le_rfl, Nat.cast_nonneg n⟩⟩ : Icc (0 : ℝ) n) x₀ (L' * n) 0 L' K := fun n ↦
    IsPicardLindelof.of_time_independent
      (fun u _ ↦ le_trans (hL u) (Real.le_coe_toNNReal L)) (hg.lipschitzOnWith)
      (by simp)
  choose α hα0 hα using fun n : ℕ ↦ IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    (hPL n)
  have hcont : ∀ n : ℕ, ContinuousOn (α n) (Icc 0 n) := fun n t ht ↦
    (hα n t ht).continuousWithinAt
  have hcons : ∀ n m : ℕ, n ≤ m → EqOn (α n) (α m) (Icc 0 n) := by
    intro n m hnm
    have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
    apply ODE_solution_unique (v := fun _ ↦ g) (K := K) (fun _ ↦ hg) (hcont n)
      (fun t ht ↦ hasDerivWithinAt_Ici_of_Icc (hα n t (Ico_subset_Icc_self ht)) ht.1 ht.2)
      ((hcont m).mono (Icc_subset_Icc_right hnm'))
      (fun t ht ↦ hasDerivWithinAt_Ici_of_Icc (hα m t ⟨ht.1, le_trans ht.2.le hnm'⟩) ht.1
        (lt_of_lt_of_le ht.2 hnm'))
    exact (hα0 n).trans (hα0 m).symm
  set y : ℝ → ℝ × ℝ := fun t ↦ α (⌈t⌉₊ + 1) t
  have hy : ∀ (m : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) m → y t = α m t := by
    intro m t ht
    have hk : t ∈ Icc (0 : ℝ) ((⌈t⌉₊ + 1 : ℕ) : ℝ) := ⟨ht.1, by
      push_cast; linarith [Nat.le_ceil t]⟩
    rcases le_total (⌈t⌉₊ + 1) m with h | h
    · exact hcons _ _ h hk
    · exact (hcons _ _ h ht).symm
  refine ⟨y, ?_, fun t ht ↦ ?_⟩
  · rw [hy 1 0 ⟨le_rfl, by norm_num⟩]
    exact hα0 1
  · set m := ⌈t⌉₊ + 1
    have htm : t < m := by simp only [m]; push_cast; linarith [Nat.le_ceil t]
    have hmem : Icc (0 : ℝ) m ∈ 𝓝[Ici 0] t :=
      mem_of_superset (inter_mem_nhdsWithin (Ici 0) (Iic_mem_nhds htm)) fun _ hr ↦ ⟨hr.1, hr.2⟩
    have h1 := (hα m t ⟨ht, htm.le⟩).mono_of_mem_nhdsWithin hmem
    rw [← hy m t ⟨ht, htm.le⟩] at h1
    exact h1.congr_of_eventuallyEq (mem_of_superset hmem fun r hr ↦ hy m r hr)
      (hy m t ⟨ht, htm.le⟩)

/-- The box radius used for a priori bound `C`. -/
def boxRadius (lam C : ℝ) : ℝ := 1 + (C + 1) + (C + 1) / (3 * lam)

theorem mem_box_of_weightedStrength_le {lam C : ℝ} (hlam : 0 < lam) (hC : 0 ≤ C) {u : ℝ × ℝ}
    (h : weightedStrength lam u.1 u.2 ≤ C + 1) : u ∈ closedBall (0 : ℝ × ℝ) (boxRadius lam C) := by
  have h3 : 0 < 3 * lam := by positivity
  have hq : 0 ≤ (C + 1) / (3 * lam) := by positivity
  set ρ := boxRadius lam C
  have hρ1 : 1 ≤ ρ := by simp only [ρ, boxRadius]; linarith
  have hρsq : ρ ≤ ρ ^ 2 := by nlinarith
  unfold weightedStrength at h
  have ha : u.1 ^ 2 ≤ ρ ^ 2 := by
    have : u.1 ^ 2 ≤ C + 1 := by nlinarith [sq_nonneg u.2]
    have : C + 1 ≤ ρ := by simp only [ρ, boxRadius]; linarith
    linarith
  have hb : u.2 ^ 2 ≤ ρ ^ 2 := by
    have : u.2 ^ 2 ≤ (C + 1) / (3 * lam) := by
      rw [le_div_iff₀ h3]; nlinarith [sq_nonneg u.1]
    have : (C + 1) / (3 * lam) ≤ ρ := by simp only [ρ, boxRadius]; linarith
    linarith
  rw [mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hρ0 : 0 ≤ ρ := by linarith
  exact max_le (by simpa [abs_of_nonneg hρ0] using sq_le_sq.mp ha)
    (by simpa [abs_of_nonneg hρ0] using sq_le_sq.mp hb)

/-- For positive `lam` and any `ε`, every initial coupling has a forward solution on `[0, ∞)`. -/
theorem exists_forward_solution {lam : ℝ} (hlam : 0 < lam) (ε : ℝ) (x₀ : ℝ × ℝ) :
    ∃ x : ℝ → ℝ × ℝ, x 0 = x₀ ∧ IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0) := by
  set C := max (weightedStrength lam x₀.1 x₀.2) (6 * flowScale * ε)
  have hC : 0 ≤ C := le_trans (weightedStrength_nonneg hlam.le _ _) (le_max_left _ _)
  set ρ := boxRadius lam C
  have hρ : 0 ≤ ρ := by
    simp only [ρ, boxRadius]; have : 0 ≤ (C + 1) / (3 * lam) := by positivity
    linarith
  obtain ⟨K, hK⟩ := ((familyField_locallyLipschitz lam ε).locallyLipschitzOn
    (s := closedBall (0 : ℝ × ℝ) ρ)).exists_lipschitzOnWith_of_compact (isCompact_closedBall 0 ρ)
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℝ × ℝ) ρ).exists_bound_of_continuousOn
    (familyField_contDiff lam ε).continuous.continuousOn
  set g : ℝ × ℝ → ℝ × ℝ := fun u ↦ familyField lam ε (clampBox ρ u)
  have hg : LipschitzWith K g := LipschitzWith.of_dist_le_mul fun u v ↦
    (hK.dist_le_mul _ (clampBox_mem hρ u) _ (clampBox_mem hρ v)).trans
      (mul_le_mul_of_nonneg_left (dist_clampBox_le ρ u v) K.2)
  obtain ⟨y, hy0, hy⟩ := exists_forward_of_lipschitz hg (fun u ↦ hL _ (clampBox_mem hρ u)) x₀
  have hR : ∀ t, 0 ≤ t → weightedStrength lam (y t).1 (y t).2 ≤ C := by
    apply le_of_deriv_neg_above one_pos (y' := fun s ↦
      2 * (y s).1 * (g (y s)).1 + 3 * lam * (2 * (y s).2 * (g (y s)).2))
    · intro s hs
      have h1 : HasDerivWithinAt (fun r ↦ (y r).1) (g (y s)).1 (Ici 0) s := (hy s hs).fst
      have h2 : HasDerivWithinAt (fun r ↦ (y r).2) (g (y s)).2 (Ici 0) s := (hy s hs).snd
      have h := (h1.pow 2).add ((h2.pow 2).const_mul (3 * lam))
      convert h using 1
      · funext r; simp [weightedStrength]
      · simp only [Nat.cast_ofNat]; ring
    · rw [hy0]; exact le_max_left _ _
    · intro s _ hCs hC1
      have hbox := mem_box_of_weightedStrength_le hlam hC hC1
      have hgf : g (y s) = familyField lam ε ((y s).1, (y s).2) := by
        simp only [g]
        rw [show clampBox ρ (y s) = y s from clampBox_of_mem hbox]
      rw [hgf]
      set R := weightedStrength lam (y s).1 (y s).2
      have hid := familyField_weightedStrength lam ε (y s).1 (y s).2
      have h1 : 6 * flowScale * ε < R := lt_of_le_of_lt (le_max_right _ _) hCs
      have h2 : 0 < R := lt_of_le_of_lt hC hCs
      have hD := weightedStrength_sq_div_six_le_radialDamping hlam.le (y s).1 (y s).2
      have hK0 := flowScale_pos
      have : flowScale * (2 * (y s).1 * (familyField lam ε ((y s).1, (y s).2)).1 +
          3 * lam * (2 * (y s).2 * (familyField lam ε ((y s).1, (y s).2)).2)) < 0 := by
        rw [show 2 * (y s).1 * (familyField lam ε ((y s).1, (y s).2)).1 +
          3 * lam * (2 * (y s).2 * (familyField lam ε ((y s).1, (y s).2)).2) =
          2 * (y s).1 * (familyField lam ε ((y s).1, (y s).2)).1 +
          6 * lam * (y s).2 * (familyField lam ε ((y s).1, (y s).2)).2 by ring, hid]
        nlinarith [mul_pos h2 (sub_pos.mpr h1)]
      exact neg_of_mul_neg_right this hK0.le
  refine ⟨y, hy0, fun t ht ↦ ?_⟩
  have hbox := mem_box_of_weightedStrength_le hlam hC (by linarith [hR t ht])
  have := hy t ht
  simp only [g] at this
  rw [show clampBox ρ (y t) = y t from clampBox_of_mem hbox] at this
  exact this

/-- Forward solutions are unique: two forward solutions with the same initial value agree on
`[0, ∞)`. -/
theorem forward_solution_unique {lam ε : ℝ} (hlam : 0 < lam) {x y : ℝ → ℝ × ℝ}
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hy : IsIntegralCurveOn y (fun _ ↦ familyField lam ε) (Ici 0)) (h0 : x 0 = y 0) :
    EqOn x y (Ici 0) := by
  set C := max (weightedStrength lam (x 0).1 (x 0).2) (6 * flowScale * ε)
  have hC : 0 ≤ C := le_trans (weightedStrength_nonneg hlam.le _ _) (le_max_left _ _)
  set ρ := boxRadius lam C
  obtain ⟨K, hK⟩ := ((familyField_locallyLipschitz lam ε).locallyLipschitzOn
    (s := closedBall (0 : ℝ × ℝ) ρ)).exists_lipschitzOnWith_of_compact (isCompact_closedBall 0 ρ)
  have hxb : ∀ t, 0 ≤ t → x t ∈ closedBall (0 : ℝ × ℝ) ρ := fun t ht ↦
    mem_box_of_weightedStrength_le hlam hC
      (by linarith [weightedStrength_le_of_solution hlam.le hx t ht])
  have hyb : ∀ t, 0 ≤ t → y t ∈ closedBall (0 : ℝ × ℝ) ρ := fun t ht ↦
    mem_box_of_weightedStrength_le hlam hC (by
      have := weightedStrength_le_of_solution hlam.le hy t ht
      rw [← h0] at this; linarith)
  intro t ht
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ ↦ familyField lam ε)
    (s := fun _ ↦ closedBall (0 : ℝ × ℝ) ρ) (fun _ _ ↦ hK)
    (hx.continuousOn.mono Icc_subset_Ici_self)
    (fun r hr ↦ (hx r hr.1).mono (Ici_subset_Ici.mpr hr.1)) (fun r hr ↦ hxb r hr.1)
    (hy.continuousOn.mono Icc_subset_Ici_self)
    (fun r hr ↦ (hy r hr.1).mono (Ici_subset_Ici.mpr hr.1)) (fun r hr ↦ hyb r hr.1) h0
    ⟨ht, le_rfl⟩

end

end ThirteenPlanes
