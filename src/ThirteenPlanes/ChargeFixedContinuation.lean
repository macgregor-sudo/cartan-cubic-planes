module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Tactic.Module

@[expose] public section

set_option backward.privateInPublic true

/-! Forward continuation by a bounded Lipschitz extension, for arbitrary real Banach spaces.
The interval gluing is the same argument as the two-dimensional `Basins.Existence` proof. -/

open Set Metric Filter
open scoped NNReal Topology

namespace ThirteenPlanes.ChargeFixed

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem hasDerivWithinAt_Ici_of_Icc {f : ℝ → V} {f' : V} {T t : ℝ}
    (h : HasDerivWithinAt f f' (Icc 0 T) t) (ht : 0 ≤ t) (htT : t < T) :
    HasDerivWithinAt f f' (Ici t) t :=
  h.mono_of_mem_nhdsWithin (mem_of_superset (inter_mem_nhdsWithin (Ici t) (Iic_mem_nhds htT))
    fun _ hr => ⟨le_trans ht hr.1,hr.2⟩)

/-- Every bounded Lipschitz autonomous vector field on a real Banach space has a global forward solution. -/
theorem exists_forward_bounded_lipschitz [CompleteSpace V] {g : V → V} {K : ℝ≥0} {L : ℝ}
    (hg : LipschitzWith K g) (hL : ∀ u, ‖g u‖ ≤ L) (x₀ : V) :
    ∃ y : ℝ → V, y 0 = x₀ ∧ ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt y (g (y t)) (Ici 0) t := by
  let L' : ℝ≥0 := Real.toNNReal L
  have hPL : ∀ n : ℕ, IsPicardLindelof (fun _ => g)
      (⟨0,⟨le_rfl,Nat.cast_nonneg n⟩⟩ : Icc (0 : ℝ) n) x₀ (L'*n) 0 L' K := fun n =>
    IsPicardLindelof.of_time_independent
      (fun u _ => (hL u).trans (Real.le_coe_toNNReal L)) (hg.lipschitzOnWith) (by simp)
  choose α hα0 hα using fun n : ℕ => IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ (hPL n)
  have hc : ∀ n : ℕ, ContinuousOn (α n) (Icc 0 n) := fun n t ht => (hα n t ht).continuousWithinAt
  have hcons : ∀ n m : ℕ, n ≤ m → EqOn (α n) (α m) (Icc 0 n) := by
    intro n m hnm
    have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
    apply ODE_solution_unique (v := fun _ => g) (K := K) (fun _ => hg) (hc n)
      (fun t ht => hasDerivWithinAt_Ici_of_Icc (hα n t (Ico_subset_Icc_self ht)) ht.1 ht.2)
      ((hc m).mono (Icc_subset_Icc_right hnm'))
      (fun t ht => hasDerivWithinAt_Ici_of_Icc (hα m t ⟨ht.1,ht.2.le.trans hnm'⟩) ht.1
        (ht.2.trans_le hnm'))
    exact (hα0 n).trans (hα0 m).symm
  let y : ℝ → V := fun t => α (⌈t⌉₊+1) t
  have hy (m : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) m) : y t = α m t := by
    have hk : t ∈ Icc (0 : ℝ) ((⌈t⌉₊+1 : ℕ) : ℝ) := ⟨ht.1,by push_cast; linarith [Nat.le_ceil t]⟩
    rcases le_total (⌈t⌉₊+1) m with h|h
    · exact hcons _ _ h hk
    · exact (hcons _ _ h ht).symm
  refine ⟨y,?_,?_⟩
  · rw [hy 1 0 ⟨le_rfl,by norm_num⟩]
    exact hα0 1
  · intro t ht
    let m := ⌈t⌉₊+1
    have htm : t < m := by simp only [m]; push_cast; linarith [Nat.le_ceil t]
    have hm : Icc (0 : ℝ) m ∈ 𝓝[Ici 0] t :=
      mem_of_superset (inter_mem_nhdsWithin (Ici 0) (Iic_mem_nhds htm)) fun _ hr => ⟨hr.1,hr.2⟩
    have h1 := (hα m t ⟨ht,htm.le⟩).mono_of_mem_nhdsWithin hm
    rw [← hy m t ⟨ht,htm.le⟩] at h1
    exact h1.congr_of_eventuallyEq (mem_of_superset hm fun s hs => hy m s hs) (hy m t ⟨ht,htm.le⟩)

/-- Radial retraction to the closed norm ball. -/
def radialClamp (r : ℝ) (x : V) : V := if ‖x‖ ≤ r then x else (r/‖x‖) • x

theorem radialClamp_fixed {r : ℝ} {x : V} (h : x ∈ closedBall (0 : V) r) : radialClamp r x = x := by
  rw [mem_closedBall,dist_zero_right] at h
  simp [radialClamp,h]

theorem radialClamp_mem {r : ℝ} (hr : 0 ≤ r) (x : V) : radialClamp r x ∈ closedBall (0 : V) r := by
  rw [mem_closedBall,dist_zero_right]
  by_cases hx : ‖x‖ ≤ r
  · simp [radialClamp,hx]
  · have hn : 0 < ‖x‖ := hr.trans_lt (lt_of_not_ge hx)
    rw [radialClamp,ite_eq_right hx,norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hr hn.le),
      div_mul_cancel₀ _ hn.ne']

private theorem radialClamp_distance_to_self {r : ℝ} (hr : 0 ≤ r) (x : V) (hx : r < ‖x‖) :
    ‖x-radialClamp r x‖ = ‖x‖-r := by
  have hn := hr.trans_lt hx
  have hcoef : r/‖x‖ ≤ 1 := (div_le_one hn).mpr hx.le
  rw [radialClamp,ite_eq_right (not_le.mpr hx),show x-(r/‖x‖) • x = (1-r/‖x‖) • x by module,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hcoef),sub_mul,one_mul,div_mul_cancel₀ _ hn.ne']

private theorem radialClamp_dist_ordered {r : ℝ} (hr : 0 ≤ r) {x y : V} (hxy : ‖x‖ ≤ ‖y‖) :
    ‖radialClamp r x-radialClamp r y‖ ≤ 2*‖x-y‖ := by
  have hg : ‖y‖-‖x‖ ≤ ‖x-y‖ := (norm_sub_norm_le y x).trans_eq (norm_sub_rev _ _)
  by_cases hy : ‖y‖ ≤ r
  · simp [radialClamp,hxy.trans hy,hy]
    linarith only [norm_nonneg (x-y)]
  by_cases hx : ‖x‖ ≤ r
  · rw [radialClamp,ite_eq_left hx]
    calc
      _ ≤ ‖x-y‖+‖y-radialClamp r y‖ := by
        rw [show x-radialClamp r y = (x-y)+(y-radialClamp r y) by abel]
        exact norm_add_le _ _
      _ = ‖x-y‖+(‖y‖-r) := by rw [radialClamp_distance_to_self hr y (lt_of_not_ge hy)]
      _ ≤ _ := by linarith only [hg,hx]
  have hnx : 0 < ‖x‖ := hr.trans_lt (lt_of_not_ge hx)
  have hny := hnx.trans_le hxy
  let a := r/‖x‖
  let b := r/‖y‖
  have hab : b ≤ a := div_le_div_of_nonneg_left hr hnx hxy
  have hb : 0 ≤ b := div_nonneg hr hny.le
  have hb₁ : b ≤ 1 := (div_le_one hny).mpr (lt_of_not_ge hy).le
  have he : (a-b)*‖x‖ = b*(‖y‖-‖x‖) := by
    dsimp [a,b]
    field_simp
  rw [radialClamp,radialClamp,ite_eq_right hx,ite_eq_right hy]
  change ‖a • x-b • y‖ ≤ _
  rw [show a • x-b • y = b • (x-y)+(a-b) • x by module]
  calc
    _ ≤ ‖b • (x-y)‖+‖(a-b) • x‖ := norm_add_le _ _
    _ = b*‖x-y‖+b*(‖y‖-‖x‖) := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hb,
        abs_of_nonneg (sub_nonneg.mpr hab),he]
    _ ≤ ‖x-y‖+‖x-y‖ := add_le_add
        (mul_le_of_le_one_left (norm_nonneg _) hb₁)
        ((mul_le_mul_of_nonneg_left hg hb).trans (mul_le_of_le_one_left (norm_nonneg _) hb₁))
    _ = _ := by ring

/-- Radial retraction of a normed space onto a ball is two-Lipschitz. -/
theorem radialClamp_lipschitz {r : ℝ} (hr : 0 ≤ r) : LipschitzWith 2 (radialClamp (V := V) r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  change ‖radialClamp r x-radialClamp r y‖ ≤ 2*‖x-y‖
  rcases le_total ‖x‖ ‖y‖ with h|h
  · exact radialClamp_dist_ordered hr h
  · rw [norm_sub_rev (radialClamp r x),norm_sub_rev x]
    exact radialClamp_dist_ordered hr h

/-- Extend a Lipschitz vector field from a closed ball to a bounded global field by retraction. -/
theorem exists_forward_of_lipschitz_on_ball [CompleteSpace V] {F : V → V} {r L : ℝ} {K : ℝ≥0}
    (hr : 0 ≤ r) (hF : LipschitzOnWith K F (closedBall 0 r)) (hL : ∀ p ∈ closedBall 0 r, ‖F p‖ ≤ L)
    (x₀ : V) : ∃ u : ℝ → V, u 0=x₀ ∧ ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt u (F (radialClamp r (u t))) (Ici 0) t := by
  let g := F ∘ radialClamp r
  have hg : LipschitzWith (K*2) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hcl := (radialClamp_lipschitz (V := V) hr).dist_le_mul x y
    change dist (F (radialClamp r x)) (F (radialClamp r y)) ≤ (K : ℝ)*2*dist x y
    change dist (radialClamp r x) (radialClamp r y) ≤ (2 : ℝ)*dist x y at hcl
    exact (hF.dist_le_mul _ (radialClamp_mem hr x) _ (radialClamp_mem hr y)).trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hcl K.2)
  exact exists_forward_bounded_lipschitz hg (fun u => hL _ (radialClamp_mem hr u)) x₀

end
end ThirteenPlanes.ChargeFixed
