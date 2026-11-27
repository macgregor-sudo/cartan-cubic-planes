module

public import ThirteenPlanes.AlbertGrading.Generation.Windows
public import ThirteenPlanes.Shares.NativeTraceFrames
public import ThirteenPlanes.PlaneShares
public import ThirteenPlanes.NativeFramesPlaneData

@[expose] public section

set_option backward.privateInPublic true

/-! At least seven third planes generate the full Albert algebra
with any fixed pair in a complete thirteen-plane system.

A proper algebra containing the three frames lies in a quaternionic window, since a line
subalgebra cannot contain two unbiased frames. The quaternionic lower bound gives a share
at least `1 - 1/√3 > 2/5`, including for complex subalgebras. The eleven nonnegative shares sum to two, so at most four of the
third planes give a proper algebra. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading

open AlbertSequential ThirteenPlanes.RoundCubics

theorem nativeEqualCubic_round : IsRound nativeEqualCubic (1 / 6) := by
  refine ⟨by norm_num, fun x => ?_⟩
  rw [nativeEqualCubic_squareLaw x]
  ring

theorem code_closedSystem (c : TightNativeCode) :
    IsClosedPlaneSystem nativeEqualCubic c.decomposition := by
  intro i x y hx hy
  change nativeCenteredJordan x y ∈ nativeFramePlane (c.point i)
  exact nativeFramePlane_closed (c.frame i) hx hy

/-- A proper subalgebra of the compact Albert algebra containing three pairwise unbiased frames lies in a
quaternionic window, so the quaternionic lower bound applies to their triple traces. -/
theorem floor_of_proper {p q r : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (hq : Glennie.Frame q) (hr : Glennie.Frame r)
    (hpq : ∀ a b, Glennie.inner (p a) (q b) = 1 / 3)
    (hpr : ∀ a b, Glennie.inner (p a) (r b) = 1 / 3)
    (hqr : ∀ a b, Glennie.inner (q a) (r b) = 1 / 3)
    (hgen : generated (Set.range p ∪ Set.range q ∪ Set.range r) ≠ ⊤) :
    1 - 1 / Real.sqrt 3 ≤ 6 * ∑ a, ∑ b, ∑ c,
      (Glennie.trace (Glennie.jordan (Glennie.jordan (p a) (q b)) (r c)) - 1 / 9) ^ 2 := by
  set X := Set.range p ∪ Set.range q ∪ Set.range r
  let B := generatedSubalgebra (coordEquiv.symm '' X)
  have hB : B.carrier ≠ ⊤ := by
    intro h
    apply hgen
    rw [generated_eq_map, map_coordEquiv_eq_top_iff]
    exact h
  have hlt : B.carrier < (H3Subalgebra .O).carrier := by
    rw [H3Subalgebra_O_eq_top]
    exact lt_top_iff_ne_top.mpr hB
  have mem (x : Glennie.Albert) (hx : x ∈ X) : coordEquiv.symm x ∈ B.carrier :=
    subset_generatedSubalgebra _ ⟨x, hx, rfl⟩
  have hpB (a : Fin 3) : coordEquiv.symm (p a) ∈ B.carrier := mem _ (Or.inl (Or.inl ⟨a, rfl⟩))
  have hqB (a : Fin 3) : coordEquiv.symm (q a) ∈ B.carrier := mem _ (Or.inl (Or.inr ⟨a, rfl⟩))
  have hrB (a : Fin 3) : coordEquiv.symm (r a) ∈ B.carrier := mem _ (Or.inr ⟨a, rfl⟩)
  rcases lem_five_sub .O B hlt with ⟨s, hs, _, hline⟩ | ⟨W, hW⟩
  · exact absurd hline (not_le_lineSubalgebra hp hq hpq B hpB hqB s hs)
  · have inRange (x : Glennie.Albert) (hx : coordEquiv.symm x ∈ B.carrier) :
        x ∈ LinearMap.range ((coordEquiv : Albert →ₗ[ℝ] Glennie.Albert) ∘ₗ W.embedding) := by
      have h : coordEquiv.symm x ∈ LinearMap.range W.embedding := by
        rw [W.range_eq]; exact hW hx
      obtain ⟨M, hM⟩ := h
      refine ⟨M, ?_⟩
      change coordEquiv (W.embedding M) = x
      rw [hM, LinearEquiv.apply_symm_apply]
    exact floor_of_qemb (window_qemb W) hp hq hr hpq hpr hqr
      (fun a => inRange _ (hpB a)) (fun a => inRange _ (hqB a)) (fun a => inRange _ (hrB a))

private theorem five_floors_gt_two : 2 < (5 : ℝ) * (1 - 1 / Real.sqrt 3) := by
  have hs : (5 / 3 : ℝ) < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hr : (5 : ℝ) / Real.sqrt 3 < 3 := (div_lt_iff₀ hspos).mpr (by linarith)
  linarith only [hr, show (5 : ℝ) * (1 / Real.sqrt 3) = 5 / Real.sqrt 3 by ring]

/-- The counting step: eleven nonnegative weights summing to two, each at least `1 - 1/√3` off a
predicate, leave at least seven indices satisfying it. -/
theorem seven_of_weights (s : Fin 13 → ℝ) {i j : Fin 13} (hij : i ≠ j)
    (hsum : (∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), s k) = 2)
    (hnn : ∀ k, k ≠ i → k ≠ j → 0 ≤ s k) (P : Fin 13 → Prop) [DecidablePred P]
    (hP : ∀ k, k ≠ i → k ≠ j → ¬ P k → 1 - 1 / Real.sqrt 3 ≤ s k) :
    7 ≤ (Finset.univ.filter fun k : Fin 13 => k ≠ i ∧ k ≠ j ∧ P k).card := by
  set T := Finset.univ.filter (fun k : Fin 13 => k ≠ i ∧ k ≠ j)
  have hT : T = (Finset.univ.erase i).erase j := by
    ext k
    simp [T, and_comm]
  have hTcard : T.card = 11 := by
    rw [hT, Finset.card_erase_of_mem (by simp [Ne.symm hij]), Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hgood : (Finset.univ.filter fun k : Fin 13 => k ≠ i ∧ k ≠ j ∧ P k) = T.filter P := by
    ext k
    simp [T, and_assoc]
  rw [hgood]
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) P
  rw [hTcard] at hsplit
  set Bad := T.filter (fun k => ¬ P k)
  have hbad_le : (Bad.card : ℝ) * (1 - 1 / Real.sqrt 3) ≤ 2 := by
    have h1 : (Bad.card : ℝ) * (1 - 1 / Real.sqrt 3) ≤ ∑ k ∈ Bad, s k := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hkT := (Finset.mem_filter.mp hk'.1).2
      exact hP k hkT.1 hkT.2 hk'.2
    have h2 : (∑ k ∈ Bad, s k) ≤ ∑ k ∈ T, s k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro k hk _
      have hkT := (Finset.mem_filter.mp hk).2
      exact hnn k hkT.1 hkT.2
    linarith
  have hbad : Bad.card ≤ 4 := by
    by_contra hcon
    have h5 : (5 : ℝ) ≤ Bad.card := by exact_mod_cast (show 5 ≤ Bad.card by omega)
    have hpos : 0 < 1 - 1 / Real.sqrt 3 := by linarith [five_floors_gt_two]
    nlinarith [five_floors_gt_two]
  omega

/-- Generation by triples of closed planes (iii). -/
theorem generationCount : Statements.GenerationCount := by
  intro c i j hij
  classical
  have rule := planeShare_sum_rule nativeEqualCubic_round (code_closedSystem c)
  apply seven_of_weights (fun k => planeShare nativeEqualCubic c.decomposition i j k) hij
    (rule.2.1 i j hij)
    (fun k hki hkj => (rule.1 i j k hij hki hkj).1.1)
  intro k hki hkj hk
  have hjk : j ≠ k := Ne.symm hkj
  have hik : i ≠ k := Ne.symm hki
  have hshare := native_shareOfThreePlanes_eq_frame_trace (c.frame i) (c.frame j) (c.frame k)
    (c.planes_orthogonal hij) (c.planes_orthogonal hik) (c.planes_orthogonal hjk)
  change 1 - 1 / Real.sqrt 3 ≤ shareOfThreePlanes nativeEqualCubic (nativeFramePlane (c.point i))
    (nativeFramePlane (c.point j)) (nativeFramePlane (c.point k))
  rw [hshare]
  exact floor_of_proper (c.frame i) (c.frame j) (c.frame k) (c.overlap hij) (c.overlap hik)
    (c.overlap hjk) hk

end ThirteenPlanes.AlbertGrading
