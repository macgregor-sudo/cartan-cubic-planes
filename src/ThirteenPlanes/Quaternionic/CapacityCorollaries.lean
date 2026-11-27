module

public import ThirteenPlanes.Quaternionic.ClosedFramePlanes
public import ThirteenPlanes.Quaternionic.GeometricFloor
public import ThirteenPlanes.Quaternionic.SixCompletion
public import ThirteenPlanes.Quaternionic.Cardinality
public import ThirteenPlanes.PlaneShares
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option backward.privateInPublic true

/-! The quaternionic obstruction and five-basis bound on the actual carriers. -/

open scoped BigOperators

namespace QuaternionicMUB

open ThirteenPlanes ThirteenPlanes.RoundCubics

noncomputable section

private theorem frame_eq_of_points {F G : Frame} (h : ∀ i, F.point i = G.point i) : F = G := by
  cases F
  cases G
  simp only [Frame.mk.injEq]
  exact funext h

private theorem orthogonal_planes_finrank {ι : Type*} [Fintype ι]
    (U : ι → Submodule ℝ TracelessHilbert) (dim : ∀ i, Module.finrank ℝ (U i) = 2)
    (ortho : Pairwise fun i j => (U i).IsOrtho (U j)) :
    Module.finrank ℝ (⨆ i, U i : Submodule ℝ TracelessHilbert) = Fintype.card ι * 2 := by
  classical
  have hf : OrthogonalFamily ℝ (fun i => U i) (fun i => (U i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise ortho
  rw [Submodule.iSup_eq_range_dfinsupp_lsum,
    LinearMap.finrank_range_of_inj hf.independent.dfinsupp_lsum_injective]
  change Module.finrank ℝ (DirectSum ι (fun i => ↥(U i))) = _
  rw [Module.finrank_directSum]
  simp [dim]

private theorem five_floors_gt_two : 2 < (5 : ℝ) * (1 - 1 / Real.sqrt 3) := by
  have hs : (5 / 3 : ℝ) < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hr : (5 : ℝ) / Real.sqrt 3 < 3 := (div_lt_iff₀ hspos).mpr (by linarith)
  linarith only [hr, show (5 : ℝ) * (1 / Real.sqrt 3) = 5 / Real.sqrt 3 by ring]

/-- Five third-plane shares of a hypothetical seven-frame family would sum to two,
contradicting the geometric lower bound on every actual triple. -/
theorem no_seven_native_frames (F : Fin 7 → Frame) : ¬ IsMUBFrameFamily F := by
  intro hF
  let U := fun i => (F i).centeredPlane
  have hdim (i : Fin 7) : Module.finrank ℝ (U i) = 2 := (F i).centeredPlane_dimension
  have horth : Pairwise fun i j => (U i).IsOrtho (U j) :=
    fun _ _ hij => Frame.centeredPlane_orthogonal (hF hij)
  have hexh : (⨆ i, U i) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [orthogonal_planes_finrank U hdim horth, finrank_TracelessHilbert, Fintype.card_fin]
  let P : PlaneDecomposition TracelessHilbert (Fin 7) := ⟨U, hdim, horth, hexh⟩
  have hc : IsClosedPlaneSystem quaternionTraceCubic P :=
    fun i => (F i).centeredPlane_closed
  let K := Finset.univ.filter (fun k : Fin 7 => k ≠ 0 ∧ k ≠ 1)
  have h01 : (0 : Fin 7) ≠ 1 := by decide
  have hsum : (∑ k ∈ K, planeShare quaternionTraceCubic P 0 1 k) = 2 :=
    planeShare_pair_sum quaternionTraceCubic_round hc h01
  choose B hB using fun i => frame_has_basis (F i)
  have hFrame (i : Fin 7) : (B i).toFrame = F i :=
    frame_eq_of_points (hB i)
  have hUB {i j : Fin 7} (hij : i ≠ j) : (B i).MutuallyUnbiased (B j) := by
    apply ((B i).mutuallyUnbiased_iff_toFrame (B j)).mpr
    rw [hFrame, hFrame]
    exact hF hij
  have hl (k : Fin 7) (hk : k ∈ K) :
      1 - 1 / Real.sqrt 3 ≤ planeShare quaternionTraceCubic P 0 1 k := by
    have hk' : k ≠ 0 ∧ k ≠ 1 := (Finset.mem_filter.mp hk).2
    have hb := quaternionicFloor.1 (B 0) (B 1) (B k)
      ⟨hUB h01, hUB hk'.1.symm, hUB hk'.2.symm⟩
    rw [planeShare_eq_shareOfThreePlanes]
    change _ ≤ shareOfThreePlanes quaternionTraceCubic
      (F 0).centeredPlane (F 1).centeredPlane (F k).centeredPlane
    simpa only [basisGeometricShare, hFrame] using hb
  have hle := Finset.sum_le_sum (fun k hk => hl k hk)
  have hcard : K.card = 5 := by decide
  rw [hsum, Finset.sum_const, hcard, nsmul_eq_mul] at hle
  exact (not_le_of_gt five_floors_gt_two) hle

/-- The native quaternionic basis version of no seven. -/
theorem no_seven_native_bases (B : Fin 7 → QBasis) : ¬ IsMUBFamily B := by
  intro hB
  apply no_seven_native_frames (fun i => (B i).toFrame)
  exact fun i j hij => ((B i).mutuallyUnbiased_iff_toFrame (B j)).mp (hB hij)

/-- Seven pairwise orthogonal native traceless two-planes cannot all be closed. -/
theorem no_seven_closedNativePlanes (U : Fin 7 → Submodule ℝ TracelessHilbert)
    (dim : ∀ i, Module.finrank ℝ (U i) = 2)
    (ortho : Pairwise fun i j => (U i).IsOrtho (U j)) :
    ¬ (∀ i, IsClosedPiece quaternionTraceCubic (U i)) := by
  intro hc
  choose F hF using fun i => closedPlane_has_frame (U i) (dim i) (hc i)
  apply no_seven_native_frames F
  intro i j hij
  apply ((F i).centeredPlane_orthogonal_iff (F j)).mp
  rw [← hF i, ← hF j]
  exact ortho hij

/-- The actual native traceless quaternionic cubic has no orthogonal decomposition into closed planes. -/
theorem no_nativeQuaternionicPlaneDecomposition {ι : Type*} [Fintype ι]
    (P : PlaneDecomposition TracelessHilbert ι) : ¬ IsClosedPlaneSystem quaternionTraceCubic P := by
  intro hc
  have h := orthogonal_planes_finrank P.plane P.dimension P.pairwise_orthogonal
  rw [P.exhaustive, finrank_top, finrank_TracelessHilbert] at h
  have ha : Fintype.card (Fin 7) ≤ Fintype.card ι := by rw [Fintype.card_fin]; omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le ha
  apply no_seven_closedNativePlanes (fun i => P.plane (e i)) (fun i => P.dimension (e i))
    (fun i j hij => P.pairwise_orthogonal (fun he => hij (e.injective he)))
  exact fun i => hc (e i)

/-- All native domains of the obstruction to seven quaternionic bases. -/
theorem quaternionicNoSeven :
    (∀ F : Fin 7 → Frame, ¬ IsMUBFrameFamily F) ∧
    (∀ B : Fin 7 → QBasis, ¬ IsMUBFamily B) ∧
    (∀ U : Fin 7 → Submodule ℝ TracelessHilbert, (∀ i, Module.finrank ℝ (U i) = 2) →
      (Pairwise fun i j => (U i).IsOrtho (U j)) →
      ¬ (∀ i, IsClosedPiece quaternionTraceCubic (U i))) ∧
    (∀ {ι : Type*} [Fintype ι] (P : PlaneDecomposition TracelessHilbert ι),
      ¬ IsClosedPlaneSystem quaternionTraceCubic P) :=
  ⟨no_seven_native_frames, no_seven_native_bases, no_seven_closedNativePlanes,
    no_nativeQuaternionicPlaneDecomposition⟩

/-- Completion of six quaternionic frames, using the constructive complement-and-joint-eigenbasis proof. -/
theorem quaternionicSixFrameCompletion (F : Fin 6 → Frame) (hF : IsMUBFrameFamily F) :
    ∃ H : Frame, ∀ i, (F i).MutuallyUnbiased H := by
  obtain ⟨U, hU⟩ := six_frames_extend F hF
  exact ⟨U.toFrame, hU⟩

/-- Quaternionic five-basis bound on arbitrary sets of native quaternionic bases. -/
theorem quaternionicFiveBound (S : Set QBasis) (hS : S.Pairwise QBasis.MutuallyUnbiased) :
    S.Finite ∧ S.ncard ≤ 5 :=
  set_finite_card_le_five_of_no_six
    (no_six_of_extension_and_no_seven six_bases_extend no_seven_native_bases) S hS

end

end QuaternionicMUB
