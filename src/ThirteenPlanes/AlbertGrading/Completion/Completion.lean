module

public import ThirteenPlanes.AlbertGrading.Completion.FramePlanes
public import ThirteenPlanes.AlbertGrading.Completion.Squares
public import ThirteenPlanes.AlbertGrading.Completion.Pair
public import ThirteenPlanes.Graded.Frames

@[expose] public section

/-! Completion of twelve Albert frames: twelve pairwise unbiased frames of the Albert algebra extend to exactly one
thirteenth, and twelve pairwise orthogonal closed planes lie in exactly one thirteen-plane system.

The squares identity uses harmonicity of the native cubic and of each closed plane.
Diagonalization of one complementary element and the Peirce gap formula give a common frame
for the complementary pair. 

-/

namespace ThirteenPlanes.AlbertGrading

open ThirteenPlanes ThirteenPlanes.RoundCubics CompletionO Module
open scoped BigOperators RealInnerProductSpace

noncomputable section

theorem nativeEqualCubic_isRound : IsRound nativeEqualCubic (1 / 6) := by
  refine ⟨by norm_num, fun x => ?_⟩
  rw [nativeEqualCubic_squareLaw x]
  ring

/-- The native cubic is harmonic, from the graded thirteen-plane system. -/
theorem nativeEqualCubic_traceFree : nativeEqualCubic.TraceFree :=
  traceFree_of_isClosedPlaneSystem nativeEqualCubic_isRound Graded.closedPlanes

theorem framePlane_closed {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    IsClosedPiece nativeEqualCubic (nativeFramePlane p) := by
  intro x y hx hy
  exact nativeFramePlane_closed hp hx hy

theorem complement_finrank (P : Fin 12 → Submodule ℝ NativeTraceless)
    (hdim : ∀ i, finrank ℝ (P i) = 2) (orth : Pairwise fun i j => (P i).IsOrtho (P j)) :
    finrank ℝ (⨆ i, P i)ᗮ = 2 := by
  have h := finrank_complement_add P orth hdim
  rw [nativeTraceless_finrank, Fintype.card_fin] at h
  omega

/-- The complement of twelve pairwise orthogonal closed planes is the plane of an actual frame. -/
theorem complement_isFramePlane (P : Fin 12 → Submodule ℝ NativeTraceless)
    (hdim : ∀ i, finrank ℝ (P i) = 2) (closed : ∀ i, IsClosedPiece nativeEqualCubic (P i))
    (orth : Pairwise fun i j => (P i).IsOrtho (P j)) :
    ∃ q : Fin 3 → Glennie.Albert, Glennie.Frame q ∧ nativeFramePlane q = (⨆ i, P i)ᗮ := by
  have hW := complement_finrank P hdim orth
  let b : OrthonormalBasis (Fin 2) ℝ (⨆ i, P i)ᗮ :=
    (stdOrthonormalBasis ℝ (⨆ i, P i)ᗮ).reindex (finCongr hW)
  have hs := complement_square_sum nativeEqualCubic_isRound nativeEqualCubic_traceFree P hdim
    closed orth b
  let x : NativeTraceless := b 0
  let y : NativeTraceless := b 1
  have coe_inner (u v : (⨆ i, P i)ᗮ) :
      ⟪u, v⟫ = Glennie.inner ((u : NativeTraceless) : Glennie.Albert) (v : NativeTraceless) := by
    rw [Submodule.coe_inner, Submodule.coe_inner, Glennie.hilbert_inner_eq_native]
  have hxx : Glennie.inner (x : Glennie.Albert) x = 1 := by
    rw [← b.inner_eq_one 0, coe_inner]
  have hyy : Glennie.inner (y : Glennie.Albert) y = 1 := by
    rw [← b.inner_eq_one 1, coe_inner]
  have hxy : Glennie.inner (x : Glennie.Albert) y = 0 := by
    rw [← b.inner_eq_zero (show (0 : Fin 2) ≠ 1 by decide), coe_inner]
  have e (z : NativeTraceless) :
      ((nativeEqualCubic.L z z : NativeTraceless) : Glennie.Albert) =
        Glennie.traceless (Glennie.jordan (z : Glennie.Albert) z) := by
    show ((nativeEqualCubic.squareMap z : NativeTraceless) : Glennie.Albert) = _
    rw [nativeEqualCubic_square, nativeCenter_coe]
  have hsq : Glennie.jordan (x : Glennie.Albert) x + Glennie.jordan (y : Glennie.Albert) y =
      (2 / 3 : ℝ) • (1 : Glennie.Albert) := by
    have h := congrArg Subtype.val hs
    rw [Submodule.coe_add, Submodule.coe_zero, e, e] at h
    have tx : Glennie.trace (Glennie.jordan (x : Glennie.Albert) x) = 1 := hxx
    have ty : Glennie.trace (Glennie.jordan (y : Glennie.Albert) y) = 1 := hyy
    rw [Glennie.traceless, Glennie.traceless, tx, ty] at h
    rw [← sub_eq_zero, ← h]
    module
  obtain ⟨q, hq, l, m, hl, hm⟩ := pair_common_frame x y (nativeTraceless_trace x)
    (nativeTraceless_trace y) hxx hyy hxy hsq
  refine ⟨q, hq, ?_⟩
  have mem (v : NativeTraceless) (c : Fin 3 → ℝ) (hv : (v : Glennie.Albert) = ∑ a, c a • q a) :
      v ∈ nativeFramePlane q := by
    have hc : ∑ a, c a = 0 := by
      rw [← nativeFrameSynthesis_trace hq]
      change Glennie.trace (∑ a, c a • q a) = 0
      rw [← hv]
      exact nativeTraceless_trace v
    obtain ⟨u, hu⟩ := nativeFrameEntries_surjective_of_zero_sum c hc
    refine ⟨u, Subtype.ext ?_⟩
    rw [nativeFrameChart_coe hq, hu, hv]
    rfl
  have hle : (⨆ i, P i)ᗮ ≤ nativeFramePlane q := by
    intro w hw
    have hrep := congrArg (fun z : (⨆ i, P i)ᗮ => (z : NativeTraceless)) (b.sum_repr' ⟨w, hw⟩)
    simp only [Fin.sum_univ_two] at hrep
    rw [← hrep]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (mem x l hl))
      (Submodule.smul_mem _ _ (mem y m hm))
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hW, nativeFramePlane_dimension hq])).symm

/-- A two-plane orthogonal to all twelve planes is their complement. -/
theorem eq_complement_of_orthogonal (P : Fin 12 → Submodule ℝ NativeTraceless)
    (hdim : ∀ i, finrank ℝ (P i) = 2) (orth : Pairwise fun i j => (P i).IsOrtho (P j))
    (U : Submodule ℝ NativeTraceless) (hU : finrank ℝ U = 2) (hUo : ∀ i, (P i).IsOrtho U) :
    U = (⨆ i, P i)ᗮ := by
  have hle : U ≤ (⨆ i, P i)ᗮ :=
    Submodule.isOrtho_iff_le.mp (Submodule.isOrtho_iSup_left.mpr hUo).symm
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hU, complement_finrank P hdim orth])

/-- Completion of twelve Albert frames, first sentence. -/
theorem completionO_frames : Statements.CompletionOFrames := by
  intro F hF hunb
  let P : Fin 12 → Submodule ℝ NativeTraceless := fun i => nativeFramePlane (F i)
  have hdim (i : Fin 12) : finrank ℝ (P i) = 2 := nativeFramePlane_dimension (hF i)
  have closed (i : Fin 12) : IsClosedPiece nativeEqualCubic (P i) := framePlane_closed (hF i)
  have orth : Pairwise fun i j => (P i).IsOrtho (P j) := fun i j hij =>
    framePlanes_orthogonal (hF i) (hF j) (hunb hij)
  obtain ⟨q, hq, hplane⟩ := complement_isFramePlane P hdim closed orth
  refine ⟨q, hq, fun i => ?_, fun q' hq' hu' => ?_⟩
  · apply unbiased_of_framePlanes_orthogonal (hF i) hq
    rw [hplane]
    exact Submodule.isOrtho_iff_le.mpr (Submodule.le_orthogonal_orthogonal _ |>.trans
      (Submodule.orthogonal_le (Submodule.orthogonal_le (le_iSup P i))))
  · apply range_eq_of_framePlane_eq hq hq'
    rw [hplane]
    exact eq_complement_of_orthogonal P hdim orth _ (nativeFramePlane_dimension hq')
      (fun i => framePlanes_orthogonal (hF i) hq' (hu' i))

/-- Any thirteen-plane system containing the twelve planes is the twelve planes and their
complement. -/
theorem system_eq (P : Fin 12 → Submodule ℝ NativeTraceless)
    (hdim : ∀ i, finrank ℝ (P i) = 2) (orth : Pairwise fun i j => (P i).IsOrtho (P j))
    (S : Set (Submodule ℝ NativeTraceless)) (hS : IsThirteenPlaneSystem S)
    (hsub : Set.range P ⊆ S) : S = insert (⨆ i, P i)ᗮ (Set.range P) := by
  obtain ⟨Q, rfl, hQd, -, hQo⟩ := hS
  have hinj : Function.Injective Q := by
    intro k l hkl
    by_contra hne
    have h : (Q k).IsOrtho (Q l) := hQo hne
    rw [hkl, Submodule.isOrtho_self] at h
    have := hQd l
    rw [h, finrank_bot] at this
    norm_num at this
  have key (k : Fin 13) (hk : Q k ∉ Set.range P) : Q k = (⨆ i, P i)ᗮ := by
    apply eq_complement_of_orthogonal P hdim orth _ (hQd k)
    intro i
    obtain ⟨l, hl⟩ := hsub ⟨i, rfl⟩
    have hlk : l ≠ k := by
      rintro rfl
      exact hk ⟨i, hl.symm⟩
    rw [← hl]
    exact hQo hlk
  have hex : ∃ k, Q k ∉ Set.range P := by
    by_contra hcon
    push Not at hcon
    choose f hf using hcon
    have finj : Function.Injective f := by
      intro k l hkl
      apply hinj
      rw [← hf k, ← hf l, hkl]
    have := Fintype.card_le_of_injective f finj
    simp at this
  obtain ⟨k0, hk0⟩ := hex
  ext U
  constructor
  · rintro ⟨k, rfl⟩
    by_cases hk : Q k ∈ Set.range P
    · exact Or.inr hk
    · exact Or.inl (key k hk)
  · rintro (rfl | hU)
    · exact ⟨k0, key k0 hk0⟩
    · exact hsub hU

/-- Completion of twelve Albert frames, second sentence. -/
theorem completionO_planes : Statements.CompletionOPlanes := by
  intro P hdim closed orth
  obtain ⟨q, hq, hplane⟩ := complement_isFramePlane P hdim closed orth
  have hW := complement_finrank P hdim orth
  have hWc : IsClosedPiece nativeEqualCubic (⨆ i, P i)ᗮ := by
    rw [← hplane]; exact framePlane_closed hq
  have hWo (i : Fin 12) : (P i).IsOrtho (⨆ j, P j)ᗮ :=
    Submodule.isOrtho_iff_le.mpr (Submodule.le_orthogonal_orthogonal _ |>.trans
      (Submodule.orthogonal_le (Submodule.orthogonal_le (le_iSup P i))))
  let Q : Fin 13 → Submodule ℝ NativeTraceless :=
    Fin.lastCases (motive := fun _ => Submodule ℝ NativeTraceless) (⨆ i, P i)ᗮ P
  have hQl : Q (Fin.last 12) = (⨆ i, P i)ᗮ := Fin.lastCases_last ..
  have hQc (i : Fin 12) : Q i.castSucc = P i := Fin.lastCases_castSucc ..
  have hS : IsThirteenPlaneSystem (Set.range Q) := by
    refine ⟨Q, rfl, fun k => ?_, fun k => ?_, ?_⟩
    · induction k using Fin.lastCases with
      | last => rw [hQl]; exact hW
      | cast i => rw [hQc]; exact hdim i
    · induction k using Fin.lastCases with
      | last => rw [hQl]; exact hWc
      | cast i => rw [hQc]; exact closed i
    · intro k l hkl
      induction k using Fin.lastCases with
      | last =>
        induction l using Fin.lastCases with
        | last => exact (hkl rfl).elim
        | cast j => rw [hQl, hQc]; exact (hWo j).symm
      | cast i =>
        induction l using Fin.lastCases with
        | last => rw [hQl, hQc]; exact hWo i
        | cast j =>
          rw [hQc, hQc]
          exact orth fun hij => hkl (congrArg Fin.castSucc hij)
  have hsub : Set.range P ⊆ Set.range Q := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castSucc, hQc i⟩
  refine ⟨Set.range Q, ⟨hS, hsub⟩, fun S ⟨hS', hsub'⟩ => ?_⟩
  rw [system_eq P hdim orth S hS' hsub', system_eq P hdim orth _ hS hsub]

/-- Completion of twelve Albert frames. -/
theorem completionO : Statements.CompletionO := ⟨completionO_frames, completionO_planes⟩

/-- The complement of the twelve frame planes is the plane of the completing frame. 
-/
theorem completionO_complement (F : Fin 12 → Fin 3 → Glennie.Albert)
    (hF : ∀ i, Glennie.Frame (F i)) (hunb : Pairwise fun i j => NativeUnbiased (F i) (F j)) :
    ∃ q : Fin 3 → Glennie.Albert, Glennie.Frame q ∧
      nativeFramePlane q = (⨆ i, nativeFramePlane (F i))ᗮ :=
  complement_isFramePlane _ (fun i => nativeFramePlane_dimension (hF i))
    (fun i => framePlane_closed (hF i))
    (fun i j hij => framePlanes_orthogonal (hF i) (hF j) (hunb hij))

/-- The hypotheses are realized: twelve frames of the graded thirteen-frame code. -/
theorem completionO_hypotheses_realized :
    ∃ F : Fin 12 → Fin 3 → Glennie.Albert, (∀ i, Glennie.Frame (F i)) ∧
      Pairwise fun i j => NativeUnbiased (F i) (F j) :=
  ⟨fun i => Graded.nativeCode.point i.castSucc, fun _ => Graded.nativeCode.frame _,
    fun _ _ hij a b => Graded.nativeCode.overlap (Fin.castSucc_injective _ |>.ne hij) a b⟩

end

end ThirteenPlanes.AlbertGrading
