module

public import ThirteenPlanes.Cartan.NativeConclusions
public import ThirteenPlanes.Cartan.AlbertDerivationRank
public import ThirteenPlanes.JordanFrames.Albert
public import ThirteenPlanes.ClosedBlocks.Transport

@[expose] public section

set_option backward.privateInPublic true

/-! The compact Albert Cartan-decomposition corollary under the quoted maximal-torus result. -/

namespace ThirteenPlanes.Cartan

open RoundCubics JordanFrames
open scoped BigOperators RealInnerProductSpace

noncomputable section

local notation "𝔣" => albertJordan.skewDerivations

/-- Pairwise commutation on the actual compact real Albert derivations. -/
def IsAlbertCommutative (T : Submodule ℝ 𝔣) : Prop :=
  ∀ X ∈ T, ∀ Y ∈ T, Commute X.val.val Y.val.val

/-- A compact Cartan is a maximal commutative subalgebra of the actual derivation algebra. -/
def IsAlbertCompactCartan (T : Submodule ℝ 𝔣) : Prop :=
  IsAlbertCommutative T ∧ ∀ S : Submodule ℝ 𝔣, T ≤ S → IsAlbertCommutative S → S = T

/-- The frame-type assertion on all maximal commutative subspaces of the compact Albert derivations. -/
def CompactF4ToriFrameType : Prop :=
  ∀ T : Submodule ℝ 𝔣, IsAlbertCompactCartan T →
    IsFrameType (T.map albertJordan.restrictDerivation) 4 (1 / 6)

/-- The operator-trace pairing of the actual 26-dimensional representation. -/
def albertTracelessOperatorTrace (X Y : 𝔣) : ℝ :=
  -LinearMap.trace ℝ albertJordan.traceFree
    ((albertJordan.restrictDerivation X).val * (albertJordan.restrictDerivation Y).val)

theorem albertTracelessOperatorTrace_eq_inner (X Y : 𝔣) :
    albertTracelessOperatorTrace X Y = ⟪X,Y⟫ := by
  change -LinearMap.trace ℝ albertJordan.traceFree _ = ⟪X.val,Y.val⟫
  rw [← albertJordan.restrictDerivation_inner X Y, skewOperator_inner]

/-- The zero-weight space is the common zero eigenspace on the literal native trace kernel. -/
def albertZeroWeightPlane (T : Submodule ℝ 𝔣) : Submodule ℝ NativeTraceless :=
  (albertJordan.fixedTraceless (T.map albertJordan.skewDerivations.subtype)).map albertTraceEquiv.toLinearMap

theorem mem_albertZeroWeightPlane (T : Submodule ℝ 𝔣) (x : NativeTraceless) :
    x ∈ albertZeroWeightPlane T ↔ ∀ A ∈ T, A.val.val x.val = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩ A hA
    have h := (albertJordan.mem_fixedTraceless y).mp hy
      ⟨A.val, Submodule.mem_map_of_mem hA⟩
    exact h
  · intro h
    let y := albertTraceEquiv.symm x
    have hy : albertTraceEquiv y = x := albertTraceEquiv.apply_symm_apply x
    refine ⟨y, (albertJordan.mem_fixedTraceless y).mpr ?_, hy⟩
    rintro ⟨_, A, hA, rfl⟩
    have he := congrArg Subtype.val hy
    rw [albertTraceEquiv_val] at he
    exact he.symm ▸ h A hA

theorem albertZeroWeightPlane_closed (T : Submodule ℝ 𝔣) :
    IsClosedPiece nativeEqualCubic (albertZeroWeightPlane T) := by
  intro x y hx hy
  rw [mem_albertZeroWeightPlane] at hx hy ⊢
  intro A hA
  have h : A.val.val (Glennie.jordan x.val y.val) =
      Glennie.jordan (A.val.val x.val) y.val + Glennie.jordan x.val (A.val.val y.val) := A.property _ _
  have hp : A.val.val (Glennie.jordan x.val y.val) = 0 := by
    simpa only [hx A hA, hy A hA, Glennie.jordan_zero_left, Glennie.jordan_zero_right, add_zero] using h
  have hunit : A.val.val (1 : Glennie.Albert) = 0 := albertJordan.derivation_unit_zero A.property
  change A.val.val (Glennie.traceless (Glennie.jordan x.val y.val)) = 0
  rw [Glennie.traceless, map_sub, map_smul, hp, hunit, smul_zero, sub_zero]

private theorem compactF4_dimension : Module.finrank ℝ 𝔣 = 52 :=
  albertDerivationEquiv.finrank_eq.trans AlbertSequential.finrank_albertDerivation

private theorem compactF4_cartan_rank (quoted : CompactF4ToriFrameType)
    (T : Submodule ℝ 𝔣) (hT : IsAlbertCompactCartan T) : Module.finrank ℝ T = 4 :=
  (T.equivMapOfInjective albertJordan.restrictDerivation albertJordan.restrictDerivation_injective).finrank_eq.trans
    (quoted T hT).2.1

set_option maxHeartbeats 900000 in
/-- Under the quoted compact-torus theorem, every operator-trace orthogonal Cartan decomposition
has thirteen actual closed zero-weight planes, filled by mutually unbiased native frames. -/
theorem compactF4_cartanDecomposition_fixedPlanes (quoted : CompactF4ToriFrameType)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Submodule ℝ 𝔣)
    (hCartan : ∀ i, IsAlbertCompactCartan (T i))
    (hOrth : Pairwise fun i j => ∀ X ∈ T i, ∀ Y ∈ T j, albertTracelessOperatorTrace X Y = 0)
    (hSum : DirectSum.IsInternal T) :
    Fintype.card ι = 13 ∧
      (∀ i, Module.finrank ℝ (albertZeroWeightPlane (T i)) = 2 ∧
        IsClosedPiece nativeEqualCubic (albertZeroWeightPlane (T i))) ∧
      OrthogonalSplit (fun i => albertZeroWeightPlane (T i)) ∧
      ∃ F : ι → Fin 3 → Glennie.Albert, (∀ i, Glennie.Frame (F i)) ∧
        (∀ i, albertZeroWeightPlane (T i) = nativeFramePlane (F i)) ∧
        (∀ i j, i ≠ j → ∀ a b, Glennie.inner (F i a) (F j b) = 1 / 3) := by
  have hdim i := compactF4_cartan_rank quoted (T i) (hCartan i)
  let : ∀ i : ι, Module.Free ℝ (T i) := fun i => Module.Free.of_divisionRing ℝ (T i)
  let : ∀ i : ι, Module.Finite ℝ (T i) := fun i =>
    Module.finite_of_finrank_pos (by rw [hdim i]; decide)
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap T) hSum
  have count := e.finrank_eq
  rw [Module.finrank_directSum, compactF4_dimension] at count
  simp only [hdim, Finset.sum_const, Finset.card_univ, smul_eq_mul] at count
  have hc : Fintype.card ι = 13 := by omega
  have ht : OrthogonalSplit (E := 𝔣) T := by
    refine ⟨?_, hSum⟩
    intro i j hij
    rw [Submodule.isOrtho_iff_inner_eq]
    intro X hX Y hY
    rw [← albertTracelessOperatorTrace_eq_inner, hOrth hij X hX Y hY]
  have hType (i : ι) := quoted (T i) (hCartan i)
  have cardEq : 2 * Fintype.card ι = Module.finrank ℝ albertJordan.traceFree := by
    rw [hc, albertTraceFree_finrank]
  obtain ⟨hSplit, _, _⟩ := albertJordan.operatorOD_fixedPlanes 𝔣 le_rfl T ht
    4 (1 / 6) (Module.finrank ℝ albertDerivationOperators / 26) (by norm_num)
    albertFullCasimir hType cardEq albertJordan_closedPlane_has_frame
  have hf (i : ι) : Module.finrank ℝ (albertZeroWeightPlane (T i)) = 2 := by
    rw [albertZeroWeightPlane, LinearEquiv.finrank_map_eq,
      albertJordan.fixedTraceless_eq_fixedSpace 𝔣 le_rfl]
    exact (hType i).2.2.1
  have hOrtho : Pairwise fun i j => (albertZeroWeightPlane (T i)).IsOrtho (albertZeroWeightPlane (T j)) :=
    fun i j hij => isOrtho_map_isometry albertTraceEquiv (hSplit.1 hij)
  have top : (⨆ i, albertZeroWeightPlane (T i)) = ⊤ := by
    simp only [albertZeroWeightPlane]
    rw [← Submodule.map_iSup, hSplit.2.submodule_iSup_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr albertTraceEquiv.surjective]
  have hClosed (i : ι) := albertZeroWeightPlane_closed (T i)
  choose F hF hPlane using fun i => nativeClosedPlane_has_frame _ (hf i) (hClosed i)
  refine ⟨hc, fun i => ⟨hf i, hClosed i⟩,
    ⟨hOrtho, (OrthogonalFamily.of_pairwise hOrtho).isInternal_iff.mpr (by rw [top, Submodule.top_orthogonal_eq_bot])⟩, F, hF, hPlane, ?_⟩
  intro i j hij
  exact (native_framePlane_orthogonal_iff (hF i) (hF j)).mp (by simpa only [hPlane] using hOrtho hij)

end

end ThirteenPlanes.Cartan
