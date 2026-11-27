module

public import ThirteenPlanes.Cartan.Restriction
public import ThirteenPlanes.Cartan.FramePlanes

@[expose] public section

set_option backward.privateInPublic true

/-! The common-kernel frame planes and the frame-type Casimir splitting. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Commutativity in the literal represented operator algebra. -/
def IsCommutativeSpace (T : Submodule ℝ (SkewOperator V)) : Prop :=
  ∀ A B : T, Commute A.val.val B.val.val

/-- Frame type in the trace-normalized model of Definition 7.1. -/
def IsFrameType (T : Submodule ℝ (SkewOperator V)) (rank : ℕ) (κ : ℝ) : Prop :=
  IsCommutativeSpace T ∧ Module.finrank ℝ T = rank ∧
    Module.finrank ℝ (fixedSpace T) = 2 ∧
    operatorCasimir T = κ • (LinearMap.id - projection (fixedSpace T))

theorem projection_map_isometry (g : V ≃ₗᵢ[ℝ] V) (U : Submodule ℝ V) :
    projection (U.map g.toLinearMap) = g.toLinearEquiv.conj (projection U) := by
  ext x
  change (U.map g.toLinearMap).starProjection x = g (U.starProjection (g.symm x))
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.mem_map_of_mem (U.starProjection_apply_mem _)
  · rintro _ ⟨y, hy, rfl⟩
    change ⟪x - g (U.starProjection (g.symm x)), g y⟫ = 0
    rw [show x = g (g.symm x) from (g.apply_symm_apply x).symm, ← map_sub, g.inner_map_map,
      g.symm_apply_apply]
    exact (Submodule.mem_orthogonal' _ _).mp (U.sub_starProjection_mem_orthogonal _) y hy

/-- Frame type transports under orthogonal conjugation, along with the actual fixed plane. -/
theorem conjugate_frameType_fixed (g : V ≃ₗᵢ[ℝ] V) (T : Submodule ℝ (SkewOperator V))
    {rank : ℕ} {κ : ℝ} (h : IsFrameType T rank κ) :
    IsFrameType (T.map (conjugateSkew g).toLinearMap) rank κ ∧
      fixedSpace (T.map (conjugateSkew g).toLinearMap) = (fixedSpace T).map g.toLinearMap := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fixedSpace_conjugate g T⟩
  · rintro ⟨_, A, hA, rfl⟩ ⟨_, B, hB, rfl⟩
    change g.toLinearEquiv.conj A.val * g.toLinearEquiv.conj B.val =
      g.toLinearEquiv.conj B.val * g.toLinearEquiv.conj A.val
    rw [← conj_mul, ← conj_mul, h.1 ⟨A, hA⟩ ⟨B, hB⟩]
  · rw [← ((conjugateSkew g).toLinearEquiv.submoduleMap T).finrank_eq, h.2.1]
  · rw [fixedSpace_conjugate, ← (g.toLinearEquiv.submoduleMap (fixedSpace T)).finrank_eq, h.2.2.1]
  · rw [operatorCasimir_conjugate, h.2.2.2, fixedSpace_conjugate, projection_map_isometry,
      map_smul, map_sub]
    have hid : g.toLinearEquiv.conj LinearMap.id = LinearMap.id :=
      LinearMap.ext fun x => g.apply_symm_apply x
    rw [hid]

private theorem orthogonalSplit_range {ι : Type*} [DecidableEq ι]
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E →ₗᵢ[ℝ] F) (U : ι → Submodule ℝ E) (hU : OrthogonalSplit U) :
    OrthogonalSplit (fun i => (U i).map (LinearMap.rangeRestrict f.toLinearMap)) := by
  have ho : Pairwise fun i j => ((U i).map (LinearMap.rangeRestrict f.toLinearMap)).IsOrtho
      ((U j).map (LinearMap.rangeRestrict f.toLinearMap)) := by
    intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change ⟪f x, f y⟫ = 0
    rw [f.inner_map_map]
    exact (hU.1 hij).inner_eq hx hy
  refine ⟨ho, (OrthogonalFamily.of_pairwise ho).isInternal_iff.mpr ?_⟩
  have htop := hU.2.submodule_iSup_eq_top
  have hsurj : Function.Surjective f.toLinearMap.rangeRestrict := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj,
    Submodule.top_orthogonal_eq_bot]

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]

namespace TraceJordanData

variable (M : TraceJordanData J)

/-- The cubic defined by the actual traceless Jordan product. -/
def traceCubic : SymmetricCubic M.traceFree :=
  (SymmetricCubic.ofProduct M.L M.comm (fun x y z => (M.assoc_inner x y z).trans
    (real_inner_comm _ _))).pullback M.traceFree.subtype

theorem traceCubic_L (x y : M.traceFree) :
    M.traceCubic.L x y = M.center (M.L x.val y.val) := by
  apply ext_inner_right ℝ
  intro z
  change M.traceCubic.apply x y z = ⟪M.L x.val y.val - _ • M.unit, z.val⟫
  rw [traceCubic, SymmetricCubic.pullback_apply]
  change ⟪M.L x.val y.val, z.val⟫ = _
  have hz : ⟪M.unit, z.val⟫ = 0 := z.property
  rw [inner_sub_left, real_inner_smul_left, hz, mul_zero, sub_zero]

/-- The ordered trace-one orthogonal Jordan idempotents of a frame. -/
structure Frame where
  point : Fin 3 → J
  trace_one : ∀ a, M.trace (point a) = 1
  mul_point : ∀ a b, M.L (point a) (point b) = if a = b then point a else 0
  sum_unit : ∑ a, point a = M.unit

/-- The plane of a frame is the span of its centered points. -/
def Frame.plane (F : M.Frame) : Submodule ℝ M.traceFree :=
  Submodule.span ℝ (Set.range fun a => M.center (F.point a))

omit [FiniteDimensional ℝ J] in
theorem trace_product (x y : J) : M.trace (M.L x y) = ⟪x, y⟫ := by
  change ⟪M.unit, M.L x y⟫ = _
  rw [← M.assoc_inner, M.L_unit_right, real_inner_comm]

omit [FiniteDimensional ℝ J] in
theorem Frame.unbiased_of_ortho (F G : M.Frame) (h : (F.plane M).IsOrtho (G.plane M))
    (a b : Fin 3) : M.trace (M.L (F.point a) (G.point b)) = 1 / 3 := by
  rw [trace_product]
  have h0 := h.inner_eq (Submodule.subset_span (Set.mem_range_self a))
    (Submodule.subset_span (Set.mem_range_self b))
  change ⟪F.point a - (M.trace (F.point a) / 3) • M.unit,
    G.point b - (M.trace (G.point b) / 3) • M.unit⟫ = 0 at h0
  have ha : ⟪F.point a, M.unit⟫ = 1 := (real_inner_comm _ _).trans (F.trace_one a)
  have hb : ⟪M.unit, G.point b⟫ = 1 := G.trace_one b
  simp only [F.trace_one, G.trace_one, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, ha, hb, M.unit_trace] at h0
  linarith

/-- A fixed algebra is unital and closed, and a two-dimensional fixed space is a frame plane
whenever the actual frame model realizes every closed trace-free two-plane. -/
theorem fixedSubalgebra_and_framePlane
    (frames : ∀ U : Submodule ℝ M.traceFree, Module.finrank ℝ U = 2 →
      IsClosedPiece M.traceCubic U → ∃ F : M.Frame, U = F.plane M)
    (T : Submodule ℝ (SkewOperator J)) (hT : T ≤ M.skewDerivations) :
    fixedSpace T = (ℝ ∙ M.unit) ⊔ (M.fixedTraceless T).map M.traceFree.subtype ∧
      M.unit ∈ fixedSpace T ∧
      (∀ x y, x ∈ fixedSpace T → y ∈ fixedSpace T → M.L x y ∈ fixedSpace T) ∧
      IsClosedPiece M.traceCubic (M.fixedTraceless T) ∧
      (Module.finrank ℝ (M.fixedTraceless T) = 2 →
        ∃ F : M.Frame, M.fixedTraceless T = F.plane M) := by
  have hc : IsClosedPiece M.traceCubic (M.fixedTraceless T) := by
    intro x y hx hy
    rw [M.traceCubic_L]
    exact M.fixedTraceless_closed hT hx hy
  exact ⟨M.fixedAlgebra_eq_unit_sup hT, (M.fixedAlgebra_unital_closed hT).1,
    (M.fixedAlgebra_unital_closed hT).2, hc, fun hd => frames _ hd hc⟩

/-- The fixed spaces of a complete frame-type operator splitting are an orthogonal direct sum
of actual frame planes, with all cross-frame overlaps equal to one third. -/
theorem operatorOD_fixedPlanes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Submodule ℝ (SkewOperator J)) (hK : K ≤ M.skewDerivations)
    (T : ι → Submodule ℝ K) (hT : OrthogonalSplit T)
    (rank : ℕ) (κ scalar : ℝ) (hκ : 0 < κ)
    (hfull : operatorCasimir (LinearMap.range (M.restrictOperators K hK).toLinearMap) =
      scalar • LinearMap.id)
    (htypes : ∀ i, IsFrameType ((T i).map (M.restrictOperators K hK).toLinearMap) rank κ)
    (hcard : 2 * Fintype.card ι = Module.finrank ℝ M.traceFree)
    (frames : ∀ U : Submodule ℝ M.traceFree, Module.finrank ℝ U = 2 →
      IsClosedPiece M.traceCubic U → ∃ F : M.Frame, U = F.plane M) :
    OrthogonalSplit (fun i => M.fixedTraceless ((T i).map K.subtype)) ∧
      (∀ i, IsClosedPiece M.traceCubic (M.fixedTraceless ((T i).map K.subtype))) ∧
      ∃ F : ι → M.Frame,
        (∀ i, M.fixedTraceless ((T i).map K.subtype) = (F i).plane M) ∧
        (∀ i j, i ≠ j → ∀ a b, M.trace (M.L ((F i).point a) ((F j).point b)) = 1 / 3) := by
  let f := M.restrictOperators K hK
  let R := LinearMap.range f.toLinearMap
  let S (i : ι) := (T i).map f.toLinearMap.rangeRestrict
  have hm (i : ι) : (S i).map R.subtype = (T i).map f.toLinearMap := by
    change ((T i).map f.toLinearMap.rangeRestrict).map f.toLinearMap.range.subtype = _
    rw [← Submodule.map_comp, LinearMap.subtype_comp_rangeRestrict]
  have hd (i : ι) : Module.finrank ℝ (M.fixedTraceless ((T i).map K.subtype)) = 2 := by
    rw [M.fixedTraceless_eq_fixedSpace K hK]
    exact (htypes i).2.2.1
  have hfixed (i : ι) : fixedSpace ((S i).map R.subtype) =
      M.fixedTraceless ((T i).map K.subtype) := by
    rw [hm]
    exact (M.fixedTraceless_eq_fixedSpace K hK (T i)).symm
  have hsum : (∑ i, Module.finrank ℝ (fixedSpace ((S i).map R.subtype))) =
      Module.finrank ℝ M.traceFree := by
    calc
      _ = ∑ _ : ι, (2 : ℕ) :=
        Finset.sum_congr rfl fun i _ => by rw [hfixed, hd]
      _ = _ := by simpa [Nat.mul_comm] using hcard
  have hs := fixedSpaces_orthSplit_of_casimir R S (orthogonalSplit_range f T hT) scalar κ hκ
    hfull (fun i => by rw [hm]; exact (htypes i).2.2.2) hsum
  have hsplit : OrthogonalSplit (fun i => M.fixedTraceless ((T i).map K.subtype)) := by
    simpa only [hfixed] using hs
  have hc (i : ι) : IsClosedPiece M.traceCubic (M.fixedTraceless ((T i).map K.subtype)) := by
    apply (M.fixedSubalgebra_and_framePlane frames _ ?_).2.2.2.1
    rintro _ ⟨D, _, rfl⟩
    exact hK D.property
  choose F hF using fun i => frames _ (hd i) (hc i)
  refine ⟨hsplit, hc, F, hF, fun i j hij a b => ?_⟩
  apply Frame.unbiased_of_ortho M
  rw [← hF i, ← hF j]
  exact hsplit.1 hij

end TraceJordanData

end

end ThirteenPlanes.Cartan
