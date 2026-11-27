module

public import ThirteenPlanes.MixedGram

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators InnerProductSpace RealInnerProductSpace TensorProduct

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {h : SymmetricCubic V} {c : ℝ}
  {U U' : Submodule ℝ V}

private abbrev proj (S : Submodule ℝ V) : Module.End ℝ V := S.starProjection.toLinearMap

private theorem trace_proj_comp (S : Submodule ℝ V) (A : Module.End ℝ V)
    {α : Type*} [Fintype α] (e : OrthonormalBasis α ℝ S) :
    LinearMap.trace ℝ V ((proj S).comp A) = ∑ a, ⟪(e a : V), A (e a : V)⟫ := by
  change LinearMap.trace ℝ V ((S.subtype.comp S.orthogonalProjectionOnto.toLinearMap).comp A) = _
  rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm' (S.orthogonalProjectionOnto.toLinearMap.comp A)
    S.subtype, SymmetricCubic.trace_eq_sum_inner e]
  exact Finset.sum_congr rfl fun a _ =>
    S.inner_orthogonalProjectionOnto_eq_of_mem_left (e a) (A (e a : V))

private theorem trace_proj_comp_proj (S W : Submodule ℝ V)
    {α : Type*} [Fintype α] (e : OrthonormalBasis α ℝ S) :
    LinearMap.trace ℝ V ((proj S).comp (proj W)) =
      ∑ a, ‖W.starProjection (e a : V)‖ ^ 2 := by
  rw [trace_proj_comp S (proj W) e]
  refine Finset.sum_congr rfl fun a _ => ?_
  change ⟪(e a : V), W.starProjection (e a : V)⟫ = _
  rw [real_inner_comm (W.starProjection (e a : V)) (e a : V)]
  exact W.re_inner_starProjection_eq_normSq (e a : V)

private theorem trace_proj (S : Submodule ℝ V) :
    LinearMap.trace ℝ V (proj S) = Module.finrank ℝ S := by
  let e := stdOrthonormalBasis ℝ S
  rw [← LinearMap.comp_id (proj S), trace_proj_comp S LinearMap.id e]
  have he (a : Fin (Module.finrank ℝ S)) : ⟪(e a : V), (e a : V)⟫ = 1 := by
    change ⟪e a, e a⟫ = 1
    rw [real_inner_self_eq_norm_sq, e.orthonormal.norm_eq_one, one_pow]
  simp only [LinearMap.id_apply, he]
  simp

/-- Half the trace of the projection onto the mixed product space followed by the
projection onto the third plane. The geometric assertions concern distinct indices. -/
def planeShare {ι : Type*} (h : SymmetricCubic V) (planes : PlaneDecomposition V ι)
    (i j k : ι) : ℝ :=
  (1 / 2) * LinearMap.trace ℝ V
    ((planes.proj k).comp (proj (mixedProductSpace h (planes.plane i) (planes.plane j))))

private theorem mixedTensorMap_norm (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2) (t : U ⊗[ℝ] U') :
    ‖mixedTensorMap h U U' t‖ = Real.sqrt (c / 2) * ‖t‖ := by
  let M := mixedTensorMap h U U'
  let A : V →ₗ[ℝ] U ⊗[ℝ] U' :=
    LinearMap.adjoint (𝕜 := ℝ) (E := U ⊗[ℝ] U') (F := V) M
  have hA : A (M t) = (c / 2) • t :=
    DFunLike.congr_fun (mixedTensorMap_adjoint_comp round orth closed closed' dim) t
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (div_nonneg round.positive.le (by norm_num : (0 : ℝ) ≤ 2))]
  change ‖M t‖ ^ 2 = c / 2 * ‖t‖ ^ 2
  calc
    ‖M t‖ ^ 2 = ⟪M t, M t⟫ := (real_inner_self_eq_norm_sq (M t)).symm
    _ = ⟪t, A (M t)⟫ :=
      (LinearMap.adjoint_inner_right (𝕜 := ℝ) (E := U ⊗[ℝ] U') (F := V) M t (M t)).symm
    _ = _ := by
      rw [hA]
      exact (real_inner_smul_right t t (c / 2)).trans
        (congrArg ((c / 2) * ·) (real_inner_self_eq_norm_sq t))

/-- Dividing the mixed-product map by the square root of the Gram scalar
gives an onto isometry from the metric tensor product to its actual image. -/
def mixedTensorIsometry (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2) :
    U ⊗[ℝ] U' ≃ₗᵢ[ℝ] mixedProductSpace h U U' := by
  let s := Real.sqrt (c / 2)
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos round.positive (by norm_num))
  let e := LinearEquiv.ofInjective (mixedTensorMap h U U')
    (mixedTensorMap_injective round orth closed closed' dim)
  refine ⟨e.trans (LinearEquiv.smulOfNeZero ℝ (mixedProductSpace h U U') s⁻¹ (inv_ne_zero hs.ne')), ?_⟩
  intro t
  change ‖s⁻¹ • mixedTensorMap h U U' t‖ = ‖t‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs),
    mixedTensorMap_norm round orth closed closed' dim]
  change s⁻¹ * (s * ‖t‖) = ‖t‖
  rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

theorem mixedTensorIsometry_apply (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2) (t : U ⊗[ℝ] U') :
    (mixedTensorIsometry round orth closed closed' dim t : V) =
      (Real.sqrt (c / 2))⁻¹ • mixedTensorMap h U U' t := rfl

variable {ι : Type*} {planes : PlaneDecomposition V ι}

theorem planeShare_eq_sum_projected_sq (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    {i j : ι} (hij : i ≠ j) (k : ι)
    {α β : Type*} [Fintype α] [Fintype β]
    (e : OrthonormalBasis α ℝ (planes.plane i)) (f : OrthonormalBasis β ℝ (planes.plane j)) :
    planeShare h planes i j k =
      (1 / c) * ∑ a, ∑ b, ‖planes.proj k (h.L (e a : V) (f b : V))‖ ^ 2 := by
  let W := mixedProductSpace h (planes.plane i) (planes.plane j)
  let K := planes.plane k
  let s := Real.sqrt (c / 2)
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos round.positive (by norm_num))
  let b := (e.tensorProduct f).map
    (mixedTensorIsometry round (planes.pairwise_orthogonal hij) (closed i) (closed j)
      (planes.dimension i))
  have hb (p : α × β) : (b p : V) = s⁻¹ • h.L (e p.1 : V) (f p.2 : V) := by
    simp [b, s, mixedTensorIsometry_apply, OrthonormalBasis.tensorProduct_apply']
  change (1 / 2) * LinearMap.trace ℝ V ((proj K).comp (proj W)) = _
  rw [LinearMap.trace_comp_comm' (proj W) (proj K), trace_proj_comp_proj W K b,
    Fintype.sum_prod_type]
  simp only [hb, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), mul_pow,
    ← Finset.mul_sum]
  rw [← mul_assoc]
  congr 1
  change (1 / 2) * ((Real.sqrt (c / 2))⁻¹) ^ 2 = 1 / c
  rw [inv_pow, Real.sq_sqrt (div_nonneg round.positive.le (by norm_num : (0 : ℝ) ≤ 2))]
  field_simp [round.positive.ne']

/-- The projection-trace share is the sum of squares of the cubic coefficients
in any three orthonormal bases, divided by the round strength. -/
theorem planeShare_eq_sum_cubic_sq (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    {i j : ι} (hij : i ≠ j) (k : ι)
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (e : OrthonormalBasis α ℝ (planes.plane i)) (f : OrthonormalBasis β ℝ (planes.plane j))
    (g : OrthonormalBasis γ ℝ (planes.plane k)) :
    planeShare h planes i j k =
      (1 / c) * ∑ a, ∑ b, ∑ d, (h.apply (e a : V) (f b : V) (g d : V)) ^ 2 := by
  rw [planeShare_eq_sum_projected_sq round closed hij k e f]
  have hn (v : V) : ‖planes.proj k v‖ ^ 2 = ∑ d, ⟪v, (g d : V)⟫ ^ 2 := by
    change ‖(planes.plane k).orthogonalProjectionOnto v‖ ^ 2 = _
    rw [← g.sum_sq_inner_left]
    simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  simp only [hn, SymmetricCubic.apply]

theorem planeShare_swap_first (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    {i j : ι} (hij : i ≠ j) (k : ι) :
    planeShare h planes i j k = planeShare h planes j i k := by
  let e (i : ι) := stdOrthonormalBasis ℝ (planes.plane i)
  rw [planeShare_eq_sum_cubic_sq round closed hij k (e i) (e j) (e k),
    planeShare_eq_sum_cubic_sq round closed hij.symm k (e j) (e i) (e k)]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [h.apply_swap₁₂]

theorem planeShare_swap_last (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) :
    planeShare h planes i j k = planeShare h planes i k j := by
  let e (i : ι) := stdOrthonormalBasis ℝ (planes.plane i)
  rw [planeShare_eq_sum_cubic_sq round closed hij k (e i) (e j) (e k),
    planeShare_eq_sum_cubic_sq round closed hik j (e i) (e k) (e j)]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
  rw [h.apply_swap₂₃]

theorem planeShare_cycle (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) :
    planeShare h planes i j k = planeShare h planes j k i :=
  (planeShare_swap_first round closed hij k).trans (planeShare_swap_last round closed hij.symm hjk)

private theorem trace_proj_comp_proj_nonneg (S W : Submodule ℝ V) :
    0 ≤ LinearMap.trace ℝ V ((proj S).comp (proj W)) := by
  rw [trace_proj_comp_proj S W (stdOrthonormalBasis ℝ S)]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem trace_proj_comp_proj_eq_zero_iff (S W : Submodule ℝ V) :
    LinearMap.trace ℝ V ((proj S).comp (proj W)) = 0 ↔ S.IsOrtho W := by
  let e := stdOrthonormalBasis ℝ S
  rw [trace_proj_comp_proj S W e, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _),
    Submodule.isOrtho_iff_le]
  constructor
  · intro zeros x hx
    have hrestrict : (proj W).comp S.subtype = 0 := by
      apply e.toBasis.ext
      intro a
      change W.starProjection (e a : V) = 0
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp (zeros a (Finset.mem_univ a)))
    exact (Submodule.starProjection_apply_eq_zero_iff (K := W)).mp
      (DFunLike.congr_fun hrestrict ⟨x, hx⟩)
  · intro hs a _
    rw [(Submodule.starProjection_apply_eq_zero_iff (K := W)).mpr (hs (e a).property), norm_zero, zero_pow]
    exact two_ne_zero

private theorem trace_proj_comp_proj_add_complement (S W : Submodule ℝ V) :
    LinearMap.trace ℝ V ((proj S).comp (proj W)) +
      LinearMap.trace ℝ V ((proj S).comp (proj Wᗮ)) = Module.finrank ℝ S := by
  have hsum : (proj W) + (proj Wᗮ) = (LinearMap.id : V →ₗ[ℝ] V) := by
    ext x
    exact W.starProjection_add_starProjection_orthogonal x
  rw [← map_add, ← LinearMap.comp_add, hsum, LinearMap.comp_id, trace_proj]

/-- Projection-trace shares lie in the unit interval. Their two extremes
are exactly orthogonality and containment of the third plane. -/
theorem planeShare_bounds (h : SymmetricCubic V) (planes : PlaneDecomposition V ι) (i j k : ι) :
    planeShare h planes i j k ∈ Set.Icc (0 : ℝ) 1 ∧
      (planeShare h planes i j k = 1 ↔
        planes.plane k ≤ mixedProductSpace h (planes.plane i) (planes.plane j)) ∧
      (planeShare h planes i j k = 0 ↔
        (planes.plane k).IsOrtho (mixedProductSpace h (planes.plane i) (planes.plane j))) := by
  let S := planes.plane k
  let W := mixedProductSpace h (planes.plane i) (planes.plane j)
  have total := trace_proj_comp_proj_add_complement S W
  rw [show Module.finrank ℝ S = 2 from planes.dimension k, Nat.cast_ofNat] at total
  have nonneg := trace_proj_comp_proj_nonneg S W
  have nonneg' := trace_proj_comp_proj_nonneg S Wᗮ
  have same : planeShare h planes i j k = (1 / 2) * LinearMap.trace ℝ V ((proj S).comp (proj W)) := rfl
  rw [same]
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · have hzero := trace_proj_comp_proj_eq_zero_iff S Wᗮ
    rw [Submodule.isOrtho_iff_le, Submodule.orthogonal_orthogonal] at hzero
    rw [← hzero]
    constructor <;> intro hEq <;> linarith
  · have hzero := trace_proj_comp_proj_eq_zero_iff S W
    rw [← hzero]
    constructor <;> intro hEq <;> linarith

/-- The plane-system isometry criterion for an arbitrary closed round plane system. -/
theorem planeShare_tensor_isometry (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    {j k : ι} (hjk : j ≠ k) :
    (∀ (x x' : planes.plane j) (y y' : planes.plane k),
      ⟪h.L (x : V) (y : V), h.L (x' : V) (y' : V)⟫ =
        (c / 2) * (⟪x, x'⟫ * ⟪y, y'⟫)) ∧
    (∃ E : planes.plane j ⊗[ℝ] planes.plane k ≃ₗᵢ[ℝ]
        mixedProductSpace h (planes.plane j) (planes.plane k),
      ∀ t, mixedTensorMap h (planes.plane j) (planes.plane k) t =
        Real.sqrt (c / 2) • (E t : V)) ∧
    Module.finrank ℝ (mixedProductSpace h (planes.plane j) (planes.plane k)) = 4 ∧
    mixedProductSpace h (planes.plane j) (planes.plane k) ≤ (planes.plane j ⊔ planes.plane k)ᗮ ∧
    (∀ i, i ≠ j → i ≠ k → ∀ {α β : Type*} [Fintype α] [Fintype β]
      (e : OrthonormalBasis α ℝ (planes.plane j)) (f : OrthonormalBasis β ℝ (planes.plane k)),
      planeShare h planes i j k =
        (1 / c) * ∑ a, ∑ b, ‖planes.proj i (h.L (e a : V) (f b : V))‖ ^ 2) := by
  let orth := planes.pairwise_orthogonal hjk
  let dim := planes.dimension j
  have hm := mixedGram round orth (closed j) (closed k) dim (planes.dimension k)
  refine ⟨hm.1, ⟨mixedTensorIsometry round orth (closed j) (closed k) dim, ?_⟩,
    hm.2.2.1, hm.2.2.2, ?_⟩
  · intro t
    rw [mixedTensorIsometry_apply, smul_smul, mul_inv_cancel₀, one_smul]
    exact (Real.sqrt_pos.2 (div_pos round.positive (by norm_num))).ne'
  · intro i hij _ α β _ _ e f
    exact (planeShare_cycle round closed hij hjk).trans
      (planeShare_eq_sum_projected_sq round closed hjk i e f)

section PairSum

variable [Fintype ι]

private theorem sum_plane_projections (planes : PlaneDecomposition V ι) :
    (∑ k, planes.proj k) = (LinearMap.id : V →ₗ[ℝ] V) := by
  let complete (i : ι) : CompleteSpace (planes.plane i) :=
    FiniteDimensional.completeSpace ℝ (planes.plane i)
  let orth : OrthogonalFamily ℝ (fun i => planes.plane i) (fun i => (planes.plane i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise planes.pairwise_orthogonal
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply, LinearMap.id_apply]
  exact orth.sum_projection_of_mem_iSup x (by rw [planes.exhaustive]; trivial)

private theorem planeShare_sum_all_third (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    {i j : ι} (hij : i ≠ j) : (∑ k, planeShare h planes i j k) = 2 := by
  let W := mixedProductSpace h (planes.plane i) (planes.plane j)
  have hcomp : (∑ k, (planes.proj k).comp (proj W)) = (∑ k, planes.proj k).comp (proj W) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  change (∑ k, (1 / 2) * LinearMap.trace ℝ V ((planes.proj k).comp (proj W))) = _
  rw [← Finset.mul_sum, ← map_sum, hcomp, sum_plane_projections, LinearMap.id_comp, trace_proj,
    mixedProductSpace_finrank round (planes.pairwise_orthogonal hij) (closed i) (closed j)
      (planes.dimension i) (planes.dimension j)]
  norm_num

omit [Fintype ι] in
theorem planeShare_repeated_third (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    {i j k : ι} (hij : i ≠ j) (hk : k = i ∨ k = j) :
    planeShare h planes i j k = 0 := by
  have hW := mixedProductSpace_le_orthogonal round (planes.pairwise_orthogonal hij) (closed i) (closed j)
  rw [← Submodule.inf_orthogonal] at hW
  apply (planeShare_bounds h planes i j k).2.2.mpr
  apply Submodule.IsOrtho.symm
  rw [Submodule.isOrtho_iff_le]
  rcases hk with rfl | rfl
  · exact hW.trans inf_le_left
  · exact hW.trans inf_le_right

/-- The shares on all third planes distinct from a fixed pair sum to two. -/
theorem planeShare_pair_sum [DecidableEq ι] (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) {i j : ι} (hij : i ≠ j) :
    (∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), planeShare h planes i j k) = 2 := by
  rw [Finset.sum_filter, ← planeShare_sum_all_third round closed hij]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k ≠ i ∧ k ≠ j
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk, planeShare_repeated_third round closed hij]
    by_contra h
    exact hk ⟨fun hki => h (Or.inl hki), fun hkj => h (Or.inr hkj)⟩

end PairSum

section TripleTotal

variable {m : ℕ} {system : PlaneDecomposition V (Fin m)}

/-- Each unordered triple is represented by its three indices in increasing order. -/
abbrev IncreasingPlaneTriple (m : ℕ) :=
  {t : Fin m × Fin m × Fin m // t.1 < t.2.1 ∧ t.2.1 < t.2.2}

private def ascendingShare (S : Fin m → Fin m → Fin m → ℝ) (i j k : Fin m) : ℝ :=
  if i < j ∧ j < k then S i j k else 0

private def distinctShare (S : Fin m → Fin m → Fin m → ℝ) (i j k : Fin m) : ℝ :=
  if i ≠ j ∧ k ≠ i ∧ k ≠ j then S i j k else 0

private theorem distinctShare_eq_six_orders (round : IsRound h c)
    (closed : IsClosedPlaneSystem h system) (i j k : Fin m) :
    let S := planeShare h system
    distinctShare S i j k =
      ascendingShare S i j k + ascendingShare S i k j +
      ascendingShare S j i k + ascendingShare S j k i +
      ascendingShare S k i j + ascendingShare S k j i := by
  let S := planeShare h system
  by_cases hd : i ≠ j ∧ k ≠ i ∧ k ≠ j
  · have hij := hd.1
    have hki := hd.2.1
    have hkj := hd.2.2
    have h₁ : S i k j = S i j k := (planeShare_swap_last round closed hij hki.symm).symm
    have h₂ : S j i k = S i j k := (planeShare_swap_first round closed hij k).symm
    have h₃ : S j k i = S i j k := (planeShare_cycle round closed hij hkj.symm).symm
    have h₄ : S k i j = S i j k := planeShare_cycle round closed hki hij
    have h₅ : S k j i = S i j k := (planeShare_swap_first round closed hkj i).trans h₃
    change distinctShare S i j k =
      ascendingShare S i j k + ascendingShare S i k j +
      ascendingShare S j i k + ascendingShare S j k i +
      ascendingShare S k i j + ascendingShare S k j i
    simp only [distinctShare, ite_eq_left hd,
      ascendingShare, h₁, h₂, h₃, h₄, h₅]
    simp only [Fin.lt_def, ne_eq, Fin.ext_iff] at hij hki hkj ⊢
    split_ifs <;> first | omega | ring
  · change distinctShare S i j k = _
    simp only [distinctShare, ascendingShare, ite_eq_right hd]
    simp only [Fin.lt_def, ne_eq, Fin.ext_iff] at hd ⊢
    split_ifs <;> first | omega | ring

private theorem distinctShare_total (round : IsRound h c) (closed : IsClosedPlaneSystem h system) :
    (∑ i, ∑ j, ∑ k, distinctShare (planeShare h system) i j k) =
      2 * (m : ℝ) * ((m : ℝ) - 1) := by
  let S := planeShare h system
  have hpair (i j : Fin m) :
      (∑ k, distinctShare S i j k) = if i ≠ j then (2 : ℝ) else 0 := by
    by_cases hij : i ≠ j
    · simpa [distinctShare, hij, Finset.sum_filter, S] using
        planeShare_pair_sum round closed hij
    · simp [distinctShare, hij]
  have hrow (i : Fin m) :
      (∑ j : Fin m, if i ≠ j then (2 : ℝ) else 0) = 2 * ((m : ℝ) - 1) := by
    have hcenter (j : Fin m) : (if i ≠ j then (2 : ℝ) else 0) =
        2 - (if j = i then 2 else 0) := by
      by_cases hij : j = i
      · subst j
        simp
      · simp [hij, Ne.symm hij]
    simp only [hcenter, Finset.sum_sub_distrib]
    simp
    ring
  change (∑ i, ∑ j, ∑ k, distinctShare S i j k) = _
  simp only [hpair, hrow]
  simp
  ring

/-- The sum over increasing triples counts each unordered triple once. -/
theorem planeShare_total (round : IsRound h c) (closed : IsClosedPlaneSystem h system) :
    (∑ t : IncreasingPlaneTriple m, planeShare h system t.val.1 t.val.2.1 t.val.2.2) =
      (m : ℝ) * ((m : ℝ) - 1) / 3 := by
  let S := planeShare h system
  let A := ascendingShare S
  have swapFirst (F : Fin m → Fin m → Fin m → ℝ) :
      (∑ a, ∑ b, ∑ d, F b a d) = ∑ a, ∑ b, ∑ d, F a b d := Finset.sum_comm
  have swapLast (F : Fin m → Fin m → Fin m → ℝ) :
      (∑ a, ∑ b, ∑ d, F a d b) = ∑ a, ∑ b, ∑ d, F a b d :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have cycle (F : Fin m → Fin m → Fin m → ℝ) :
      (∑ a, ∑ b, ∑ d, F b d a) = ∑ a, ∑ b, ∑ d, F a b d := by
    rw [swapFirst (fun a b d => F a d b), swapLast F]
  have cycleTwice (F : Fin m → Fin m → Fin m → ℝ) :
      (∑ a, ∑ b, ∑ d, F d a b) = ∑ a, ∑ b, ∑ d, F a b d := by
    rw [swapLast (fun a b d => F b a d), swapFirst F]
  have reverse (F : Fin m → Fin m → Fin m → ℝ) :
      (∑ a, ∑ b, ∑ d, F d b a) = ∑ a, ∑ b, ∑ d, F a b d := by
    rw [swapFirst (fun a b d => F d a b), cycleTwice F]
  have hcount : (∑ i, ∑ j, ∑ k, distinctShare S i j k) =
      6 * (∑ i, ∑ j, ∑ k, A i j k) := by
    have hsix (i j k : Fin m) :
        distinctShare S i j k = A i j k + A i k j + A j i k + A j k i + A k i j + A k j i :=
      distinctShare_eq_six_orders round closed i j k
    simp_rw [hsix]
    simp only [Finset.sum_add_distrib]
    rw [swapLast A, swapFirst A, cycle A, cycleTwice A, reverse A]
    ring
  have hsubtype : (∑ i, ∑ j, ∑ k, A i j k) =
      ∑ t : IncreasingPlaneTriple m, S t.val.1 t.val.2.1 t.val.2.2 := by
    have ht := Finset.sum_subtype
      (F := (inferInstance : Fintype (IncreasingPlaneTriple m)))
      (p := fun t : Fin m × Fin m × Fin m => t.1 < t.2.1 ∧ t.2.1 < t.2.2)
      (Finset.univ.filter (fun t : Fin m × Fin m × Fin m => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
      (by intro t; simp) (fun t : Fin m × Fin m × Fin m => S t.1 t.2.1 t.2.2)
    simpa only [A, ascendingShare, Finset.sum_filter, Fintype.sum_prod_type] using ht
  have ht : (∑ i, ∑ j, ∑ k, distinctShare S i j k) = _ := distinctShare_total round closed
  rw [ht, hsubtype] at hcount
  change (∑ t : IncreasingPlaneTriple m, S t.val.1 t.val.2.1 t.val.2.2) = _
  linarith

/-- The projection bounds and both sum rules for a complete orthogonal system of closed planes. -/
theorem planeShare_sum_rule (round : IsRound h c) (closed : IsClosedPlaneSystem h system) :
    (∀ i j k : Fin m, i ≠ j → k ≠ i → k ≠ j →
      planeShare h system i j k ∈ Set.Icc (0 : ℝ) 1 ∧
      (planeShare h system i j k = 1 ↔
        system.plane k ≤ mixedProductSpace h (system.plane i) (system.plane j)) ∧
      (planeShare h system i j k = 0 ↔
        (system.plane k).IsOrtho (mixedProductSpace h (system.plane i) (system.plane j)))) ∧
    (∀ i j : Fin m, i ≠ j →
      (∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), planeShare h system i j k) = 2) ∧
    (∑ t : IncreasingPlaneTriple m, planeShare h system t.val.1 t.val.2.1 t.val.2.2) =
      (m : ℝ) * ((m : ℝ) - 1) / 3 :=
  ⟨fun i j k _ _ _ => planeShare_bounds h system i j k,
    fun _ _ hij => planeShare_pair_sum round closed hij, planeShare_total round closed⟩

end TripleTotal

end
end ThirteenPlanes.RoundCubics
