module

public import ThirteenPlanes.MinimumHessian.Invariance
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

set_option backward.privateInPublic true

/-! The trace metric and Casimir of a subspace of real skew endomorphisms. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The actual skew-adjoint real endomorphisms of the representation space. -/
def skewOperators (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    Submodule ℝ (Module.End ℝ V) where
  carrier := {A | IsSkew A}
  zero_mem' := by intro x y; simp
  add_mem' := by
    intro A B hA hB x y
    simp [inner_add_left, inner_add_right, hA x y, hB x y, add_comm]
  smul_mem' := by
    intro a A hA x y
    simp [real_inner_smul_left, real_inner_smul_right, hA x y]

abbrev SkewOperator (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :=
  ↥(skewOperators V)

private def tracePair (A B : SkewOperator V) : ℝ :=
  -LinearMap.trace ℝ V (A.val * B.val)

omit [FiniteDimensional ℝ V] in
private theorem tracePair_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)
    (A B : SkewOperator V) : tracePair A B = ∑ i, ⟪A.val (e i), B.val (e i)⟫ := by
  rw [tracePair, SymmetricCubic.trace_eq_sum_inner e, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change -⟪e i, A.val (B.val (e i))⟫ = _
  rw [← A.property]

private theorem tracePair_definite (A : SkewOperator V) (h : tracePair A A = 0) : A = 0 := by
  let e := stdOrthonormalBasis ℝ V
  rw [tracePair_eq_sum e] at h
  apply Subtype.ext
  apply e.toBasis.ext
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => real_inner_self_nonneg)).mp h i
    (Finset.mem_univ i)
  change A.val (e i) = 0
  exact inner_self_eq_zero.mp hi

private instance skewTraceCore : InnerProductSpace.Core ℝ (SkewOperator V) where
  inner := tracePair
  conj_inner_symm A B := by
    simp only [RCLike.conj_to_real, tracePair, LinearMap.trace_mul_comm]
  re_inner_nonneg A := by
    rw [RCLike.re_to_real, tracePair_eq_sum (stdOrthonormalBasis ℝ V)]
    exact Finset.sum_nonneg fun _ _ => real_inner_self_nonneg
  add_left A B C := by
    simp [tracePair, add_mul, add_comm]
  smul_left A B a := by
    simp [tracePair]
  definite A := tracePair_definite A

noncomputable instance : NormedAddCommGroup (SkewOperator V) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

noncomputable instance : InnerProductSpace ℝ (SkewOperator V) :=
  InnerProductSpace.ofCore (𝕜 := ℝ) (F := SkewOperator V) inferInstance

/-- The operator inner product is minus the trace in the given representation. -/
theorem skewOperator_inner (A B : SkewOperator V) :
    ⟪A, B⟫ = -LinearMap.trace ℝ V (A.val * B.val) := rfl

/-- A finite orthogonal internal direct sum, allowing zero summands. -/
def OrthogonalSplit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [DecidableEq ι] (U : ι → Submodule ℝ E) : Prop :=
  (Pairwise fun i j => (U i).IsOrtho (U j)) ∧ DirectSum.IsInternal U

/-- The common kernel of a space of represented skew operators. -/
def fixedSpace (T : Submodule ℝ (SkewOperator V)) : Submodule ℝ V :=
  ⨅ X : T, LinearMap.ker X.val.val

omit [FiniteDimensional ℝ V] in
@[simp] theorem mem_fixedSpace (T : Submodule ℝ (SkewOperator V)) (x : V) :
    x ∈ fixedSpace T ↔ ∀ X : T, X.val.val x = 0 := by
  simp [fixedSpace, Submodule.mem_iInf]

/-- Orthogonal projection as a real linear endomorphism. -/
abbrev projection (U : Submodule ℝ V) : Module.End ℝ V :=
  U.starProjection.toLinearMap

private def casimirOfBasis (T : Submodule ℝ (SkewOperator V)) {α : Type*} [Fintype α]
    (b : OrthonormalBasis α ℝ T) : Module.End ℝ V :=
  -∑ a, (b a).val.val * (b a).val.val

/-- The Casimir uses the actual trace-orthonormal operators on the representation space. -/
def operatorCasimir (T : Submodule ℝ (SkewOperator V)) : Module.End ℝ V :=
  casimirOfBasis T (stdOrthonormalBasis ℝ T)

private def evaluation (T : Submodule ℝ (SkewOperator V)) (x : V) : T →ₗ[ℝ] V where
  toFun X := X.val.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem casimirOfBasis_pairing (T : Submodule ℝ (SkewOperator V))
    {α : Type*} [Fintype α] (b : OrthonormalBasis α ℝ T) (x y : V) :
    ⟪casimirOfBasis T b x, y⟫ =
      LinearMap.trace ℝ T ((evaluation T x).adjoint.comp (evaluation T y)) := by
  rw [casimirOfBasis, SymmetricCubic.trace_eq_sum_inner b]
  simp only [LinearMap.neg_apply, LinearMap.sum_apply, inner_neg_left, sum_inner,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  change -⟪(b a).val.val ((b a).val.val x), y⟫ =
    ⟪b a, (evaluation T x).adjoint ((evaluation T y) (b a))⟫
  rw [(b a).val.property, neg_neg, LinearMap.adjoint_inner_right]
  rfl

/-- The trace-normalized Casimir is independent of the orthonormal basis. -/
theorem operatorCasimir_eq_sum (T : Submodule ℝ (SkewOperator V))
    {α : Type*} [Fintype α] (b : OrthonormalBasis α ℝ T) :
    operatorCasimir T = -∑ a, (b a).val.val * (b a).val.val := by
  ext x
  apply ext_inner_right ℝ
  intro y
  change ⟪casimirOfBasis T (stdOrthonormalBasis ℝ T) x, y⟫ = ⟪casimirOfBasis T b x, y⟫
  rw [casimirOfBasis_pairing, casimirOfBasis_pairing]

/-- The trace of the Casimir equals the dimension of the operator subspace. -/
theorem trace_operatorCasimir (T : Submodule ℝ (SkewOperator V)) :
    LinearMap.trace ℝ V (operatorCasimir T) = Module.finrank ℝ T := by
  let b := stdOrthonormalBasis ℝ T
  rw [operatorCasimir_eq_sum T b, map_neg, map_sum, ← Finset.sum_neg_distrib]
  have hb (a : Fin (Module.finrank ℝ T)) :
      -LinearMap.trace ℝ V ((b a).val.val * (b a).val.val) = 1 := by
    change ⟪b a, b a⟫ = 1
    exact orthonormal_iff_ite.mp b.orthonormal a a ▸ by simp
  simp [hb]

/-- The Casimir adds over an internal orthogonal splitting of the operator subspace. -/
theorem operatorCasimir_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Submodule ℝ (SkewOperator V)) (T : ι → Submodule ℝ K)
    (hT : OrthogonalSplit T) :
    operatorCasimir K = ∑ i, operatorCasimir ((T i).map K.subtype) := by
  let b (i : ι) := stdOrthonormalBasis ℝ (T i)
  let B := hT.2.collectedOrthonormalBasis (OrthogonalFamily.of_pairwise hT.1) b
  have hB (i) (a : Fin (Module.finrank ℝ (T i))) : B ⟨i, a⟩ = (b i a : K) := by
    simp [B, DirectSum.IsInternal.collectedOrthonormalBasis]
  let g (i : ι) : T i →ₗᵢ[ℝ] (T i).map K.subtype := K.subtypeₗᵢ.submoduleMap (T i)
  have hg (i : ι) : Function.Surjective (g i) := by
    intro x
    obtain ⟨y, hy, he⟩ := x.property
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  have hgi (i : ι) : Function.Injective (g i).toLinearMap := by
    intro x y hxy
    have hv := congrArg (fun a : (T i).map K.subtype => a.val) hxy
    exact Subtype.ext (Subtype.ext hv)
  let f (i : ι) : T i ≃ₗᵢ[ℝ] (T i).map K.subtype :=
    { LinearEquiv.ofBijective (g i).toLinearMap ⟨hgi i, hg i⟩ with
      norm_map' := fun _ => rfl }
  have hf (i) (a : Fin (Module.finrank ℝ (T i))) :
      ((f i (b i a)).val : SkewOperator V) = (b i a : K).val := rfl
  rw [operatorCasimir_eq_sum K B, Fintype.sum_sigma]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [operatorCasimir_eq_sum _ ((b i).map (f i))]
  simp only [hB, OrthonormalBasis.map_apply, hf]

private theorem trace_projection (U : Submodule ℝ V) :
    LinearMap.trace ℝ V (projection U) = Module.finrank ℝ U := by
  have h : LinearMap.IsProj U (projection U) :=
    ⟨U.starProjection_apply_mem, fun x hx => U.starProjection_mem_subspace_eq_self ⟨x, hx⟩⟩
  exact h.trace

/-- A family of orthogonal projections summing to the identity gives an orthogonal internal sum. -/
theorem orthogonalSplit_of_sum_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι → Submodule ℝ V) (h : (∑ i, projection (U i)) = LinearMap.id) :
    OrthogonalSplit U := by
  have hx (x : V) : ∑ i, (U i).starProjection x = x := by
    have h' := LinearMap.congr_fun h x
    simpa only [LinearMap.sum_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe] using h'
  have ha : Pairwise fun i j => (U i).IsOrtho (U j) := by
    intro i j hij
    apply Submodule.isOrtho_iff_le.mpr
    intro x hxi
    have hn : ∑ k, ‖(U k).orthogonalProjectionOnto x‖ ^ 2 = ‖x‖ ^ 2 := by
      have hi := congrArg (fun z : V => ⟪z, x⟫) (hx x)
      rw [sum_inner, real_inner_self_eq_norm_sq] at hi
      simpa only [← (U _).re_inner_starProjection_eq_normSq, RCLike.re_to_real] using hi
    have hc : ‖(U i).orthogonalProjectionOnto x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← (U i).norm_coe, ← (U i).starProjection_apply,
        (U i).starProjection_mem_subspace_eq_self ⟨x, hxi⟩]
    have hz : (∑ k ∈ Finset.univ.erase i, ‖(U k).orthogonalProjectionOnto x‖ ^ 2) = 0 := by
      have hh := Finset.sum_erase_add Finset.univ
        (fun k => ‖(U k).orthogonalProjectionOnto x‖ ^ 2) (Finset.mem_univ i)
      rw [hn, hc] at hh
      linarith
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)).mp hz j
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
    have hproj : (U j).starProjection x = 0 := by
      rw [(U j).starProjection_apply]
      exact congrArg Subtype.val (norm_eq_zero.mp (sq_eq_zero_iff.mp hj))
    exact (Submodule.starProjection_apply_eq_zero_iff (K := U j)).mp hproj
  refine ⟨ha, ?_⟩
  apply (OrthogonalFamily.of_pairwise ha).isInternal_iff.mpr
  have htop : ⨆ i, U i = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    rw [← hx x]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup U i) ((U i).starProjection_apply_mem x)
  rw [htop, Submodule.top_orthogonal_eq_bot]

/-- Casimir lemma. The hypothesis is scalarity of the full Casimir in the given representation. -/
theorem fixedSpaces_orthSplit_of_casimir {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Submodule ℝ (SkewOperator V)) (T : ι → Submodule ℝ K)
    (split : OrthogonalSplit T) (scalar κ : ℝ) (hκ : 0 < κ)
    (hfull : operatorCasimir K = scalar • LinearMap.id)
    (hpieces : ∀ i, operatorCasimir ((T i).map K.subtype) =
      κ • (LinearMap.id - projection (fixedSpace ((T i).map K.subtype))))
    (hcard : (∑ i, Module.finrank ℝ (fixedSpace ((T i).map K.subtype))) =
      Module.finrank ℝ V) :
    OrthogonalSplit fun i => fixedSpace ((T i).map K.subtype) := by
  let U := fun i => fixedSpace ((T i).map K.subtype)
  have h := operatorCasimir_sum K T split
  simp_rw [hfull, hpieces] at h
  change scalar • (LinearMap.id : Module.End ℝ V) = ∑ i, κ • (LinearMap.id - projection (U i)) at h
  have hsum : (∑ i, projection (U i)) =
      ((Fintype.card ι : ℝ) - scalar / κ) • LinearMap.id := by
    have hs : (∑ _ : ι, (LinearMap.id : Module.End ℝ V)) =
        (Fintype.card ι : ℝ) • LinearMap.id := by
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    simp only [← Finset.smul_sum, Finset.sum_sub_distrib, hs] at h
    have hh := congrArg (fun A : Module.End ℝ V => κ⁻¹ • A) h
    simp only [smul_smul, inv_mul_cancel₀ hκ.ne', one_smul] at hh
    calc
      _ = (Fintype.card ι : ℝ) • LinearMap.id - (κ⁻¹ * scalar) • LinearMap.id := by
        rw [hh]
        abel
      _ = _ := by rw [sub_smul, div_eq_inv_mul]
  apply orthogonalSplit_of_sum_projection U
  by_cases hV : Module.finrank ℝ V = 0
  · let : Subsingleton V := Module.finrank_zero_iff.mp hV
    ext x
    exact Subsingleton.elim _ _
  · have ht := congrArg (LinearMap.trace ℝ V) hsum
    rw [map_sum, map_smul, LinearMap.trace_id, smul_eq_mul] at ht
    simp only [trace_projection] at ht
    have hcast : (∑ i, (Module.finrank ℝ (U i) : ℝ)) = (Module.finrank ℝ V : ℝ) := by
      exact_mod_cast hcard
    rw [hcast] at ht
    have hn : (Module.finrank ℝ V : ℝ) ≠ 0 := by exact_mod_cast hV
    have hcoef : (Fintype.card ι : ℝ) - scalar / κ = 1 := by
      apply mul_right_cancel₀ hn
      rw [← ht, one_mul]
    rw [hsum, hcoef, one_smul]

end

end ThirteenPlanes.Cartan
