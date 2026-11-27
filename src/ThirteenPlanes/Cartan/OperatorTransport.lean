module

public import ThirteenPlanes.Cartan.JordanOperators

@[expose] public section

/-! Conjugation of the trace-normalized skew-operator models. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem conj_mul {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (g : E ≃ₗ[ℝ] F) (A B : Module.End ℝ E) :
    g.conj (A * B) = g.conj A * g.conj B := by
  ext x
  change g (A (B (g.symm x))) = g (A (g.symm (g (B (g.symm x)))))
  rw [g.symm_apply_apply]

/-- Conjugating a skew operator by a real orthogonal change of coordinates. -/
def conjugateSkew (g : V ≃ₗᵢ[ℝ] V) : SkewOperator V ≃ₗᵢ[ℝ] SkewOperator V := by
  let f := g.toLinearEquiv.conj
  have hskew (A : SkewOperator V) : IsSkew (f A.val) := by
    intro x y
    change ⟪g (A.val (g.symm x)), y⟫ = -⟪x, g (A.val (g.symm y))⟫
    rw [← g.apply_symm_apply y, g.inner_map_map, ← g.apply_symm_apply x, g.inner_map_map,
      g.symm_apply_apply, A.property, g.symm_apply_apply]
  have hskew' (A : SkewOperator V) : IsSkew (f.symm A.val) := by
    intro x y
    change ⟪g.symm (A.val (g x)), y⟫ = -⟪x, g.symm (A.val (g y))⟫
    rw [← g.symm_apply_apply y, g.symm.inner_map_map, ← g.symm_apply_apply x, g.symm.inner_map_map,
      g.apply_symm_apply, A.property, g.apply_symm_apply]
  let e : SkewOperator V ≃ₗ[ℝ] SkewOperator V :=
    { toFun := fun A => ⟨f A.val, hskew A⟩
      invFun := fun A => ⟨f.symm A.val, hskew' A⟩
      left_inv := fun A => Subtype.ext (f.symm_apply_apply A.val)
      right_inv := fun A => Subtype.ext (f.apply_symm_apply A.val)
      map_add' := fun A B => Subtype.ext (f.map_add A.val B.val)
      map_smul' := fun r A => Subtype.ext (f.map_smul r A.val) }
  refine { e with norm_map' := fun A => ?_ }
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    skewOperator_inner, skewOperator_inner]
  change -LinearMap.trace ℝ V (f A.val * f A.val) = _
  rw [show f A.val * f A.val = f (A.val * A.val) from (conj_mul g.toLinearEquiv _ _).symm,
    LinearMap.trace_conj']

@[simp] theorem conjugateSkew_val (g : V ≃ₗᵢ[ℝ] V) (A : SkewOperator V) :
    (conjugateSkew g A).val = g.toLinearEquiv.conj A.val := rfl

@[simp] theorem conjugateSkew_symm_apply_apply (g : V ≃ₗᵢ[ℝ] V) (A : SkewOperator V) :
    conjugateSkew g.symm (conjugateSkew g A) = A := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change g.symm (g (A.val (g.symm (g x)))) = A.val x
  rw [g.symm_apply_apply, g.symm_apply_apply]

theorem conjugateSkew_map_roundtrip (g : V ≃ₗᵢ[ℝ] V)
    (T : Submodule ℝ (SkewOperator V)) :
    (T.map (conjugateSkew g).toLinearMap).map (conjugateSkew g.symm).toLinearMap = T := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    change conjugateSkew g.symm (conjugateSkew g A) ∈ T
    rw [conjugateSkew_symm_apply_apply]
    exact hA
  · intro A hA
    exact ⟨conjugateSkew g A, ⟨A, hA, rfl⟩, conjugateSkew_symm_apply_apply g A⟩

/-- Common kernels are carried to their images by conjugation. -/
theorem fixedSpace_conjugate (g : V ≃ₗᵢ[ℝ] V) (T : Submodule ℝ (SkewOperator V)) :
    fixedSpace (T.map (conjugateSkew g).toLinearMap) = (fixedSpace T).map g.toLinearMap := by
  ext x
  rw [mem_fixedSpace, Submodule.mem_map_equiv]
  change (∀ D : T.map (conjugateSkew g).toLinearMap, D.val.val x = 0) ↔
    g.symm x ∈ fixedSpace T
  rw [mem_fixedSpace]
  constructor
  · intro h D
    have hd := h ⟨conjugateSkew g D.val, Submodule.mem_map_of_mem D.property⟩
    change g (D.val.val (g.symm x)) = 0 at hd
    exact g.injective (hd.trans g.map_zero.symm)
  · rintro h ⟨D, W, hW, rfl⟩
    change g (W.val (g.symm x)) = 0
    rw [h ⟨W, hW⟩, map_zero]

/-- The Casimir of a conjugated operator space is its conjugated Casimir. -/
theorem operatorCasimir_conjugate (g : V ≃ₗᵢ[ℝ] V) (T : Submodule ℝ (SkewOperator V)) :
    operatorCasimir (T.map (conjugateSkew g).toLinearMap) =
      g.toLinearEquiv.conj (operatorCasimir T) := by
  let b := stdOrthonormalBasis ℝ T
  let W := T.map (conjugateSkew g).toLinearMap
  let e : T ≃ₗᵢ[ℝ] W :=
    { (conjugateSkew g).toLinearEquiv.submoduleMap T with
      norm_map' := fun A => (conjugateSkew g).norm_map A.val }
  change operatorCasimir W = _
  rw [operatorCasimir_eq_sum W (b.map e), operatorCasimir_eq_sum T b, map_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change g.toLinearEquiv.conj (b i).val.val * g.toLinearEquiv.conj (b i).val.val =
    g.toLinearEquiv.conj ((b i).val.val * (b i).val.val)
  rw [conj_mul]

/-- The scalar of an invariant full Casimir in a nonzero representation is the dimension ratio. -/
theorem fullCasimir_eq_finrank_div {G : Type*} (act : G → V ≃ₗᵢ[ℝ] V)
    (K : Submodule ℝ (SkewOperator V)) (hV : Module.finrank ℝ V ≠ 0)
    (normalizes : ∀ g, K.map (conjugateSkew (act g)).toLinearMap = K)
    (commutant : ∀ S : Module.End ℝ V,
      (∀ g x, S (act g x) = act g (S x)) → ∃ a : ℝ, S = a • LinearMap.id) :
    operatorCasimir K = (Module.finrank ℝ K / (Module.finrank ℝ V : ℝ)) • LinearMap.id := by
  obtain ⟨a, ha⟩ := commutant (operatorCasimir K) (by
    intro g x
    have eq := operatorCasimir_conjugate (act g) K
    rw [normalizes] at eq
    have hx := LinearMap.congr_fun eq (act g x)
    change operatorCasimir K (act g x) = act g (operatorCasimir K ((act g).symm (act g x))) at hx
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hx)
  rw [ha]
  have ht := trace_operatorCasimir K
  rw [ha, map_smul, LinearMap.trace_id, smul_eq_mul] at ht
  congr 1
  exact (eq_div_iff (by exact_mod_cast hV)).mpr ht

end

end ThirteenPlanes.Cartan
