module

public import ThirteenPlanes.Contracts
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-! Restriction of the tensor one-loop field to the homogeneous coupling family.

Under the two contraction laws, the tensor one-loop field evaluated on `aD + bC` is again in the
plane, with coefficients given by the scalar field `familyField`. When the two cubics are linearly
independent the coefficients are unique, and integral curves of the scalar field are exactly the
curves whose cubics solve the tensor equation, the latter read through every linear functional on
the space of cubics. -/

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- Evaluation of a difference of cubics. -/
theorem SymmetricCubic.apply_sub' (h g : SymmetricCubic V) (x y z : V) :
    (h - g).apply x y z = h.apply x y z - g.apply x y z := by
  simp [SymmetricCubic.apply, SymmetricCubic.L, inner_sub_left]

/-- The tensor one-loop field on `a D + b C` is `a' D + b' C` with `(a', b')` the scalar field. -/
theorem oneLoop_restricts_to_familyField (P : CubicPair V) {lam ε : ℝ}
    (h : HasContractionLaws P lam) (u : ℝ × ℝ) :
    oneLoopBeta ε (coupling P u) = coupling P (familyField lam ε u) := by
  rcases u with ⟨a, b⟩
  have hM := h.double (a, b)
  have hT := h.triangle (a, b)
  simp only [oneLoopBeta, hM, hT, SymmetricCubic.insert_smul_id]
  apply SymmetricCubic.ext
  intro x y z
  simp only [coupling_apply, familyField, flowScale, SymmetricCubic.apply_smul,
    SymmetricCubic.apply_sub', SymmetricCubic.apply_add]
  field_simp
  ring

omit [FiniteDimensional ℝ V] in
/-- If the diagonal and mixing cubics are linearly independent, the pencil map is injective. -/
theorem coupling_injective (P : CubicPair V)
    (hli : LinearIndependent ℝ ![P.diagonalCubic, P.mixingCubic]) :
    Function.Injective (coupling P) := by
  refine (injective_iff_map_eq_zero (coupling P)).mpr fun u hu => ?_
  rw [coupling_apply] at hu
  obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff (R := ℝ) (M := SymmetricCubic V) |>.mp hli) u.1 u.2 hu
  exact Prod.ext h1 h2

/-- Uniqueness of the coefficients of the restricted one-loop field. -/
theorem oneLoop_coefficients_unique (P : CubicPair V) {lam ε : ℝ}
    (h : HasContractionLaws P lam)
    (hli : LinearIndependent ℝ ![P.diagonalCubic, P.mixingCubic]) (u v : ℝ × ℝ)
    (hv : oneLoopBeta ε (coupling P u) = coupling P v) : v = familyField lam ε u :=
  coupling_injective P hli (hv.symm.trans (oneLoop_restricts_to_familyField P h u))

/-- Two vectors whose only vanishing combination is trivial admit a dual pair of functionals. -/
theorem exists_dual_pair {M : Type*} [AddCommGroup M] [Module ℝ M] {x y : M}
    (hpair : ∀ s t : ℝ, s • x + t • y = 0 → s = 0 ∧ t = 0) :
    ∃ f g : M →ₗ[ℝ] ℝ, f x = 1 ∧ f y = 0 ∧ g x = 0 ∧ g y = 1 := by
  have hli : LinearIndependent ℝ ![x, y] := LinearIndependent.pair_iff.mpr hpair
  let b := Module.Basis.span hli
  obtain ⟨f, hf⟩ := LinearMap.exists_extend (b.coord 0)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (b.coord 1)
  have ev : ∀ (F : M →ₗ[ℝ] ℝ) (i j : Fin 2),
      F ∘ₗ (Submodule.span ℝ (Set.range ![x, y])).subtype = b.coord i →
        F (![x, y] j) = if j = i then 1 else 0 := by
    intro F i j hF
    have hb : ((b j : _) : M) = ![x, y] j := congrArg Subtype.val (Module.Basis.span_apply hli j)
    rw [← hb]
    have := LinearMap.congr_fun hF (b j)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  refine ⟨f, g, ?_, ?_, ?_, ?_⟩
  · simpa using ev f 0 0 hf
  · simpa using ev f 0 1 hf
  · simpa using ev g 1 0 hg
  · simpa using ev g 1 1 hg

omit [FiniteDimensional ℝ V] in
/-- A linear reading of the pencil differentiates along a differentiable coefficient curve. -/
theorem hasDerivAt_reading (P : CubicPair V) (φ : SymmetricCubic V →ₗ[ℝ] ℝ)
    {u : ℝ → ℝ × ℝ} {s : ℝ} {w : ℝ × ℝ} (hu : HasDerivAt u w s) :
    HasDerivAt (fun r => φ (coupling P (u r))) (φ (coupling P w)) s := by
  let ψ : (ℝ × ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (φ ∘ₗ coupling P)
  have hψ := ψ.hasFDerivAt.comp_hasDerivAt s hu
  exact hψ

/-- Along a scalar integral curve, every linear reading of the cubic solves the tensor equation. -/
theorem tensorFlow_of_familyFlow (P : CubicPair V) {lam ε : ℝ}
    (h : HasContractionLaws P lam) {u : ℝ → ℝ × ℝ} {s : ℝ}
    (hu : HasDerivAt u (familyField lam ε (u s)) s) (φ : SymmetricCubic V →ₗ[ℝ] ℝ) :
    HasDerivAt (fun r => φ (coupling P (u r))) (φ (oneLoopBeta ε (coupling P (u s)))) s := by
  rw [oneLoop_restricts_to_familyField P h]
  exact hasDerivAt_reading P φ hu

/-- For independent cubics, a curve of coefficients is a scalar integral curve iff every linear
reading of the corresponding cubic solves the tensor one-loop equation. -/
theorem familyFlow_iff_tensorFlow (P : CubicPair V) {lam ε : ℝ}
    (h : HasContractionLaws P lam)
    (hli : LinearIndependent ℝ ![P.diagonalCubic, P.mixingCubic]) (u : ℝ → ℝ × ℝ) (s : ℝ) :
    HasDerivAt u (familyField lam ε (u s)) s ↔
      ∀ φ : SymmetricCubic V →ₗ[ℝ] ℝ,
        HasDerivAt (fun r => φ (coupling P (u r))) (φ (oneLoopBeta ε (coupling P (u s)))) s := by
  refine ⟨fun hu φ => tensorFlow_of_familyFlow P h hu φ, fun hφ => ?_⟩
  have hpair := LinearIndependent.pair_iff (R := ℝ) (M := SymmetricCubic V) |>.mp hli
  obtain ⟨f, g, hfx, hfy, hgx, hgy⟩ := exists_dual_pair hpair
  have hf : ∀ v, f (coupling P v) = v.1 := by
    intro v
    rw [coupling_apply, map_add, map_smul, map_smul, hfx, hfy, smul_eq_mul, smul_eq_mul]
    ring
  have hg : ∀ v, g (coupling P v) = v.2 := by
    intro v
    rw [coupling_apply, map_add, map_smul, map_smul, hgx, hgy, smul_eq_mul, smul_eq_mul]
    ring
  have h1 := hφ f
  have h2 := hφ g
  rw [oneLoop_restricts_to_familyField P h, hf] at h1
  rw [oneLoop_restricts_to_familyField P h, hg] at h2
  have e1 : (fun r => f (coupling P (u r))) = fun r => (u r).1 := funext fun r => hf (u r)
  have e2 : (fun r => g (coupling P (u r))) = fun r => (u r).2 := funext fun r => hg (u r)
  rw [e1] at h1
  rw [e2] at h2
  exact h1.prodMk h2

/-- Componentwise form: along a scalar integral curve, every coefficient of the cubic solves the
tensor one-loop equation. -/
theorem tensorFlow_apply_of_familyFlow (P : CubicPair V) {lam ε : ℝ}
    (h : HasContractionLaws P lam) {u : ℝ → ℝ × ℝ} {s : ℝ}
    (hu : HasDerivAt u (familyField lam ε (u s)) s) (x y z : V) :
    HasDerivAt (fun r => (coupling P (u r)).apply x y z)
      ((oneLoopBeta ε (coupling P (u s))).apply x y z) s := by
  let φ : SymmetricCubic V →ₗ[ℝ] ℝ :=
    { toFun := fun c => c.apply x y z
      map_add' := fun c d => SymmetricCubic.apply_add c d x y z
      map_smul' := fun r c => SymmetricCubic.apply_smul r c x y z }
  exact tensorFlow_of_familyFlow P h hu φ

end

end ThirteenPlanes
