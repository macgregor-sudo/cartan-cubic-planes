module

public import ThirteenPlanes.Cartan.LieOrthogonalDecomposition
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

set_option backward.privateInPublic true

/-! Conjugacy of compact conjugations by a complex Lie automorphism. -/

namespace ThirteenPlanes.Cartan

open LieAlgebra
open scoped BigOperators TensorProduct

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A conjugate-linear involution of a complex Lie algebra preserving its bracket. -/
structure LieConjugation (G : Type*) [LieRing G] [LieAlgebra ℂ G] where
  toFun : G → G
  add : ∀ x y, toFun (x + y) = toFun x + toFun y
  smul : ∀ (z : ℂ) x, toFun (z • x) = star z • toFun x
  involutive : Function.Involutive toFun
  bracket : ∀ x y, toFun ⁅x,y⁆ = ⁅toFun x,toFun y⁆

namespace LieConjugation

variable {G : Type*} [LieRing G] [LieAlgebra ℂ G]

instance : CoeFun (LieConjugation G) (fun _ => G → G) := ⟨toFun⟩

/-- Compactness is positivity of the negative Killing form paired with the conjugation. -/
def IsCompact (σ : LieConjugation G) : Prop :=
  ∀ x : G, x ≠ 0 → (killingForm ℂ G x (σ x)).re < 0

/-- Composition of two conjugations is a complex-linear Lie automorphism. -/
def product (τ σ : LieConjugation G) : G ≃ₗ⁅ℂ⁆ G where
  toFun x := τ (σ x)
  invFun x := σ (τ x)
  left_inv x := by change σ.toFun (τ.toFun (τ.toFun (σ.toFun x))) = x; rw [τ.involutive, σ.involutive]
  right_inv x := by change τ.toFun (σ.toFun (σ.toFun (τ.toFun x))) = x; rw [σ.involutive, τ.involutive]
  map_add' x y := by rw [σ.add, τ.add]
  map_smul' z x := by change τ (σ (z • x)) = _; rw [σ.smul, τ.smul, star_star]; rfl
  map_lie' := by intro x y; rw [σ.bracket, τ.bracket]

@[simp] theorem product_apply (τ σ : LieConjugation G) (x : G) :
    product τ σ x = τ (σ x) := rfl

@[simp] theorem involutive_apply (σ : LieConjugation G) (x : G) :
    σ (σ x) = x := σ.involutive x

private theorem killing_covariance (τ σ : LieConjugation G)
    (hτ : ∀ x y, killingForm ℂ G (τ x) (τ y) = star (killingForm ℂ G x y))
    (x y : G) : killingForm ℂ G (σ x) (σ y) = star (killingForm ℂ G x y) := by
  have h := killingForm_of_equiv_apply (product τ σ) x y
  simp only [product_apply, hτ] at h
  exact star_injective (by simpa only [star_star] using h)

@[instance_reducible] private def killingInnerCore (τ : LieConjugation G) (hc : τ.IsCompact)
    (hτ : ∀ x y, killingForm ℂ G (τ x) (τ y) = star (killingForm ℂ G x y)) :
    InnerProductSpace.Core ℂ G where
  inner x y := -killingForm ℂ G (τ x) y
  conj_inner_symm x y := by
    change star (-killingForm ℂ G (τ y) x) = -killingForm ℂ G (τ x) y
    rw [star_neg, ← hτ, involutive_apply, LieModule.traceForm_comm]
  re_inner_nonneg x := by
    change 0 ≤ (-killingForm ℂ G (τ x) x).re
    rw [LieModule.traceForm_comm, Complex.neg_re]
    by_cases hx : x = 0
    · simp [hx]
    · exact neg_nonneg.mpr (hc x hx).le
  add_left x y z := by simp [τ.add, add_comm]
  smul_left x y r := by
    change -killingForm ℂ G (τ (r • x)) y = star r * -killingForm ℂ G (τ x) y
    simp [τ.smul, mul_neg]
  definite x hx := by
    change -killingForm ℂ G (τ x) x = 0 at hx
    rw [neg_eq_zero, LieModule.traceForm_comm] at hx
    by_contra hn
    have h := hc x hn
    rw [hx, Complex.zero_re] at h
    exact lt_irrefl _ h

private theorem lie_map_of_basis {ι : Type*} (b : Module.Basis ι ℂ G) (g : G →ₗ[ℂ] G)
    (h : ∀ i j, g ⁅b i,b j⁆ = ⁅g (b i),g (b j)⁆) :
    ∀ x y, g ⁅x,y⁆ = ⁅g x,g y⁆ := by
  let β := (LieAlgebra.ad ℂ G).toLinearMap
  have h' : β.compr₂ g = β.compl₁₂ g g := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    exact h i j
  intro x y
  exact LinearMap.congr_fun (LinearMap.congr_fun h' x) y

private theorem diagonal_maps_on_eigenvector {ι : Type*} [DecidableEq ι]
    (b : Module.Basis ι ℂ G) (A g : G →ₗ[ℂ] G) (a : ι → ℝ) (f : ℝ → ℝ)
    (hA : ∀ i, A (b i) = (a i : ℂ) • b i)
    (hg : ∀ i, g (b i) = (f (a i) : ℂ) • b i)
    (x : G) (r : ℝ) (hx : A x = (r : ℂ) • x) :
    g x = (f r : ℂ) • x := by
  have hc (i : ι) (T : G →ₗ[ℂ] G) (d : ι → ℝ)
      (hT : ∀ j, T (b j) = (d j : ℂ) • b j) :
      (b.coord i).comp T = (d i : ℂ) • b.coord i := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, hT, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      rfl
    · rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hij]
      simp
  apply b.repr.injective
  ext i
  have hi := LinearMap.congr_fun (hc i g (f ∘ a) hg) x
  change b.repr (g x) i = (f (a i) : ℂ) * b.repr x i at hi
  have ha := LinearMap.congr_fun (hc i A a hA) x
  rw [LinearMap.comp_apply, hx, map_smul] at ha
  change (r : ℂ) * b.repr x i = (a i : ℂ) * b.repr x i at ha
  rw [map_smul, Finsupp.smul_apply]
  change b.repr (g x) i = (f r : ℂ) * b.repr x i
  rw [hi]
  by_cases hzero : b.repr x i = 0
  · simp [hzero]
  · have heq := mul_right_cancel₀ hzero ha
    exact congrArg (fun t : ℝ => (f t : ℂ) * b.repr x i) (Complex.ofReal_injective heq).symm

set_option maxRecDepth 1000 in
/-- Two compact conjugations are conjugate by a complex-linear Lie automorphism.
The automorphism is the positive square root of their product. -/
theorem exists_intertwining_aut [Module.Finite ℂ G] (τ σ : LieConjugation G)
    (ht : τ.IsCompact) (hs : σ.IsCompact)
    (hτ : ∀ x y, killingForm ℂ G (τ x) (τ y) = star (killingForm ℂ G x y)) :
    ∃ e : G ≃ₗ⁅ℂ⁆ G, ∀ x, e (σ x) = τ (e x) := by
  classical
  have hh := killing_covariance τ σ hτ
  let core := killingInnerCore τ ht hτ
  let : InnerProductSpace.Core ℂ G := core
  let : NormedAddCommGroup G := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ G := InnerProductSpace.ofCore (𝕜 := ℂ) (F := G) inferInstance
  let A := (product τ σ).toLinearMap
  have hA : A.IsSymmetric := by
    intro x y
    change -killingForm ℂ G (τ (τ (σ x))) y = -killingForm ℂ G (τ x) (τ (σ y))
    rw [involutive_apply, hτ, ← hh, involutive_apply]
  let n := Module.finrank ℂ G
  let b := (hA.eigenvectorBasis (n := n) rfl).toBasis
  let a := hA.eigenvalues (n := n) rfl
  have hAb (i : Fin n) : A (b i) = (a i : ℂ) • b i := hA.apply_eigenvectorBasis rfl i
  have ha (i : Fin n) : 0 < a i := by
    have hval : inner ℂ (b i) (A (b i)) = (a i : ℂ) := by
      rw [hAb, inner_smul_right]
      have hb : inner ℂ (b i) (b i) = 1 :=
        (orthonormal_iff_ite.mp (hA.eigenvectorBasis (n := n) rfl).orthonormal i i).trans
          (ite_eq_left rfl)
      rw [hb, mul_one]
    have hval' : inner ℂ (b i) (A (b i)) = -star (killingForm ℂ G (b i) (σ (b i))) := by
      change -killingForm ℂ G (τ (b i)) (τ (σ (b i))) = _
      rw [hτ]
    have he := congrArg Complex.re (hval.symm.trans hval')
    have hp := hs (b i) (b.ne_zero i)
    change a i = -(killingForm ℂ G (b i) (σ (b i))).re at he
    linarith
  let g : G →ₗ[ℂ] G := b.constr ℂ (fun i => (Real.sqrt (a i) : ℂ) • b i)
  let gi : G →ₗ[ℂ] G := b.constr ℂ (fun i => (((Real.sqrt (a i))⁻¹ : ℝ) : ℂ) • b i)
  have hgb (i : Fin n) : g (b i) = (Real.sqrt (a i) : ℂ) • b i :=
    b.constr_basis ℂ _ i
  have hgib (i : Fin n) : gi (b i) = (((Real.sqrt (a i))⁻¹ : ℝ) : ℂ) • b i :=
    b.constr_basis ℂ _ i
  have hgi : gi.comp g = LinearMap.id := by
    apply b.ext
    intro i
    rw [LinearMap.comp_apply, hgb, map_smul, hgib, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (Real.sqrt_pos.2 (ha i)).ne', Complex.ofReal_one, one_smul]
    rfl
  have hig : g.comp gi = LinearMap.id := by
    apply b.ext
    intro i
    rw [LinearMap.comp_apply, hgib, map_smul, hgb, smul_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (Real.sqrt_pos.2 (ha i)).ne', Complex.ofReal_one, one_smul]
    rfl
  have geigen := diagonal_maps_on_eigenvector b A g a Real.sqrt hAb hgb
  have hglie : ∀ x y, g ⁅x,y⁆ = ⁅g x,g y⁆ := by
    apply lie_map_of_basis b
    intro i j
    have hp : A ⁅b i,b j⁆ = ((a i * a j : ℝ) : ℂ) • ⁅b i,b j⁆ := by
      change product τ σ ⁅b i,b j⁆ = _
      rw [LieEquiv.map_lie]
      change ⁅A (b i),A (b j)⁆ = _
      rw [hAb, hAb, smul_lie, lie_smul, smul_smul, Complex.ofReal_mul]
    rw [geigen _ _ hp, hgb, hgb, smul_lie, lie_smul, smul_smul,
      Real.sqrt_mul (ha i).le, Complex.ofReal_mul]
  let e : G ≃ₗ⁅ℂ⁆ G :=
    { (LinearEquiv.ofBijective g
        ⟨fun x y h => by
          have hx := LinearMap.congr_fun hgi x
          have hy := LinearMap.congr_fun hgi y
          change gi (g x) = x at hx
          change gi (g y) = y at hy
          rw [h] at hx
          exact hx.symm.trans hy,
        fun x => ⟨gi x, LinearMap.congr_fun hig x⟩⟩) with map_lie' := fun {x y} => hglie x y }
  have hstar (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
    apply Complex.ext <;> simp
  have hinter : ∀ i, g (σ (b i)) = τ (g (b i)) := by
    intro i
    have hσ : σ (b i) = (a i : ℂ) • τ (b i) := by
      have h := congrArg τ.toFun (hAb i)
      change τ (τ (σ (b i))) = τ ((a i : ℂ) • b i) at h
      simpa only [involutive_apply, τ.smul, hstar] using h
    have hτ' : A (τ (b i)) = (((a i)⁻¹ : ℝ) : ℂ) • τ (b i) := by
      have h : A (σ (b i)) = τ (b i) := by change τ (σ (σ (b i))) = _; simp
      rw [hσ, map_smul] at h
      calc
        A (τ (b i)) = (((a i)⁻¹ : ℝ) : ℂ) • ((a i : ℂ) • A (τ (b i))) := by
          rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ha i).ne',
            Complex.ofReal_one, one_smul]
        _ = _ := by rw [h]
    rw [hσ, map_smul, geigen _ _ hτ', hgb, τ.smul, hstar, smul_smul,
      ← Complex.ofReal_mul, Real.sqrt_inv]
    congr 2
    have hpos : Real.sqrt (a i) ≠ 0 := (Real.sqrt_pos.2 (ha i)).ne'
    apply (mul_right_cancel₀ hpos)
    rw [mul_assoc, inv_mul_cancel₀ hpos, mul_one, Real.mul_self_sqrt (ha i).le]
  let f : G →ₗ[ℂ] G :=
    { toFun := fun x => τ (g (σ x))
      map_add' := fun x y => by rw [σ.add, map_add, τ.add]
      map_smul' := fun c x => by rw [σ.smul, map_smul, τ.smul, star_star]; rfl }
  have hf : f = g := by
    apply b.ext
    intro i
    change τ (g (σ (b i))) = g (b i)
    rw [hinter, involutive_apply]
  refine ⟨e, fun x => ?_⟩
  have hg := LinearMap.congr_fun hf x
  change τ (g (σ x)) = g x at hg
  have h := congrArg τ.toFun hg
  change τ (τ (g (σ x))) = τ (g x) at h
  change g (σ x) = τ (g x)
  simpa only [involutive_apply] using h

/-- Transport a complex Lie conjugation along a complex-linear Lie equivalence. -/
def transport {H : Type*} [LieRing H] [LieAlgebra ℂ H] (e : G ≃ₗ⁅ℂ⁆ H)
    (σ : LieConjugation G) : LieConjugation H where
  toFun x := e (σ (e.symm x))
  add x y := by rw [map_add, σ.add, map_add]
  smul z x := by rw [map_smul, σ.smul, map_smul]
  involutive x := by
    change e (σ (e.symm (e (σ (e.symm x))))) = x
    rw [LieEquiv.symm_apply_apply, involutive_apply, LieEquiv.apply_symm_apply]
  bracket x y := by rw [LieEquiv.map_lie, σ.bracket, LieEquiv.map_lie]

@[simp] theorem transport_apply {H : Type*} [LieRing H] [LieAlgebra ℂ H]
    (e : G ≃ₗ⁅ℂ⁆ H) (σ : LieConjugation G) (x : H) :
    transport e σ x = e (σ (e.symm x)) := rfl

theorem transport_compact {H : Type*} [LieRing H] [LieAlgebra ℂ H]
    (e : G ≃ₗ⁅ℂ⁆ H) (σ : LieConjugation G) (hs : σ.IsCompact) :
    (transport e σ).IsCompact := by
  intro x hx
  have he : e.symm x ≠ 0 := fun hz => hx (e.symm.injective (hz.trans (map_zero e.symm).symm))
  have h := hs (e.symm x) he
  rw [← killingForm_of_equiv_apply e, LieEquiv.apply_symm_apply] at h
  exact h

end LieConjugation

namespace LieComplex

variable {K : Type*} [LieRing K] [LieAlgebra ℝ K]

/-- Conjugation on the complex scalar in the tensor-product model. -/
def compactConjugation : LieConjugation (LieComplex K) where
  toFun := conjugation
  add := map_add conjugation
  smul z x := by
    induction x using TensorProduct.inductionOn with
    | tmul w y => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp [smul_add, map_add, hx, hy]
  involutive := conjugation_involutive
  bracket := conjugation.map_lie

@[simp] theorem compactConjugation_apply (x : LieComplex K) :
    compactConjugation x = conjugation x := rfl

theorem compactConjugation_isCompact [Module.Finite ℝ K] (hK : CompactKilling K) :
    (compactConjugation : LieConjugation (LieComplex K)).IsCompact :=
  fun _ hx => killing_conjugation_negative hK hx

theorem killing_conjugation_conjugation [Module.Finite ℝ K] (x y : LieComplex K) :
    killingForm ℂ (LieComplex K) (compactConjugation x) (compactConjugation y) =
      star (killingForm ℂ (LieComplex K) x y) := by
  have h : killingForm ℂ (LieComplex K) x y =
      (killingForm ℝ K (realPart x) (realPart y) : ℂ) -
      (killingForm ℝ K (imagPart x) (imagPart y) : ℂ) +
        Complex.I * ((killingForm ℝ K (realPart x) (imagPart y) : ℂ) +
          (killingForm ℝ K (imagPart x) (realPart y) : ℂ)) := by
    conv_lhs => rw [← decompose_smul x, ← decompose_smul y]
    exact killing_parts _ _ _ _
  rw [h, compactConjugation_apply, compactConjugation_apply, conjugation_decompose,
    conjugation_decompose, sub_eq_add_neg, sub_eq_add_neg, ← smul_neg, ← smul_neg,
    ← map_neg ofReal, ← map_neg ofReal, killing_parts]
  apply Complex.ext
  · simp
  · simp; ring

end LieComplex

variable {𝕜 G H ι : Type*} [Field 𝕜] [LieRing G] [LieAlgebra 𝕜 G]
  [LieRing H] [LieAlgebra 𝕜 H] [DecidableEq ι]

/-- A Lie equivalence preserves the Cartan property, the Killing form and internal summation. -/
theorem killingCartanOD_map (e : G ≃ₗ⁅𝕜⁆ H) (T : ι → LieSubalgebra 𝕜 G) (hT : IsKillingCartanOD T) :
    IsKillingCartanOD (fun i => (T i).map e.toLieHom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    let R := (T i).map e.toLieHom
    let f := (T i).equivMapOfInjective e.toLieHom e.injective
    refine ⟨f.nilpotent_iff_equiv_nilpotent.mp (hT.1 i).nilpotent, le_antisymm ?_ R.le_normalizer⟩
    intro y hy
    obtain ⟨x,rfl⟩ := e.surjective y
    apply (LieSubalgebra.mem_map _ _ _).mpr
    refine ⟨x, ?_, rfl⟩
    rw [← (hT.1 i).self_normalizing, LieSubalgebra.mem_normalizer_iff]
    intro z hz
    have hz' : e z ∈ R := (LieSubalgebra.mem_map _ _ _).mpr ⟨z,hz,rfl⟩
    have he := (R.mem_normalizer_iff _).mp hy (e z) hz'
    change ⁅e x, e z⁆ ∈ R at he
    rw [← LieEquiv.map_lie] at he
    obtain ⟨w,hw,heq⟩ := (LieSubalgebra.mem_map _ _ _).mp he
    exact (e.injective heq) ▸ hw
  · intro i j hij _ hx _ hy
    obtain ⟨x,hxT,rfl⟩ := (LieSubalgebra.mem_map _ _ _).mp hx
    obtain ⟨y,hyT,rfl⟩ := (LieSubalgebra.mem_map _ _ _).mp hy
    change killingForm 𝕜 H (e x) (e y) = 0
    rw [killingForm_of_equiv_apply]
    exact hT.2.1 hij x hxT y hyT
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact e.toLinearMap.iSupIndep_map e.injective hT.2.2.submodule_iSupIndep
    · change (⨆ i, (T i).toSubmodule.map e.toLinearMap) = ⊤
      rw [← Submodule.map_iSup, hT.2.2.submodule_iSup_eq_top, Submodule.map_top,
        LinearMap.range_eq_top.mpr e.surjective]

/-- An intertwiner carries the same permutation of an indexed family to the transported family. -/
theorem conjugation_permutes_map {G H ι : Type*} [LieRing G] [LieAlgebra ℂ G]
    [LieRing H] [LieAlgebra ℂ H] (e : G ≃ₗ⁅ℂ⁆ H) (σ : LieConjugation G) (τ : LieConjugation H)
    (he : ∀ x, e (σ x) = τ (e x)) (T : ι → LieSubalgebra ℂ G) (π : Equiv.Perm ι)
    (hπ : ∀ i, σ '' (T i : Set G) = T (π i)) :
    ∀ i, τ '' ((T i).map e.toLieHom : Set H) = (T (π i)).map e.toLieHom := by
  intro i
  change τ '' (e '' (T i : Set G)) = e '' (T (π i) : Set G)
  rw [Set.image_image, ← hπ i, Set.image_image]
  exact congrArg (fun f : G → H => f '' (T i : Set G)) (funext fun x => (he x).symm)

end
end ThirteenPlanes.Cartan
