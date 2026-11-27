module

public import ThirteenPlanes.FieldDefect.Statements
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-! Coefficient coordinates on `𝒲_m` for radial field defect (i).

A real trilinear form on `ℂ³` is fixed by its eight values on the real basis `{1, i}`; the space
`𝒯` of families `(T_{ijk})_{i<j<k}` is identified with `Triple m → (Fin 3 → Fin 2) → ℝ`, and
`T ↦ W_T` with `c ↦ coefCubic c`. This file proves `cubicClass m = range coefCubic`, joint
smoothness in `(c, z)`, cubic homogeneity, Euler's identity and the evaluation of the coupling part
at the points with entries in `{1, i}` on one triple. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading.Defect

open Complex

variable {m : ℕ}

/-- The real basis `1, i` of `ℂ`. -/
def eb : Fin 2 → ℂ := ![1, I]

/-- Its coordinate functionals `Re, Im`. -/
def fb : Fin 2 → (ℂ →ₗ[ℝ] ℝ) := ![reLm, imLm]

lemma fb_eb (α β : Fin 2) : fb α (eb β) = if α = β then 1 else 0 := by
  fin_cases α <;> fin_cases β <;> simp [fb, eb]

lemma sum_fb_smul_eb (a : ℂ) : ∑ α, fb α a • eb α = a := by
  simp [fb, eb, Fin.sum_univ_two]

/-- Coefficient space of the couplings. -/
abbrev Coef (m : ℕ) := Triple m → (Fin 3 → Fin 2) → ℝ

/-- The monomial `∏ᵢ f_{rᵢ}(vᵢ)`. -/
def mono (r : Fin 3 → Fin 2) (v : Fin 3 → ℂ) : ℝ := fb (r 0) (v 0) * fb (r 1) (v 1) * fb (r 2) (v 2)

/-- `W_c(z) = ∑ᵢ Re zᵢ³ + ∑_{t} ∑_r c_{t,r} ∏ f_{rᵢ}(z_{tᵢ})`. -/
def coefCubic (c : Coef m) (z : Field m) : ℝ :=
  diagonalCubic z + ∑ t : Triple m, ∑ r : Fin 3 → Fin 2, c t r * mono r (fun a => z (t.1 a))

/-- Coefficients of a trilinear form. -/
def coefOf (T : TriForm) (r : Fin 3 → Fin 2) : ℝ := T fun i => eb (r i)

lemma triForm_expand (T : TriForm) (v : Fin 3 → ℂ) :
    T v = ∑ r : Fin 3 → Fin 2, coefOf T r * mono r v := by
  have hv : v = fun i => ∑ α, fb α (v i) • eb α := funext fun i => (sum_fb_smul_eb (v i)).symm
  conv_lhs => rw [hv, MultilinearMap.map_sum]
  refine Finset.sum_congr (by simp) fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, Fin.prod_univ_three, smul_eq_mul, coefOf, mono]
  simp only [RingHom.id_apply]
  ring

lemma fieldCubic_eq_coefCubic (T : Triple m → TriForm) :
    fieldCubic T = coefCubic (fun t => coefOf (T t)) := by
  funext z
  simp only [fieldCubic, coefCubic, triForm_expand]

/-- The trilinear form `v ↦ ∏ᵢ f_{rᵢ}(vᵢ)`. -/
def monoForm (r : Fin 3 → Fin 2) : TriForm :=
  (MultilinearMap.mkPiAlgebra ℝ (Fin 3) ℝ).compLinearMap fun i => fb (r i)

lemma monoForm_apply (r : Fin 3 → Fin 2) (v : Fin 3 → ℂ) : monoForm r v = mono r v := by
  simp [monoForm, mono, Fin.prod_univ_three]

lemma coefCubic_eq_fieldCubic (c : Coef m) :
    coefCubic c = fieldCubic (fun t => ∑ r, c t r • monoForm r) := by
  funext z
  simp [fieldCubic, coefCubic, monoForm_apply]

lemma cubicClass_eq_range : cubicClass m = Set.range (coefCubic (m := m)) := by
  ext W
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨_, (fieldCubic_eq_coefCubic T).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, coefCubic_eq_fieldCubic c⟩

/-! ### Smoothness -/

lemma contDiff_coord (i : Fin m) : ContDiff ℝ 1 fun z : Field m => z i :=
  ((EuclideanSpace.proj i : Field m →L[ℂ] ℂ).restrictScalars ℝ).contDiff

lemma contDiff_coefCubic_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → Coef m} {b : X → Field m} (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 fun x => coefCubic (a x) (b x) := by
  unfold coefCubic diagonalCubic mono
  have hz : ∀ i : Fin m, ContDiff ℝ 1 fun x => b x i := fun i => (contDiff_coord i).comp hb
  have hf : ∀ (α : Fin 2) (i : Fin m), ContDiff ℝ 1 fun x => fb α (b x i) :=
    fun α i => (LinearMap.toContinuousLinearMap (fb α)).contDiff.comp (hz i)
  have hc : ∀ (t : Triple m) (r : Fin 3 → Fin 2), ContDiff ℝ 1 fun x => a x t r := fun t r =>
    contDiff_pi.mp (contDiff_pi.mp ha t) r
  refine ContDiff.add ?_ ?_
  · exact ContDiff.sum fun i _ => reCLM.contDiff.comp ((hz i).pow 3)
  · refine ContDiff.sum fun t _ => ContDiff.sum fun r _ => ?_
    exact (hc t r).mul (((hf _ _).mul (hf _ _)).mul (hf _ _))

lemma contDiff_coefCubic (c : Coef m) : ContDiff ℝ 1 (coefCubic c) :=
  contDiff_coefCubic_comp (a := fun _ : Field m => c) contDiff_const contDiff_id

lemma continuous_fderiv_coefCubic :
    Continuous fun p : Coef m × Field m => fderiv ℝ (coefCubic p.1) p.2 := by
  have hu : ContDiff ℝ 1 (Function.uncurry fun (p : Coef m × Field m) (y : Field m) =>
      coefCubic p.1 y) :=
    contDiff_coefCubic_comp (a := fun q : (Coef m × Field m) × Field m => q.1.1)
      (b := fun q => q.2) contDiff_fst.fst contDiff_snd
  have h := ContDiff.fderiv (𝕜 := ℝ) (n := 0)
    (f := fun (p : Coef m × Field m) (y : Field m) => coefCubic p.1 y) (g := Prod.snd)
    hu contDiff_snd (by simp)
  exact h.continuous

/-! ### Homogeneity and Euler -/

lemma coefCubic_smul (c : Coef m) (s : ℝ) (z : Field m) :
    coefCubic c (s • z) = s ^ 3 * coefCubic c z := by
  have hz : ∀ i, (s • z) i = (s : ℂ) * z i := fun i => by
    rw [PiLp.smul_apply, Complex.real_smul]
  have hf : ∀ α i, fb α ((s • z) i) = s * fb α (z i) := fun α i => by
    rw [PiLp.smul_apply, LinearMap.map_smul, smul_eq_mul]
  have hd : ∀ i, (((s • z) i) ^ 3).re = s ^ 3 * ((z i) ^ 3).re := fun i => by
    rw [hz, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  simp only [coefCubic, diagonalCubic, mono, hd, hf, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun r _ => ?_
  ring

/-- Euler's identity for a differentiable cubic form: `dW(z)[z] = 3 W(z)`. -/
lemma euler {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : E → ℝ)
    (hW : Differentiable ℝ W) (hhom : ∀ (s : ℝ) z, W (s • z) = s ^ 3 * W z) (z : E) :
    fderiv ℝ W z z = 3 * W z := by
  have h1 : HasDerivAt (fun s : ℝ => W (s • z)) (fderiv ℝ W z z) 1 := by
    have hs : HasDerivAt (fun s : ℝ => s • z) ((1 : ℝ) • z) 1 := (hasDerivAt_id 1).smul_const z
    rw [one_smul] at hs
    have hl : HasFDerivAt W (fderiv ℝ W z) ((fun s : ℝ => s • z) 1) := by
      simp only [one_smul]; exact (hW z).hasFDerivAt
    exact hl.comp_hasDerivAt (x := (1 : ℝ)) hs
  have h2 : HasDerivAt (fun s : ℝ => s ^ 3 * W z) (3 * W z) 1 := by
    have := ((hasDerivAt_pow 3 (1 : ℝ)).mul_const (W z))
    simpa using this
  have heq : (fun s : ℝ => W (s • z)) = fun s => s ^ 3 * W z := funext fun s => hhom s z
  rw [heq] at h1
  exact h1.unique h2

/-- The derivative of a cubic form is homogeneous of degree two. -/
lemma fderiv_smul_hom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : E → ℝ)
    (hW : Differentiable ℝ W) (hhom : ∀ (s : ℝ) z, W (s • z) = s ^ 3 * W z) (s : ℝ)
    (hs : s ≠ 0) (z : E) : fderiv ℝ W (s • z) = s ^ 2 • fderiv ℝ W z := by
  have h1 : HasFDerivAt (fun y => W (s • y)) ((fderiv ℝ W (s • z)).comp (s • ContinuousLinearMap.id ℝ E)) z :=
    (hW (s • z)).hasFDerivAt.comp z ((ContinuousLinearMap.id ℝ E).hasFDerivAt.const_smul s)
  have h2 : HasFDerivAt (fun y => s ^ 3 * W y) (s ^ 3 • fderiv ℝ W z) z :=
    (hW z).hasFDerivAt.const_mul (s ^ 3)
  have heq : (fun y => W (s • y)) = fun y => s ^ 3 * W y := funext fun y => hhom s y
  rw [heq] at h1
  have hu := h1.unique h2
  ext v
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hu
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, map_smul] at hv
  simp only [smul_apply, smul_eq_mul]
  have : s * (fderiv ℝ W (s • z) v - s ^ 2 * fderiv ℝ W z v) = 0 := by rw [mul_sub]; nlinarith [hv]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hs
  · linarith

/-! ### Evaluation on one triple -/

/-- The point with entries `e_{r₀}, e_{r₁}, e_{r₂}` in positions `t₀, t₁, t₂`. -/
def tPoint (t : Triple m) (r : Fin 3 → Fin 2) : Field m :=
  WithLp.toLp 2 fun k => ∑ i : Fin 3, if k = t.1 i then eb (r i) else 0

lemma triple_inj (t : Triple m) : Function.Injective t.1 := by
  obtain ⟨t, h1, h2⟩ := t
  intro a b hab
  simp only [Fin.lt_def] at h1 h2
  fin_cases a <;> fin_cases b <;> simp_all [Fin.ext_iff] <;> omega

lemma tPoint_apply_self (t : Triple m) (r : Fin 3 → Fin 2) (i : Fin 3) :
    tPoint t r (t.1 i) = eb (r i) := by
  simp only [tPoint, PiLp.toLp_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [ite_eq_right_iff]
    exact fun h => absurd ((triple_inj t) h).symm hj
  · simp

lemma tPoint_apply_out (t : Triple m) (r : Fin 3 → Fin 2) (k : Fin m) (hk : ∀ j, t.1 j ≠ k) :
    tPoint t r k = 0 := by
  simp only [tPoint, PiLp.toLp_apply]
  exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right_iff]; exact fun h => absurd h.symm (hk j)

lemma triple_out (t t' : Triple m) (h : t' ≠ t) : ∃ i, ∀ j, t.1 j ≠ t'.1 i := by
  by_contra hc
  push Not at hc
  apply h
  obtain ⟨j0, h0⟩ := hc 0
  obtain ⟨j1, h1⟩ := hc 1
  obtain ⟨j2, h2⟩ := hc 2
  obtain ⟨t, ht1, ht2⟩ := t
  obtain ⟨u, hu1, hu2⟩ := t'
  apply Subtype.ext
  simp only [Fin.lt_def] at ht1 ht2 hu1 hu2
  simp only [Fin.ext_iff] at h0 h1 h2
  funext i
  rw [Fin.ext_iff]
  fin_cases j0 <;> fin_cases j1 <;> fin_cases j2 <;> fin_cases i <;> simp_all <;> omega

lemma mono_tPoint_self (t : Triple m) (r r' : Fin 3 → Fin 2) :
    mono r' (fun a => tPoint t r (t.1 a)) = if r' = r then 1 else 0 := by
  simp only [mono, tPoint_apply_self, fb_eb]
  by_cases h : r' = r
  · subst h; simp
  · simp only [h, ↓reduceIte]
    have : ∃ i, r' i ≠ r i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    obtain ⟨i, hi⟩ := this
    fin_cases i <;> simp_all

lemma mono_eq_zero_of {r : Fin 3 → Fin 2} (v : Fin 3 → ℂ) (i : Fin 3) (hv : v i = 0) :
    mono r v = 0 := by
  fin_cases i <;> simp_all [mono]

lemma coupling_tPoint (c : Coef m) (t : Triple m) (r : Fin 3 → Fin 2) :
    ∑ t' : Triple m, ∑ r' : Fin 3 → Fin 2, c t' r' * mono r' (fun a => tPoint t r (t'.1 a)) =
      c t r := by
  rw [Finset.sum_eq_single t]
  · simp only [mono_tPoint_self, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  · intro t' _ ht'
    obtain ⟨i, hi⟩ := triple_out t t' ht'
    refine Finset.sum_eq_zero fun r' _ => ?_
    have h0 : tPoint t r (t'.1 i) = 0 := tPoint_apply_out t r _ hi
    rw [mono_eq_zero_of (fun a => tPoint t r (t'.1 a)) i h0, mul_zero]
  · simp

lemma coefCubic_tPoint (c : Coef m) (t : Triple m) (r : Fin 3 → Fin 2) :
    c t r = coefCubic c (tPoint t r) - diagonalCubic (tPoint t r) := by
  rw [coefCubic, coupling_tPoint]
  ring

end ThirteenPlanes.AlbertGrading.Defect

end
