module

public import ThirteenPlanes.AlbertGrading.Contrast.HermTrace
public import ThirteenPlanes.AlbertGrading.Contrast.WeylFrames

@[expose] public section

/-!
# Transporting a complexified qutrit to `M₃(ℂ)`

For a Jordan isomorphism `E : Herm₃(ℂ) → Q ⊆ J` and a unitary `U`, the map
`x ↦ U E⁻¹(x) U*` on `Q`, extended complex-linearly to `Q_ℂ ⊆ J_ℂ`, is injective and carries the
Jordan product of `J_ℂ` to `½(AB+BA)` and the conjugation of `J_ℂ` to `A ↦ A*`. A linear left
inverse `g` of the inclusion `Q ⊆ J` extends the map to all of `J_ℂ`; only its values on `Q_ℂ`
are used.
-/

open scoped Matrix

namespace ThirteenPlanes.AlbertGrading.Contrast

noncomputable section

open Graded AlbertC

/-- Elements of `Q_ℂ = Q + i Q`. -/
def InQ (Q : Submodule ℝ Glennie.Albert) (z : AlbertC) : Prop := z.re ∈ Q ∧ z.im ∈ Q

section InQ

variable {Q : Submodule ℝ Glennie.Albert}

theorem InQ.add {z w : AlbertC} (hz : InQ Q z) (hw : InQ Q w) : InQ Q (z + w) :=
  ⟨Q.add_mem hz.1 hw.1, Q.add_mem hz.2 hw.2⟩

theorem InQ.sub {z w : AlbertC} (hz : InQ Q z) (hw : InQ Q w) : InQ Q (z - w) :=
  ⟨Q.sub_mem hz.1 hw.1, Q.sub_mem hz.2 hw.2⟩

theorem InQ.smul (c : ℂ) {z : AlbertC} (hz : InQ Q z) : InQ Q (c • z) :=
  ⟨Q.sub_mem (Q.smul_mem _ hz.1) (Q.smul_mem _ hz.2),
    Q.add_mem (Q.smul_mem _ hz.2) (Q.smul_mem _ hz.1)⟩

theorem InQ.conj {z : AlbertC} (hz : InQ Q z) : InQ Q (AlbertC.conj z) :=
  ⟨hz.1, Q.neg_mem hz.2⟩

theorem InQ.ofReal {x : Glennie.Albert} (hx : x ∈ Q) : InQ Q (AlbertC.ofReal x) :=
  ⟨hx, Q.zero_mem⟩

theorem InQ.jordan (hQ : ∀ x y, x ∈ Q → y ∈ Q → Glennie.jordan x y ∈ Q) {z w : AlbertC}
    (hz : InQ Q z) (hw : InQ Q w) : InQ Q (AlbertC.jordan z w) :=
  ⟨Q.sub_mem (hQ _ _ hz.1 hw.1) (hQ _ _ hz.2 hw.2),
    Q.add_mem (hQ _ _ hz.1 hw.2) (hQ _ _ hz.2 hw.1)⟩

theorem InQ.of_contrast {p : Fin 3 → Glennie.Albert} (hp : ∀ a, p a ∈ Q) : InQ Q (contrast p) := by
  refine ⟨?_, ?_⟩
  · rw [contrast, frame_sum_re]
    exact Q.sum_mem fun a _ => Q.smul_mem _ (hp a)
  · rw [contrast, frame_sum_im]
    exact Q.sum_mem fun a _ => Q.smul_mem _ (hp a)

end InQ

/-- Conjugation by `U`, as a real-linear map. -/
def conjU (U : ComplexMatrix3) : ComplexMatrix3 →ₗ[ℝ] ComplexMatrix3 where
  toFun M := U * M * star U
  map_add' M N := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' r M := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem real_smul_zmat (r : ℝ) (A : ZMat) : r • A = (r : ℂ) • A := by
  ext i j
  simp [Complex.real_smul]

theorem symm_jordan {Q : Submodule ℝ Glennie.Albert} (E : FullHermitian3 ≃ₗ[ℝ] Q)
    (hE : ∀ X Y, (E (fullHermitianProduct X Y)).val = Glennie.jordan (E X).val (E Y).val)
    {x y : Glennie.Albert} (hx : x ∈ Q) (hy : y ∈ Q) (hxy : Glennie.jordan x y ∈ Q) :
    E.symm ⟨Glennie.jordan x y, hxy⟩ = fullHermitianProduct (E.symm ⟨x, hx⟩) (E.symm ⟨y, hy⟩) := by
  apply E.injective
  apply Subtype.ext
  rw [LinearEquiv.apply_symm_apply, hE, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

section Transport

variable {Q : Submodule ℝ Glennie.Albert} (E : FullHermitian3 ≃ₗ[ℝ] Q) (U : ComplexMatrix3)
  (g : Glennie.Albert →ₗ[ℝ] Q)

/-- `x ↦ U E⁻¹(g x) U*`, read with `𝔽₃` indices. -/
def transR (x : Glennie.Albert) : ZMat :=
  zIdx (conjU U ((E.symm (g x)).val))

/-- Its complex-linear extension to `J_ℂ`. -/
def transC (z : AlbertC) : ZMat := transR E U g z.re + Complex.I • transR E U g z.im

theorem transR_add (x y : Glennie.Albert) : transR E U g (x + y) = transR E U g x + transR E U g y := by
  simp [transR, zIdx_add]

theorem transR_smul (r : ℝ) (x : Glennie.Albert) : transR E U g (r • x) = (r : ℂ) • transR E U g x := by
  rw [← real_smul_zmat]
  simp [transR]
  rfl

theorem transR_neg (x : Glennie.Albert) : transR E U g (-x) = -transR E U g x := by
  rw [show -x = (-1 : ℝ) • x by simp, transR_smul]; simp

theorem transR_sub (x y : Glennie.Albert) : transR E U g (x - y) = transR E U g x - transR E U g y := by
  rw [sub_eq_add_neg, transR_add, transR_neg, ← sub_eq_add_neg]

theorem transR_zero : transR E U g 0 = 0 := by simp [transR]; rfl

theorem transC_add (z w : AlbertC) : transC E U g (z + w) = transC E U g z + transC E U g w := by
  simp only [transC, add_re, add_im, transR_add, smul_add]; abel

theorem transC_zero : transC E U g 0 = 0 := by simp [transC, transR_zero]

theorem transC_smul (c : ℂ) (z : AlbertC) : transC E U g (c • z) = c • transC E U g z := by
  simp only [transC, smul_re, smul_im, transR_sub, transR_add, transR_smul]
  conv_rhs => rw [← Complex.re_add_im c]
  linear_combination (norm := module) (-(c.im : ℂ) * Complex.I_sq) • transR E U g z.im

theorem transC_sub (z w : AlbertC) : transC E U g (z - w) = transC E U g z - transC E U g w := by
  simp only [transC, sub_re, sub_im, transR_sub, smul_sub]; abel

theorem transC_ofReal (x : Glennie.Albert) : transC E U g (AlbertC.ofReal x) = transR E U g x := by
  simp [transC, transR_zero]

theorem transC_sum {ι : Type*} (s : Finset ι) (f : ι → AlbertC) :
    transC E U g (∑ i ∈ s, f i) = ∑ i ∈ s, transC E U g (f i) :=
  map_sum (⟨⟨transC E U g, transC_zero E U g⟩, transC_add E U g⟩ : AlbertC →+ ZMat) f s

variable (hg : ∀ q : Q, g q = q)
include hg

theorem transR_mem {x : Glennie.Albert} (hx : x ∈ Q) :
    transR E U g x = zIdx (U * (E.symm ⟨x, hx⟩).val * star U) := by
  simp only [transR, conjU, LinearMap.coe_mk, AddHom.coe_mk]
  rw [show g x = ⟨x, hx⟩ from hg ⟨x, hx⟩]

theorem transR_herm {x : Glennie.Albert} (hx : x ∈ Q) : (transR E U g x)ᴴ = transR E U g x := by
  rw [transR_mem E U g hg hx, ← zIdx_conjTranspose, Matrix.star_eq_conjTranspose]
  exact congrArg zIdx (Matrix.isHermitian_mul_mul_conjTranspose U (E.symm ⟨x, hx⟩).2)

theorem transC_conj {z : AlbertC} (hz : InQ Q z) :
    transC E U g (AlbertC.conj z) = (transC E U g z)ᴴ := by
  simp only [transC, conj_re, conj_im, transR_neg, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, transR_herm E U g hg hz.1, transR_herm E U g hg hz.2]
  rw [Complex.star_def, Complex.conj_I]
  module

variable (hU : star U * U = 1)
include hU

theorem transR_injective {x : Glennie.Albert} (hx : x ∈ Q) (h : transR E U g x = 0) : x = 0 := by
  rw [transR_mem E U g hg hx] at h
  have h' : U * (E.symm ⟨x, hx⟩).val * star U = 0 := h
  have h'' : (E.symm ⟨x, hx⟩).val = 0 := by
    have := congrArg (fun M => star U * M * U) h'
    simp only [Matrix.mul_zero, Matrix.zero_mul] at this
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU,
      Matrix.mul_one] at this
  have : E.symm ⟨x, hx⟩ = 0 := Subtype.ext h''
  rw [LinearEquiv.map_eq_zero_iff] at this
  exact congrArg Subtype.val this

theorem transC_injective {z : AlbertC} (hz : InQ Q z) (h : transC E U g z = 0) : z = 0 := by
  have hc := congrArg Matrix.conjTranspose h
  rw [← transC_conj E U g hg hz, Matrix.conjTranspose_zero] at hc
  simp only [transC, conj_re, conj_im, transR_neg] at h hc
  have hre : transR E U g z.re = 0 := by
    have := congrArg (fun M => (1 / 2 : ℂ) • M) (congrArg₂ (· + ·) h hc)
    simp only [add_zero, smul_zero] at this
    rw [← this]; module
  have him : transR E U g z.im = 0 := by
    have := congrArg₂ (· - ·) h hc
    simp only [sub_zero] at this
    have h2 : (2 * Complex.I) • transR E U g z.im = 0 := by rw [← this]; module
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (mul_ne_zero two_ne_zero Complex.I_ne_zero)
    · exact h3
  exact AlbertC.ext (transR_injective E U g hg hU hz.1 hre) (transR_injective E U g hg hU hz.2 him)

variable (hE : ∀ X Y, (E (fullHermitianProduct X Y)).val = Glennie.jordan (E X).val (E Y).val)
include hE

theorem transR_jordan {x y : Glennie.Albert} (hx : x ∈ Q) (hy : y ∈ Q)
    (hxy : Glennie.jordan x y ∈ Q) :
    transR E U g (Glennie.jordan x y) = symZ (transR E U g x) (transR E U g y) := by
  rw [transR_mem E U g hg hxy, transR_mem E U g hg hx, transR_mem E U g hg hy,
    symm_jordan E hE hx hy hxy]
  set A := (E.symm ⟨x, hx⟩).val
  set B := (E.symm ⟨y, hy⟩).val
  change zIdx (U * ((1 / 2 : ℂ) • (A * B + B * A)) * star U) = _
  unfold symZ
  rw [← zIdx_mul, ← zIdx_mul, ← zIdx_add, ← zIdx_smul]
  refine congrArg zIdx ?_
  have e1 : U * A * star U * (U * B * star U) = U * (A * B) * star U := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul]
  have e2 : U * B * star U * (U * A * star U) = U * (B * A) * star U := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul]
  rw [e1, e2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

theorem transC_jordan (hQ : ∀ x y, x ∈ Q → y ∈ Q → Glennie.jordan x y ∈ Q) {z w : AlbertC}
    (hz : InQ Q z) (hw : InQ Q w) :
    transC E U g (AlbertC.jordan z w) = symZ (transC E U g z) (transC E U g w) := by
  rw [transC, transC, transC, symZ_expand]
  simp only [jordan_re, jordan_im, transR_sub, transR_add]
  rw [transR_jordan E U g hg hU hE hz.1 hw.1 (hQ _ _ hz.1 hw.1),
    transR_jordan E U g hg hU hE hz.2 hw.2 (hQ _ _ hz.2 hw.2),
    transR_jordan E U g hg hU hE hz.1 hw.2 (hQ _ _ hz.1 hw.2),
    transR_jordan E U g hg hU hE hz.2 hw.1 (hQ _ _ hz.2 hw.1)]

end Transport

end

end ThirteenPlanes.AlbertGrading.Contrast
