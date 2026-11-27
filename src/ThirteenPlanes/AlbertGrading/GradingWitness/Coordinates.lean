module

public import ThirteenPlanes.AlbertGrading.Grading.Statements
public import ThirteenPlanes.Graded.Characters

@[expose] public section

set_option backward.privateInPublic true

/-! # The reference grading is a ternary grading group

The accepted real signed coordinates `Graded.nativeSignedCoordinates : J ≃ SignedUnital` identify
`J` with the real form `{z : G → ℂ | z(-q) = conj (z q)}` of `ℂ^G`, intertwining the reference action
`Graded.nativeCharacterAction s` with multiplication by `ω^{s·q}` on the coordinate `q`.
Extending them complex-linearly gives a complex-linear bijection `J_ℂ ≃ ℂ^G`
(`Grading.JC`, the grading model's complexification, to the `Charge → ℂ`), and the
character space `A_g` of the grading model corresponds to the line
`Graded.characterLine g = ℂ · δ_g`, which is one-dimensional
(`Graded.characterLine_dimension`). -/

namespace ThirteenPlanes.AlbertGrading

open Grading Grading.JC ThirteenPlanes.Graded

noncomputable section

namespace GradingWitness

/-- Real part of a coordinate vector, `(w q + conj (w (-q))) / 2`, in the real form. -/
def rePart (w : Charge → ℂ) : SignedUnital :=
  ⟨fun q => (w q + star (w (-q))) / 2, by
    intro q
    change (w (-q) + star (w (-(-q)))) / 2 = star ((w q + star (w (-q))) / 2)
    rw [neg_neg, star_div₀, star_add, star_star]
    simp only [star_ofNat]
    ring⟩

/-- Imaginary part of a coordinate vector, `-(i/2) (w q - conj (w (-q)))`, in the real form. -/
def imPart (w : Charge → ℂ) : SignedUnital :=
  ⟨fun q => -(Complex.I / 2) * (w q - star (w (-q))), by
    intro q
    change -(Complex.I / 2) * (w (-q) - star (w (-(-q)))) =
      star (-(Complex.I / 2) * (w q - star (w (-q))))
    rw [neg_neg, star_mul, star_neg, star_div₀, star_sub, star_star]
    simp only [Complex.star_def, Complex.conj_I, map_ofNat]
    ring⟩

/-- The complex-linear coordinate map `J_ℂ → ℂ^G`, `x + i y ↦ c(x) + i c(y)`. -/
def coordsFun (z : JC) : Charge → ℂ := fun q =>
  (nativeSignedCoordinates z.re).val q + Complex.I * (nativeSignedCoordinates z.im).val q

private theorem coordsFun_smul (c : ℂ) (z : JC) : coordsFun (c • z) = c • coordsFun z := by
  funext q
  simp only [coordsFun, smul_re, smul_im, map_sub, map_add, map_smul, Submodule.coe_sub,
    Submodule.coe_add, Submodule.coe_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    Complex.real_smul, smul_eq_mul]
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  linear_combination
    (-((nativeSignedCoordinates z.re).val q + Complex.I * (nativeSignedCoordinates z.im).val q)) * hc +
    (-((c.im : ℂ) * (nativeSignedCoordinates z.im).val q)) * Complex.I_sq

/-- The coordinate map as a complex-linear equivalence `J_ℂ ≃ ℂ^G`. -/
def coords : JC ≃ₗ[ℂ] (Charge → ℂ) where
  toFun := coordsFun
  invFun w := ⟨nativeSignedCoordinates.symm (rePart w), nativeSignedCoordinates.symm (imPart w)⟩
  map_add' z w := by
    funext q
    simp only [coordsFun, add_re, add_im, map_add, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c z := coordsFun_smul c z
  left_inv z := by
    have ha := (nativeSignedCoordinates z.re).property
    have hb := (nativeSignedCoordinates z.im).property
    apply JC.ext
    · change nativeSignedCoordinates.symm (rePart (coordsFun z)) = z.re
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      funext q
      change (coordsFun z q + star (coordsFun z (-q))) / 2 = _
      simp only [coordsFun, star_add, star_mul, ha q, hb q, Complex.star_def, Complex.conj_conj,
        Complex.conj_I]
      ring
    · change nativeSignedCoordinates.symm (imPart (coordsFun z)) = z.im
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      funext q
      change -(Complex.I / 2) * (coordsFun z q - star (coordsFun z (-q))) = _
      simp only [coordsFun, star_add, star_mul, ha q, hb q, Complex.star_def, Complex.conj_conj,
        Complex.conj_I]
      linear_combination (-(nativeSignedCoordinates z.im).val q) * Complex.I_sq
  right_inv w := by
    funext q
    change (nativeSignedCoordinates (nativeSignedCoordinates.symm (rePart w))).val q +
      Complex.I * (nativeSignedCoordinates (nativeSignedCoordinates.symm (imPart w))).val q = w q
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    change (w q + star (w (-q))) / 2 + Complex.I * (-(Complex.I / 2) * (w q - star (w (-q)))) = w q
    linear_combination (-(w q - star (w (-q))) / 2) * Complex.I_sq

theorem coords_apply (z : JC) (q : Charge) :
    coords z q =
      (nativeSignedCoordinates z.re).val q + Complex.I * (nativeSignedCoordinates z.im).val q := rfl

/-- The coordinates intertwine the complexified reference action with the character action. -/
theorem coords_act (s : Charge) (z : JC) :
    coords (act nativeGradingHom s z) = characterAction s (coords z) := by
  funext q
  change (nativeSignedCoordinates (nativeCharacterAction s z.re)).val q +
      Complex.I * (nativeSignedCoordinates (nativeCharacterAction s z.im)).val q = _
  rw [nativeCharacterAction_coordinates, nativeCharacterAction_coordinates,
    characterAction_apply, characterAction_apply, characterAction_apply, coords_apply]
  ring

/-- Under the coordinates, the character space `A_g` of the reference action is the accepted
character line `ℂ · δ_g`. -/
theorem charSpace_native_eq (g : Charge) :
    charSpace nativeGradingHom g = (characterLine g).comap coords.toLinearMap := by
  ext z
  rw [Submodule.mem_comap, mem_characterLine_iff]
  change (∀ s, act nativeGradingHom s z = gradeCharacter s g • z) ↔ _
  refine forall_congr' fun s => ?_
  rw [LinearEquiv.coe_coe, ← coords_act, gradeCharacter, ← map_smul]
  exact coords.injective.eq_iff.symm

theorem charSpace_native_finrank (g : Charge) :
    Module.finrank ℂ (charSpace nativeGradingHom g) = 1 := by
  rw [charSpace_native_eq, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  exact characterLine_dimension g

end GradingWitness

end

end ThirteenPlanes.AlbertGrading
