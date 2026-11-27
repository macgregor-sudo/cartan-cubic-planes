module

public import ThirteenPlanes.AlbertGrading.Grading.Statements
public import ThirteenPlanes.Graded.Characters

@[expose] public section

set_option backward.privateInPublic true

/-! The original native grading realizes the literal Albert complex character spaces. -/

namespace ThirteenPlanes.Cartan

open AlbertLean.Generic.C1Coordinates AlbertGrading.Grading

noncomputable section

private def signedCoordinate : Glennie.Albert →ₗ[ℝ] (Charge → ℂ) :=
  signedUnitalSubspace.subtype.comp Graded.nativeSignedCoordinates.toLinearMap

private theorem signedCoordinate_star (x : Glennie.Albert) (q : Charge) :
    star (signedCoordinate x (-q)) = signedCoordinate x q := by
  change star ((Graded.nativeSignedCoordinates x).val (-q)) =
    (Graded.nativeSignedCoordinates x).val q
  rw [(Graded.nativeSignedCoordinates x).property q, star_star]

private def signedComplexRe (z : Charge → ℂ) : SignedUnital :=
  ⟨fun q => (z q + star (z (-q))) / 2, by
    intro q
    change (z (-q) + star (z (-(-q)))) / 2 = star ((z q + star (z (-q))) / 2)
    simp only [Complex.star_def, neg_neg, map_div₀, map_add, map_ofNat, Complex.conj_conj]
    ring⟩

private def signedComplexIm (z : Charge → ℂ) : SignedUnital :=
  ⟨fun q => (z q - star (z (-q))) / (2 * Complex.I), by
    intro q
    change (z (-q) - star (z (-(-q)))) / (2 * Complex.I) =
      star ((z q - star (z (-q))) / (2 * Complex.I))
    simp only [Complex.star_def, neg_neg, map_div₀, map_sub, map_mul, map_ofNat,
      Complex.conj_I, Complex.conj_conj]
    field_simp [Complex.I_ne_zero]
    ring⟩

private def signedComplexAssembly (z : JC) : Charge → ℂ :=
  fun q => signedCoordinate z.re q + Complex.I * signedCoordinate z.im q

private theorem signedComplexAssembly_star (z : JC) (q : Charge) :
    star (signedComplexAssembly z (-q)) =
      signedCoordinate z.re q - Complex.I * signedCoordinate z.im q := by
  simp only [signedComplexAssembly, star_add, star_mul', signedCoordinate_star,
    show star Complex.I = -Complex.I from Complex.conj_I, neg_mul, sub_eq_add_neg]

/-- Complex-linear signed coordinates on the same pair carrier used for literal character spaces. -/
def nativeGradeCoordinates : JC ≃ₗ[ℂ] (Charge → ℂ) where
  toFun := signedComplexAssembly
  invFun z := ⟨Graded.nativeSignedCoordinates.symm (signedComplexRe z),
    Graded.nativeSignedCoordinates.symm (signedComplexIm z)⟩
  left_inv z := by
    apply JC.ext
    · apply Graded.nativeSignedCoordinates.injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      funext q
      change (signedComplexAssembly z q + star (signedComplexAssembly z (-q))) / 2 =
        signedCoordinate z.re q
      rw [signedComplexAssembly_star]
      unfold signedComplexAssembly
      ring
    · apply Graded.nativeSignedCoordinates.injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      funext q
      change (signedComplexAssembly z q - star (signedComplexAssembly z (-q))) /
        (2 * Complex.I) = signedCoordinate z.im q
      rw [signedComplexAssembly_star]
      unfold signedComplexAssembly
      field_simp [Complex.I_ne_zero]
      ring
  right_inv z := by
    funext q
    change ((Graded.nativeSignedCoordinates (Graded.nativeSignedCoordinates.symm
      (signedComplexRe z))).val q + Complex.I *
      (Graded.nativeSignedCoordinates (Graded.nativeSignedCoordinates.symm
        (signedComplexIm z))).val q) = z q
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    change (z q + star (z (-q))) / 2 + Complex.I *
      ((z q - star (z (-q))) / (2 * Complex.I)) = z q
    field_simp [Complex.I_ne_zero]
    ring
  map_add' x y := by
    funext q
    simp only [signedComplexAssembly, JC.add_re, JC.add_im, map_add, Pi.add_apply]
    ring
  map_smul' c z := by
    funext q
    simp only [signedComplexAssembly, JC.smul_re, JC.smul_im, map_add, map_sub, map_smul,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul, RingHom.id_apply]
    conv_rhs => rw [← Complex.re_add_im c]
    linear_combination -((c.im : ℂ) * signedCoordinate z.im q) * Complex.I_mul_I

theorem nativeGradeCoordinates_equivariant (s : Charge) (z : JC) :
    nativeGradeCoordinates (act Graded.nativeGradingHom s z) =
      Graded.characterAction s (nativeGradeCoordinates z) := by
  funext q
  change signedCoordinate (Graded.nativeCharacterAction s z.re) q +
    Complex.I * signedCoordinate (Graded.nativeCharacterAction s z.im) q =
      chargePhase (chargeDot s q) *
        (signedCoordinate z.re q + Complex.I * signedCoordinate z.im q)
  have h (x : Glennie.Albert) := congrFun (Graded.nativeCharacterAction_coordinates s x) q
  change ∀ x, signedCoordinate (Graded.nativeCharacterAction s x) q =
    chargePhase (chargeDot s q) * signedCoordinate x q at h
  rw [h, h]
  ring

theorem nativeGradeCoordinates_mem_characterLine (g : Charge) (z : JC) :
    nativeGradeCoordinates z ∈ Graded.characterLine g ↔
      z ∈ charSpace Graded.nativeGradingHom g := by
  rw [Graded.mem_characterLine_iff]
  change (∀ s : Charge, Graded.characterAction s (nativeGradeCoordinates z) =
    gradeCharacter s g • nativeGradeCoordinates z) ↔
      ∀ s : Charge, act Graded.nativeGradingHom s z = gradeCharacter s g • z
  simp only [← nativeGradeCoordinates_equivariant, ← map_smul, nativeGradeCoordinates.injective.eq_iff]

/-- The explicit standard action is a ternary grading on the literal native Albert algebra. -/
theorem nativeGradingHom_isTernaryGrading : IsTernaryGrading Graded.nativeGradingHom := by
  refine ⟨Graded.nativeGradingHom_injective, fun s =>
    Graded.nativeCharacterAction_product s.toAdd, fun g => ?_⟩
  let U := charSpace Graded.nativeGradingHom g
  have hmap : U.map nativeGradeCoordinates.toLinearMap = Graded.characterLine g := by
    ext w
    obtain ⟨z, rfl⟩ := nativeGradeCoordinates.surjective w
    constructor
    · rintro ⟨x, hx, heq⟩
      have hz : x = z := nativeGradeCoordinates.injective heq
      exact (nativeGradeCoordinates_mem_characterLine g z).mpr (hz ▸ hx)
    · intro hz
      exact ⟨z, (nativeGradeCoordinates_mem_characterLine g z).mp hz, rfl⟩
  have heq := (U.equivMapOfInjective nativeGradeCoordinates.toLinearMap
    nativeGradeCoordinates.injective).finrank_eq
  rw [hmap] at heq
  exact heq.trans (Graded.characterLine_dimension g)

end
end ThirteenPlanes.Cartan
