/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.F4.SignedAutomorphisms
public import ThirteenPlanes.Cartan.GradeRealAlbertOD

@[expose] public section

set_option backward.privateInPublic true

/-! Covariance of the actual opposite-character Cartans under grading symmetries. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading
open scoped BigOperators

noncomputable section

private abbrev nativeρ := Graded.nativeGradingHom
private theorem nativeρ_grading : IsTernaryGrading nativeρ :=
  nativeGradingHom_isTernaryGrading

/-- The complex linear extension of an actual Albert automorphism. -/
def albertAutomorphismComplex (g : Glennie.CompactAutomorphism) : JC ≃ₗ[ℂ] JC :=
  { JC.mapC g.equiv.toLinearMap with
    invFun := JC.mapC g.equiv.symm.toLinearMap
    left_inv := fun x => by apply JC.ext <;> simp
    right_inv := fun x => by apply JC.ext <;> simp }

@[simp] theorem albertAutomorphismComplex_re (g : Glennie.CompactAutomorphism) (z : JC) :
    (albertAutomorphismComplex g z).re = g.equiv z.re := rfl

@[simp] theorem albertAutomorphismComplex_im (g : Glennie.CompactAutomorphism) (z : JC) :
    (albertAutomorphismComplex g z).im = g.equiv z.im := rfl

@[simp] theorem albertAutomorphismComplex_of (g : Glennie.CompactAutomorphism)
    (x : Glennie.Albert) : albertAutomorphismComplex g (JC.of x) = JC.of (g.equiv x) :=
  JC.mapC_of _ _

theorem albertAutomorphismComplex_mul (g : Glennie.CompactAutomorphism) (x y : JC) :
    albertAutomorphismComplex g (JC.mul x y) =
      JC.mul (albertAutomorphismComplex g x) (albertAutomorphismComplex g y) :=
  JC.mapC_mul _ g.map_jordan x y

/-- Native covariance data relating the grading parameters and grades. -/
def AlbertGradingCovariance (g : Glennie.CompactAutomorphism) (t u : Charge → Charge) : Prop :=
  (∀ s x, Graded.nativeCharacterAction s (g.equiv x) =
    g.equiv (Graded.nativeCharacterAction (t s) x)) ∧
  ∀ s q, gradeCharacter (t s) q = gradeCharacter s (u q)

theorem AlbertGradingCovariance.complex {g : Glennie.CompactAutomorphism} {t u : Charge → Charge}
    (h : AlbertGradingCovariance g t u) (s : Charge) (x : JC) :
    act nativeρ s (albertAutomorphismComplex g x) =
      albertAutomorphismComplex g (act nativeρ (t s) x) := by
  apply JC.ext
  · exact h.1 s x.re
  · exact h.1 s x.im

private theorem conj_eq_smul_iff (e : JC ≃ₗ[ℂ] JC) (D : Module.End ℂ JC) (c : ℂ) :
    e.conj D = c • D ↔ ∀ x, e (D x) = c • D (e x) := by
  constructor
  · intro h x
    have hx := LinearMap.congr_fun h (e x)
    simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, LinearMap.smul_apply]
      using hx
  · intro h
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, LinearMap.smul_apply]
      using h x

private theorem conj_apply (e : JC ≃ₗ[ℂ] JC) (D : Module.End ℂ JC) (x : JC) :
    e.conj D (e x) = e (D x) := by
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]

private theorem conj_derivation (G : JC ≃ₗ[ℂ] JC)
    (hMul : ∀ x y, G (JC.mul x y) = JC.mul (G x) (G y)) (D : Module.End ℂ JC)
    (hDer : ∀ x y, D (JC.mul x y) = JC.mul (D x) y + JC.mul x (D y)) :
    ∀ x y, G.conj D (JC.mul x y) = JC.mul (G.conj D x) y + JC.mul x (G.conj D y) := by
  intro x y
  obtain ⟨x, rfl⟩ := G.surjective x
  obtain ⟨y, rfl⟩ := G.surjective y
  rw [← hMul x y, conj_apply, conj_apply, conj_apply, hDer, map_add, hMul, hMul]

set_option maxHeartbeats 1000000 in
theorem AlbertGradingCovariance.grade_map {g : Glennie.CompactAutomorphism} {t u : Charge → Charge}
    (h : AlbertGradingCovariance g t u) (q : Charge) {D : Module.End ℂ JC}
    (hD : D ∈ (albertGradingBasis nativeρ_grading).derivationGrade q) :
    (albertAutomorphismComplex g).conj D ∈
      (albertGradingBasis nativeρ_grading).derivationGrade (u q) := by
  rw [albertGrading_derivationGrade_iff_character nativeρ_grading] at hD ⊢
  let G := albertAutomorphismComplex g
  refine ⟨?_, ?_⟩
  · have hDer : ∀ x y, D (JC.mul x y) = JC.mul (D x) y + JC.mul x (D y) := by
      simpa only [NormalizedTernaryBasis.IsDerivation, albertGradingBasis_product] using hD.1
    simpa only [NormalizedTernaryBasis.IsDerivation, albertGradingBasis_product] using
      conj_derivation G (albertAutomorphismComplex_mul g) D hDer
  · intro s
    apply (conj_eq_smul_iff _ _ _).mpr
    intro x
    obtain ⟨x, rfl⟩ := G.surjective x
    change act nativeρ s (G.conj D (G x)) =
      gradeCharacter s (u q) • G.conj D (act nativeρ s (G x))
    have hs := (conj_eq_smul_iff _ _ _).mp (hD.2 (t s)) x
    change act nativeρ (t s) (D x) = gradeCharacter (t s) q • D (act nativeρ (t s) x) at hs
    rw [conj_apply, h.complex, h.complex, conj_apply, hs, map_smul, h.2]

private theorem gradingRep_ofReal_as_mapC (D : NativeAlbertDerivations) :
    albertGradingRep (LieComplex.ofReal D) = JC.mapC D.val := by
  change (albertDerivationComplexEquiv (LieComplex.ofReal D)).val = _
  rw [albertDerivationComplexEquiv_apply_ofReal, extendAlbertDerivation_val]

private theorem gradingRep_native_conj (g : Glennie.CompactAutomorphism)
    (D : NativeAlbertDerivations) :
    albertGradingRep (LieComplex.ofReal (nativeAlbertLieAction g D)) =
      (albertAutomorphismComplex g).conj (albertGradingRep (LieComplex.ofReal D)) := by
  rw [gradingRep_ofReal_as_mapC, gradingRep_ofReal_as_mapC, nativeAlbertLieAction_val]
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (albertAutomorphismComplex g).surjective x
  rw [conj_apply]
  apply JC.ext <;> simp [LinearEquiv.conj_apply_apply]

/-- A symmetry preserving the two opposite charges maps the native Cartan into itself. -/
theorem AlbertGradingCovariance.maps_gradedCartan
    {g : Glennie.CompactAutomorphism} {t u : Charge → Charge} (h : AlbertGradingCovariance g t u)
    (p : SignedPlaneIndex) (hp : u p.val.val = p.val.val) (hn : u (-p.val.val) = -p.val.val)
    {D : NativeAlbertDerivations} (hD : D ∈ albertGradingRealCartan nativeρ_grading p) :
    nativeAlbertLieAction g D ∈ albertGradingRealCartan nativeρ_grading p := by
  change LieComplex.ofReal (nativeAlbertLieAction g D) ∈ pairedGrade (albertComplexGrade nativeρ_grading) p
  change LieComplex.ofReal D ∈ pairedGrade (albertComplexGrade nativeρ_grading) p at hD
  apply (albertComplexGradePair_mem nativeρ_grading p _).mpr
  have he := (albertComplexGradePair_mem nativeρ_grading p _).mp hD
  obtain ⟨X, hX, Y, hY, hXY⟩ := Submodule.mem_sup.mp he
  rw [gradingRep_native_conj, ← hXY, map_add]
  exact Submodule.mem_sup.mpr ⟨_, hp ▸ h.grade_map _ hX, _, hn ▸ h.grade_map _ hY, rfl⟩

/-- A symmetry with this parameter change carries each complex character line to its relabeling. -/
theorem AlbertGradingCovariance.maps_charSpace
    {g : Glennie.CompactAutomorphism} {t u : Charge → Charge} (h : AlbertGradingCovariance g t u)
    (q : Charge) {x : JC} (hx : x ∈ charSpace nativeρ q) :
    albertAutomorphismComplex g x ∈ charSpace nativeρ (u q) := by
  intro s
  rw [h.complex, hx (t s), map_smul, h.2]

/-- The induced real action maps the actual point planes along the two opposite charges. -/
theorem AlbertGradingCovariance.maps_pointPlane
    {g : Glennie.CompactAutomorphism} {t u : Charge → Charge} (h : AlbertGradingCovariance g t u)
    (q r : SignedPlaneIndex) (hr : u q.val.val = r.val.val) (hn : u (-q.val.val) = -r.val.val)
    {x : NativeTraceless} (hx : x ∈ pointPlane nativeρ q) :
    albertTracelessAction g x ∈ pointPlane nativeρ r := by
  change JC.of x.val ∈ charSpace nativeρ q.val.val ⊔ charSpace nativeρ (-q.val.val) at hx
  change JC.of (g.equiv x.val) ∈ charSpace nativeρ r.val.val ⊔ charSpace nativeρ (-r.val.val)
  obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp hx
  rw [← albertAutomorphismComplex_of, ← he, map_add]
  exact Submodule.mem_sup.mpr ⟨_, hr ▸ h.maps_charSpace _ hy, _, hn ▸ h.maps_charSpace _ hz, rfl⟩

end

end ThirteenPlanes.Cartan
