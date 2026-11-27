module

public import ThirteenPlanes.Cartan.AlbertDerivationComplex
public import ThirteenPlanes.Cartan.AlbertOperators
public import ThirteenPlanes.Cartan.RotatedKillingDecomposition

@[expose] public section

set_option backward.privateInPublic true

/-! Conjugation on native Albert derivations and on their fixed traceless subspaces. -/

namespace ThirteenPlanes.Cartan

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

private def nativeConjugateDerivation (g : Glennie.CompactAutomorphism) (D : NativeAlbertDerivations) :
    NativeAlbertDerivations := nativeAlbertDerivationSkewEquiv.symm
  ((albertJordanAction g).conjugateDerivation albertJordan (nativeAlbertDerivationSkewEquiv D))

/-- Conjugation by an actual Albert automorphism on the actual real derivation Lie algebra. -/
def nativeAlbertLieAction (g : Glennie.CompactAutomorphism) :
    NativeAlbertDerivations ≃ₗ⁅ℝ⁆ NativeAlbertDerivations where
  toFun := nativeConjugateDerivation g
  invFun := nativeConjugateDerivation g.symm
  left_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change g.equiv.symm (g.equiv (D.val (g.equiv.symm (g.equiv x)))) = D.val x
    rw [g.equiv.symm_apply_apply, g.equiv.symm_apply_apply]
  right_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change g.equiv (g.equiv.symm (D.val (g.equiv (g.equiv.symm x)))) = D.val x
    rw [g.equiv.apply_symm_apply, g.equiv.apply_symm_apply]
  map_add' D E := Subtype.ext ((g.equiv.conj).map_add D.val E.val)
  map_smul' r D := Subtype.ext ((g.equiv.conj).map_smul r D.val)
  map_lie' := fun {D E} => by
    apply Subtype.ext
    change g.equiv.conj (D.val * E.val - E.val * D.val) =
      g.equiv.conj D.val * g.equiv.conj E.val - g.equiv.conj E.val * g.equiv.conj D.val
    rw [map_sub, conj_mul, conj_mul]

@[simp] theorem nativeAlbertLieAction_val (g : Glennie.CompactAutomorphism) (D : NativeAlbertDerivations) :
    (nativeAlbertLieAction g D).val = g.equiv.conj D.val := rfl

/-- Common kernel of a Lie subalgebra on the traceless Albert representation. -/
def albertRealFixed (T : LieSubalgebra ℝ NativeAlbertDerivations) : Submodule ℝ NativeTraceless :=
  ⨅ D : T, LinearMap.ker (D.val.val.comp Glennie.traceLinear.ker.subtype)

theorem mem_albertRealFixed (T : LieSubalgebra ℝ NativeAlbertDerivations) (x : NativeTraceless) :
    x ∈ albertRealFixed T ↔ ∀ D ∈ T, D.val x.val = 0 := by
  simp [albertRealFixed, Submodule.mem_iInf, Subtype.forall]

/-- The common traceless kernel transforms by the same native Albert automorphism as the Cartan. -/
theorem albertRealFixed_map (g : Glennie.CompactAutomorphism) (T : LieSubalgebra ℝ NativeAlbertDerivations) :
    albertRealFixed (T.map (nativeAlbertLieAction g).toLieHom) =
      (albertRealFixed T).map (albertTracelessAction g).toLinearMap := by
  ext x
  rw [mem_albertRealFixed]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := (albertTracelessAction g).surjective x
    refine ⟨y, (mem_albertRealFixed T y).mpr ?_, rfl⟩
    intro D hD
    have he := hx (nativeAlbertLieAction g D) ((LieSubalgebra.mem_map _ _ _).mpr ⟨D, hD, rfl⟩)
    change g.equiv (D.val (g.equiv.symm (g.equiv y.val))) = 0 at he
    rw [g.equiv.symm_apply_apply, ← g.equiv.map_zero] at he
    exact g.equiv.injective he
  · rintro ⟨y, hy, rfl⟩ X hX
    obtain ⟨D, hD, rfl⟩ := (LieSubalgebra.mem_map _ _ _).mp hX
    change g.equiv (D.val (g.equiv.symm (g.equiv y.val))) = 0
    rw [g.equiv.symm_apply_apply, (mem_albertRealFixed T y).mp hy D hD, map_zero]

/-- The fixed planes of a partially conjugated family rotate on exactly the indicated indices. -/
theorem albertRealFixed_rotated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → LieSubalgebra ℝ NativeAlbertDerivations) (L : Set ι) (g : Glennie.CompactAutomorphism)
    (i : ι) [Decidable (i ∈ L)] :
    albertRealFixed (rotatedKillingCartans T L (nativeAlbertLieAction g) i) =
      if i ∈ L then (albertRealFixed (T i)).map (albertTracelessAction g).toLinearMap else albertRealFixed (T i) := by
  classical
  by_cases hi : i ∈ L
  · simpa only [rotatedKillingCartans, ite_eq_left hi] using albertRealFixed_map g (T i)
  · simp only [rotatedKillingCartans, ite_eq_right hi]

end

end ThirteenPlanes.Cartan
