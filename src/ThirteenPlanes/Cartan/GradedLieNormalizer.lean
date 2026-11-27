module

public import ThirteenPlanes.Cartan.ExponentialNormalizer

@[expose] public section

set_option backward.privateInPublic true

/-! The actual exponential acts by conjugation on real Jordan derivations. -/

namespace ThirteenPlanes.Cartan

open NormedSpace

noncomputable section

namespace TraceJordanData

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]
  (M : TraceJordanData J)

local instance : CompleteSpace J := FiniteDimensional.completeSpace ℝ J
local instance : NormedAlgebra ℚ (J →L[ℝ] J) := NormedAlgebra.restrictScalars ℚ ℝ _

/-- The inverse of the native exponential automorphism is the operator exponential of minus the derivation. -/
theorem expAutomorphism_symm_apply (D : M.skewDerivations) (x : J) :
    (M.expAutomorphism D).action.symm x =
      exp (-LinearMap.toContinuousLinearMap D.val.val) x := by
  let A := LinearMap.toContinuousLinearMap D.val.val
  have h : exp A * exp (-A) = 1 := by
    rw [← exp_add_of_commute (Commute.refl A).neg_right, add_neg_cancel, exp_zero]
  apply (M.expAutomorphism D).action.injective
  rw [(M.expAutomorphism D).action.apply_symm_apply, M.expAutomorphism_apply]
  change x = (exp A * exp (-A)) x
  rw [h]
  rfl

private theorem cont_conjugate_expAutomorphism (D : M.skewDerivations) (X : Module.End ℝ J) :
    LinearMap.toContinuousLinearMap ((M.expAutomorphism D).action.toLinearEquiv.conj X) =
      exp (LinearMap.toContinuousLinearMap D.val.val) * LinearMap.toContinuousLinearMap X *
        exp (-LinearMap.toContinuousLinearMap D.val.val) := by
  apply ContinuousLinearMap.ext
  intro x
  change (M.expAutomorphism D).action (X ((M.expAutomorphism D).action.symm x)) = _
  rw [M.expAutomorphism_apply, M.expAutomorphism_symm_apply]
  rfl

/-- The actual exponential Jordan automorphism normalizes any real operator subspace
preserved by commutation with its derivation. -/
theorem expAutomorphism_normalizes (D : M.skewDerivations)
    (S : Submodule ℝ (Module.End ℝ J))
    (closed : ∀ X ∈ S, operatorBracket D.val.val X ∈ S) :
    S.map (M.expAutomorphism D).action.toLinearEquiv.conj.toLinearMap = S := by
  let c : Module.End ℝ J ≃ₗ[ℝ] (J →L[ℝ] J) := LinearMap.toContinuousLinearMap
  let S' := S.map c.toLinearMap
  let d := c D.val.val
  have hclosed (X : J →L[ℝ] J) (hX : X ∈ S') : d * X - X * d ∈ S' := by
    obtain ⟨Y, hY, rfl⟩ := hX
    refine ⟨operatorBracket D.val.val Y, closed Y hY, ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have h := exp_normalizes_of_commutator S' d hclosed
  apply Submodule.map_injective_of_injective c.injective
  ext Y
  constructor
  · rintro ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    change c ((M.expAutomorphism D).action.toLinearEquiv.conj X) ∈ S'
    have hx : exp d * c X * exp (-d) ∈ S' := by
      change exp d * c X * exp (-d) ∈ (S' : Set (J →L[ℝ] J))
      rw [← h]
      exact ⟨c X, ⟨X, hX, rfl⟩, rfl⟩
    rw [show c ((M.expAutomorphism D).action.toLinearEquiv.conj X) =
      exp d * c X * exp (-d) from M.cont_conjugate_expAutomorphism D X]
    exact hx
  · intro hY
    have he : Y ∈ (fun X => exp d * X * exp (-d)) '' (S' : Set (J →L[ℝ] J)) := by
      rw [h]
      exact hY
    obtain ⟨_, ⟨X, hX, rfl⟩, rfl⟩ := he
    refine ⟨(M.expAutomorphism D).action.toLinearEquiv.conj X, ⟨X, hX, rfl⟩, ?_⟩
    exact M.cont_conjugate_expAutomorphism D X

/-- Conjugation by a Jordan automorphism is a linear equivalence on the full skew derivation algebra. -/
def Automorphism.conjugateDerivationEquiv (g : M.Automorphism) :
    M.skewDerivations ≃ₗ[ℝ] M.skewDerivations where
  toFun := g.conjugateDerivation M
  invFun := (g.symm M).conjugateDerivation M
  left_inv D := by
    apply Subtype.ext
    exact conjugateSkew_symm_apply_apply g.action D.val
  right_inv D := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change g.action (g.action.symm (D.val.val (g.action (g.action.symm x)))) = D.val.val x
    rw [g.action.apply_symm_apply, g.action.apply_symm_apply]
  map_add' D E := Subtype.ext ((conjugateSkew g.action).map_add D.val E.val)
  map_smul' a D := Subtype.ext ((conjugateSkew g.action).map_smul a D.val)

@[simp] theorem Automorphism.conjugateDerivationEquiv_operator (g : M.Automorphism)
    (D : M.skewDerivations) :
    (g.conjugateDerivationEquiv M D).val.val = g.action.toLinearEquiv.conj D.val.val := rfl

/-- Normalizer law for the exponential on a subspace of skew Jordan derivations. -/
theorem expAutomorphism_normalizes_derivationSubspace (D : M.skewDerivations)
    (S : Submodule ℝ M.skewDerivations)
    (closed : ∀ X ∈ S, ∃ Y ∈ S, Y.val.val = operatorBracket D.val.val X.val.val) :
    S.map ((M.expAutomorphism D).conjugateDerivationEquiv M).toLinearMap = S := by
  let f : M.skewDerivations →ₗ[ℝ] Module.End ℝ J :=
    (skewOperators J).subtype.comp M.skewDerivations.subtype
  have hf : Function.Injective f :=
    Subtype.val_injective.comp Subtype.val_injective
  have hc : ∀ X ∈ S.map f, operatorBracket D.val.val X ∈ S.map f := by
    rintro X ⟨Y, hY, rfl⟩
    obtain ⟨Z, hZ, he⟩ := closed Y hY
    exact ⟨Z, hZ, he⟩
  have h := M.expAutomorphism_normalizes D (S.map f) hc
  apply Submodule.map_injective_of_injective hf
  rw [← Submodule.map_comp, ← h, ← Submodule.map_comp]
  congr 1

/-- Real derivation conjugation agrees with orthogonal conjugation on the trace kernel. -/
theorem Automorphism.restrictDerivation_map_conjugate (g : M.Automorphism)
    (S : Submodule ℝ M.skewDerivations) :
    (S.map M.restrictDerivation).map (conjugateSkew (g.traceAction M)).toLinearMap =
      (S.map (g.conjugateDerivationEquiv M).toLinearMap).map M.restrictDerivation := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

end TraceJordanData

end

end ThirteenPlanes.Cartan
