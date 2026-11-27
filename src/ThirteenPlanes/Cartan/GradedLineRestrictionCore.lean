module

public import ThirteenPlanes.Cartan.DerivationGradingGeneration
public import ThirteenPlanes.Cartan.DerivationGradingProjection

@[expose] public section

set_option backward.privateInPublic true

/-! The line subalgebra and restriction of its homogeneous derivations. -/

open Module

namespace ThirteenPlanes.Cartan.NormalizedTernaryBasis

noncomputable section

variable {A : Type*} [AddCommGroup A] [Module ℂ A] (M : NormalizedTernaryBasis A)

variable (L : Submodule (ZMod 3) Charge)

/-- The complex Jordan subalgebra spanned by the degrees in the charge plane. -/
def gradedLineSubspace : Submodule ℂ A :=
  Submodule.span ℂ (Set.range (fun g : L => M.basis g.val))

theorem basis_mem_gradedLineSubspace (g : L) :
    M.basis g.val ∈ M.gradedLineSubspace L :=
  Submodule.subset_span ⟨g, rfl⟩

/-- The actual basis on the projective line, including the unit in degree zero. -/
def gradedLineBasis : Basis L ℂ (M.gradedLineSubspace L) :=
  Basis.span (M.basis.linearIndependent.comp (fun g : L => g.val) Subtype.val_injective)

@[simp] theorem gradedLineBasis_coe (g : L) :
    (M.gradedLineBasis L g : A) = M.basis g.val := by
  exact Basis.coe_span_apply _ _

theorem gradedLine_productClosed : M.ProductClosed (M.gradedLineSubspace L) := by
  let S := M.gradedLineSubspace L
  intro x y hx hy
  refine Submodule.span_induction₂ (p := fun x y _ _ => M.product x y ∈ S) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
    obtain ⟨c, hc⟩ := M.homogeneous_product g.val h.val
    rw [hc]
    exact S.smul_mem c (M.basis_mem_gradedLineSubspace L (g + h))
  · intro y _
    simp
  · intro x _
    simp
  · intro x y z _ _ _ hx hy
    rw [map_add, LinearMap.add_apply]
    exact S.add_mem hx hy
  · intro x y z _ _ _ hy hz
    rw [map_add]
    exact S.add_mem hy hz
  · intro c x y _ _ hx
    rw [map_smul, LinearMap.smul_apply]
    exact S.smul_mem c hx
  · intro c x y _ _ hy
    rw [map_smul]
    exact S.smul_mem c hy

/-- The actual product of line coordinates. -/
def gradedLineProduct : M.gradedLineSubspace L →ₗ[ℂ] M.gradedLineSubspace L →ₗ[ℂ] M.gradedLineSubspace L :=
  LinearMap.mk₂ ℂ
    (fun x y => ⟨M.product x.val y.val, M.gradedLine_productClosed L x.property y.property⟩)
    (fun x y z => Subtype.ext (by
      change M.product (x.val + y.val) z.val = M.product x.val z.val + M.product y.val z.val
      rw [map_add, LinearMap.add_apply]))
    (fun c x y => Subtype.ext (by
      change M.product (c • x.val) y.val = c • M.product x.val y.val
      rw [map_smul, LinearMap.smul_apply]))
    (fun x y z => Subtype.ext ((M.product x.val).map_add y.val z.val))
    (fun c x y => Subtype.ext (map_smul (M.product x.val) c y.val))

@[simp] theorem gradedLineProduct_coe (x y : M.gradedLineSubspace L) :
    (M.gradedLineProduct L x y : A) = M.product x.val y.val := rfl

theorem gradedLineBasis_unit_left (x : M.gradedLineSubspace L) :
    M.gradedLineProduct L (M.gradedLineBasis L 0) x = x := by
  apply Subtype.ext
  simp [M.unit_left]

/-- The sum of all ambient derivation grades lying in the charge plane. -/
def lineDerivations : Submodule ℂ (Module.End ℂ A) :=
  ⨆ γ : L, M.derivationGrade γ.val

theorem lineDerivations_le : M.lineDerivations L ≤ M.derivations :=
  iSup_le fun _ _ h => (M.mem_derivationGrade.mp h).1

theorem grade_preserves_line {D : Module.End ℂ A} {γ : L}
    (h : M.HasDegree D γ.val) :
    M.gradedLineSubspace L ≤ (M.gradedLineSubspace L).comap D := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  obtain ⟨c, hc⟩ := h g.val
  change D (M.basis g.val) ∈ M.gradedLineSubspace L
  rw [hc]
  exact (M.gradedLineSubspace L).smul_mem c (M.basis_mem_gradedLineSubspace L (g + γ))

theorem lineDerivations_preserve_line {D : Module.End ℂ A}
    (h : D ∈ M.lineDerivations L) {x : A} (hx : x ∈ M.gradedLineSubspace L) :
    D x ∈ M.gradedLineSubspace L := by
  refine Submodule.iSup_induction _ (motive := fun T : Module.End ℂ A =>
      T x ∈ M.gradedLineSubspace L) h ?_ ?_ ?_
  · intro γ T hT
    exact M.grade_preserves_line L (M.mem_derivationGrade.mp hT).2 hx
  · simp
  · intro T U hT hU
    exact (M.gradedLineSubspace L).add_mem hT hU

private theorem bracket_add_left (D E F : Module.End ℂ A) :
    operatorBracket (D + E) F = operatorBracket D F + operatorBracket E F := by
  simp only [operatorBracket, add_mul, mul_add]
  abel

private theorem bracket_add_right (D E F : Module.End ℂ A) :
    operatorBracket D (E + F) = operatorBracket D E + operatorBracket D F := by
  simp only [operatorBracket, add_mul, mul_add]
  abel

/-- The grades indexed by a charge plane form a Lie subalgebra. -/
theorem lineDerivations_bracket {D E : Module.End ℂ A}
    (hD : D ∈ M.lineDerivations L) (hE : E ∈ M.lineDerivations L) :
    operatorBracket D E ∈ M.lineDerivations L := by
  refine Submodule.iSup_induction _ (motive := fun D => operatorBracket D E ∈ M.lineDerivations L)
    hD ?_ (by simp [operatorBracket]) ?_
  · intro γ D hD
    refine Submodule.iSup_induction _ (motive := fun E => operatorBracket D E ∈ M.lineDerivations L)
      hE ?_ (by simp [operatorBracket]) ?_
    · intro δ E hE
      exact Submodule.mem_iSup_of_mem (γ + δ) (M.derivationGrade_bracket hD hE)
    · intro E F hE hF
      rw [bracket_add_right]
      exact (M.lineDerivations L).add_mem hE hF
  · intro D F hD hF
    rw [bracket_add_left]
    exact (M.lineDerivations L).add_mem hD hF

/-- Derivations of the induced line product, without restrictions on their degree. -/
def gradedLineDerivations : Submodule ℂ (Module.End ℂ (M.gradedLineSubspace L)) where
  carrier := {D | ∀ x y, D (M.gradedLineProduct L x y) =
    M.gradedLineProduct L (D x) y + M.gradedLineProduct L x (D y)}
  zero_mem' := by intro x y; simp
  add_mem' := by
    rintro D E hD hE x y
    simp only [LinearMap.add_apply, hD x y, hE x y, map_add]
    abel
  smul_mem' := by
    rintro c D hD x y
    simp only [LinearMap.smul_apply, hD x y, map_smul, smul_add]

theorem mem_gradedLineDerivations {D : Module.End ℂ (M.gradedLineSubspace L)} :
    D ∈ M.gradedLineDerivations L ↔
      ∀ x y, D (M.gradedLineProduct L x y) =
        M.gradedLineProduct L (D x) y + M.gradedLineProduct L x (D y) := Iff.rfl

private def lineRestrictionValue (D : M.lineDerivations L) : Module.End ℂ (M.gradedLineSubspace L) :=
  (D.val.comp (M.gradedLineSubspace L).subtype).codRestrict (M.gradedLineSubspace L)
    (fun x => M.lineDerivations_preserve_line L D.property x.property)

/-- The map restricting actual derivations to the actual line subalgebra. -/
def gradedLineRestriction : M.lineDerivations L →ₗ[ℂ] M.gradedLineDerivations L where
  toFun D := ⟨M.lineRestrictionValue L D, M.mem_gradedLineDerivations L |>.mpr (by
    intro x y
    apply Subtype.ext
    change D.val (M.product x.val y.val) = M.product (D.val x.val) y.val + M.product x.val (D.val y.val)
    exact (M.lineDerivations_le L D.property) _ _)⟩
  map_add' D E := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rfl
  map_smul' c D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rfl

@[simp] theorem gradedLineRestriction_apply (D : M.lineDerivations L) (x : M.gradedLineSubspace L) :
    ((M.gradedLineRestriction L D).val x : A) = D.val x.val := rfl

end

end ThirteenPlanes.Cartan.NormalizedTernaryBasis
