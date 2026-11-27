module

public import ThirteenPlanes.Basic
public import ThirteenPlanes.Cartan.Casimir
public import ThirteenPlanes.Cartan.ComplexOperators

@[expose] public section

/-! Fixed Jordan subalgebras and multiplication operators on the trace-free representation. -/

namespace ThirteenPlanes.Cartan

open scoped RealInnerProductSpace TensorProduct

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- The real unital Jordan product and its associative positive trace metric. -/
structure TraceJordanData (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℝ J] where
  L : J →ₗ[ℝ] Module.End ℝ J
  unit : J
  unit_left : ∀ x, L unit x = x
  unit_trace : ⟪unit, unit⟫ = 3
  comm : ∀ x y, L x y = L y x
  assoc_inner : ∀ x y z, ⟪L x y, z⟫ = ⟪y, L x z⟫
  jordan : ∀ x, Commute (L x) (L (L x x))

namespace TraceJordanData

variable (M : TraceJordanData J)

@[simp] theorem L_unit_right (x : J) : M.L x M.unit = x :=
  (M.comm x M.unit).trans (M.unit_left x)

@[simp] theorem L_unit : M.L M.unit = LinearMap.id := by
  ext x
  exact M.unit_left x

theorem L_injective : Function.Injective M.L := by
  intro x y h
  simpa only [L_unit_right] using LinearMap.congr_fun h M.unit

/-- The real trace functional (operatorname{tr}(x)=\langle e,x\rangle). -/
def trace : J →ₗ[ℝ] ℝ where
  toFun x := ⟪M.unit, x⟫
  map_add' _ _ := inner_add_right ..
  map_smul' _ _ := real_inner_smul_right ..

@[simp] theorem trace_unit : M.trace M.unit = 3 := M.unit_trace

/-- The literal trace-free subspace. -/
abbrev traceFree : Submodule ℝ J := LinearMap.ker M.trace

/-- The trace-free part of any element of the unital Jordan algebra. -/
def center (x : J) : M.traceFree :=
  ⟨x - (M.trace x / 3) • M.unit, by
    change M.trace (x - (M.trace x / 3) • M.unit) = 0
    rw [map_sub, map_smul, M.trace_unit, smul_eq_mul]
    ring⟩

/-- The ordinary Leibniz law on the native unital product. -/
def IsDerivation (D : Module.End ℝ J) : Prop :=
  ∀ x y, D (M.L x y) = M.L (D x) y + M.L x (D y)

/-- The full space of real trace-skew derivations of the given Jordan algebra. -/
def skewDerivations : Submodule ℝ (SkewOperator J) where
  carrier := {D | M.IsDerivation D.val}
  zero_mem' := by intro x y; simp
  add_mem' := by
    intro A B hA hB x y
    change A.val (M.L x y) + B.val (M.L x y) =
      M.L (A.val x + B.val x) y + M.L x (A.val y + B.val y)
    rw [hA x y, hB x y, map_add, LinearMap.add_apply, map_add]
    abel
  smul_mem' := by
    intro a A hA x y
    change a • A.val (M.L x y) = M.L (a • A.val x) y + M.L x (a • A.val y)
    rw [hA x y, map_smul, LinearMap.smul_apply, map_smul, smul_add]

theorem derivation_unit_zero {D : Module.End ℝ J} (hD : M.IsDerivation D) : D M.unit = 0 := by
  have h := hD M.unit M.unit
  rw [M.unit_left, L_unit_right, M.unit_left] at h
  exact add_left_cancel (show D M.unit + D M.unit = D M.unit + 0 by rw [← h, add_zero])

theorem derivation_preserves_traceFree {D : SkewOperator J} (hD : M.IsDerivation D.val)
    (x : M.traceFree) : D.val x.val ∈ M.traceFree := by
  change ⟪M.unit, D.val x.val⟫ = 0
  rw [← neg_inj, ← D.property, M.derivation_unit_zero hD, inner_zero_left, neg_zero]

/-- The common kernel of the same derivations on the actual traceless representation. -/
def fixedTraceless (T : Submodule ℝ (SkewOperator J)) : Submodule ℝ M.traceFree :=
  (fixedSpace T).comap M.traceFree.subtype

@[simp] theorem mem_fixedTraceless {T : Submodule ℝ (SkewOperator J)} (x : M.traceFree) :
    x ∈ M.fixedTraceless T ↔ ∀ D : T, D.val.val x.val = 0 :=
  mem_fixedSpace T x.val

/-- The common kernel of any derivation space is an actual unital Jordan subalgebra. -/
theorem fixedAlgebra_unital_closed {T : Submodule ℝ (SkewOperator J)} (hT : T ≤ M.skewDerivations) :
    M.unit ∈ fixedSpace T ∧
      ∀ x y, x ∈ fixedSpace T → y ∈ fixedSpace T → M.L x y ∈ fixedSpace T := by
  refine ⟨?_, ?_⟩
  · exact (mem_fixedSpace T M.unit).mpr (fun D => M.derivation_unit_zero (hT D.property))
  · intro x y hx hy
    apply (mem_fixedSpace T _).mpr
    intro D
    have hD : M.IsDerivation D.val.val := hT D.property
    rw [hD x y, (mem_fixedSpace T x).mp hx D, (mem_fixedSpace T y).mp hy D]
    simp

/-- The fixed algebra is exactly the sum of the unit line and its traceless common kernel. -/
theorem fixedAlgebra_eq_unit_sup {T : Submodule ℝ (SkewOperator J)} (hT : T ≤ M.skewDerivations) :
    fixedSpace T = (ℝ ∙ M.unit) ⊔ (M.fixedTraceless T).map M.traceFree.subtype := by
  apply le_antisymm
  · intro x hx
    apply Submodule.mem_sup.mpr
    have he := (M.fixedAlgebra_unital_closed hT).1
    have hc : M.center x ∈ M.fixedTraceless T := by
      exact (fixedSpace T).sub_mem hx ((fixedSpace T).smul_mem _ he)
    exact ⟨(M.trace x / 3) • M.unit, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
      (M.center x).val, ⟨M.center x, hc, rfl⟩, by
        change (M.trace x / 3) • M.unit + (x - (M.trace x / 3) • M.unit) = x
        abel⟩
  · apply sup_le
    · apply Submodule.span_le.mpr
      intro x hx
      have he : x = M.unit := Set.mem_singleton_iff.mp hx
      rw [he]
      exact (M.fixedAlgebra_unital_closed hT).1
    · rintro x ⟨y, hy, rfl⟩
      exact hy

/-- The traceless common kernel is closed under the centered Jordan product. -/
theorem fixedTraceless_closed {T : Submodule ℝ (SkewOperator J)} (hT : T ≤ M.skewDerivations)
    {x y : M.traceFree} (hx : x ∈ M.fixedTraceless T) (hy : y ∈ M.fixedTraceless T) :
    M.center (M.L x.val y.val) ∈ M.fixedTraceless T := by
  change M.L x.val y.val - (M.trace (M.L x.val y.val) / 3) • M.unit ∈ fixedSpace T
  have h := M.fixedAlgebra_unital_closed hT
  exact (fixedSpace T).sub_mem (h.2 _ _ hx hy) ((fixedSpace T).smul_mem _ h.1)

/-- Bracketing a derivation with multiplication by (x) gives multiplication by (Dx). -/
theorem bracket_leftMul {D : Module.End ℝ J} (hD : M.IsDerivation D) (x : J) :
    operatorBracket D (M.L x) = M.L (D x) := by
  ext y
  change D (M.L x y) - M.L x (D y) = M.L (D x) y
  rw [hD, add_sub_cancel_right]

end TraceJordanData

end

end ThirteenPlanes.Cartan
