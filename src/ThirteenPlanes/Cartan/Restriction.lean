module

public import ThirteenPlanes.Cartan.OperatorTransport

@[expose] public section

set_option backward.privateInPublic true

/-! Restriction of derivations from the unital algebra to its traceless representation. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]

namespace TraceJordanData

variable (M : TraceJordanData J)

/-- Decompose an element into its scalar trace coordinate and its traceless part. -/
def unitTraceCoordinates : J ≃ₗ[ℝ] ℝ × M.traceFree where
  toFun x := (M.trace x / 3, M.center x)
  invFun p := p.1 • M.unit + p.2.val
  left_inv x := by
    change (M.trace x / 3) • M.unit + (x - (M.trace x / 3) • M.unit) = x
    abel
  right_inv p := by
    have hz : M.trace p.2.val = 0 := p.2.property
    have ht : M.trace (p.1 • M.unit + p.2.val) / 3 = p.1 := by
      rw [map_add, map_smul, M.trace_unit, hz, add_zero, smul_eq_mul]
      ring
    refine Prod.ext ht (Subtype.ext ?_)
    change p.1 • M.unit + p.2.val - (M.trace (p.1 • M.unit + p.2.val) / 3) • M.unit = p.2.val
    rw [ht]
    abel
  map_add' x y := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change M.trace (x + y) / 3 = M.trace x / 3 + M.trace y / 3
      rw [map_add]
      ring
    · change (x + y) - (M.trace (x + y) / 3) • M.unit =
        (x - (M.trace x / 3) • M.unit) + (y - (M.trace y / 3) • M.unit)
      rw [map_add, add_div, add_smul]
      abel
  map_smul' r x := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change M.trace (r • x) / 3 = r * (M.trace x / 3)
      rw [map_smul, smul_eq_mul]
      ring
    · change r • x - (M.trace (r • x) / 3) • M.unit = r • (x - (M.trace x / 3) • M.unit)
      rw [map_smul, smul_eq_mul, smul_sub, smul_smul, mul_div_assoc]

/-- A derivation acts on the literal traceless submodule, preserving trace-skewness. -/
def restrictDerivation : M.skewDerivations →ₗ[ℝ] SkewOperator M.traceFree where
  toFun D := ⟨D.val.val.restrict (fun x hx => M.derivation_preserves_traceFree D.property ⟨x, hx⟩),
    fun x y => D.val.property x.val y.val⟩
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)

omit [FiniteDimensional ℝ J] in
@[simp] theorem restrictDerivation_apply_val (D : M.skewDerivations) (x : M.traceFree) :
    ((M.restrictDerivation D).val x).val = D.val.val x.val := rfl

omit [FiniteDimensional ℝ J] in
theorem restrictDerivation_injective : Function.Injective M.restrictDerivation := by
  intro A B h
  apply Subtype.ext
  apply Subtype.ext
  ext x
  have hv := congrArg (fun D : SkewOperator M.traceFree => (D.val (M.center x)).val) h
  change A.val.val (M.center x).val = B.val.val (M.center x).val at hv
  simpa only [center, map_sub, map_smul, M.derivation_unit_zero A.property,
    M.derivation_unit_zero B.property, smul_zero, sub_zero] using hv

omit [FiniteDimensional ℝ J] in
private theorem unitTraceCoordinates_conj (D : M.skewDerivations) :
    M.unitTraceCoordinates.conj D.val.val =
      LinearMap.prodMap (0 : Module.End ℝ ℝ) (M.restrictDerivation D).val := by
  apply LinearMap.ext
  intro p
  have hz : M.trace (D.val.val p.2.val) = 0 :=
    M.derivation_preserves_traceFree D.property p.2
  have hd : D.val.val (p.1 • M.unit + p.2.val) = D.val.val p.2.val := by
    rw [map_add, map_smul, M.derivation_unit_zero D.property, smul_zero, zero_add]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · change M.trace (D.val.val (p.1 • M.unit + p.2.val)) / 3 = 0
    rw [hd, hz, zero_div]
  · change (M.center (D.val.val (p.1 • M.unit + p.2.val))).val = D.val.val p.2.val
    simp only [hd, center, hz, zero_div, zero_smul, sub_zero]

/-- The trace pairing on real derivations agrees with the trace pairing of the traceless action. -/
theorem restrictDerivation_inner (A B : M.skewDerivations) :
    ⟪M.restrictDerivation A, M.restrictDerivation B⟫ = ⟪A.val, B.val⟫ := by
  rw [skewOperator_inner, skewOperator_inner, ← LinearMap.trace_conj' (A.val.val * B.val.val)
    M.unitTraceCoordinates]
  have hc : M.unitTraceCoordinates.conj (A.val.val * B.val) =
      LinearMap.prodMap (0 : Module.End ℝ ℝ)
        ((M.restrictDerivation A).val * (M.restrictDerivation B).val) := by
    rw [conj_mul M.unitTraceCoordinates A.val.val B.val.val,
      M.unitTraceCoordinates_conj A, M.unitTraceCoordinates_conj B]
    apply LinearMap.ext
    intro p
    exact Prod.ext rfl rfl
  rw [hc, LinearMap.trace_prodMap', map_zero, zero_add]

/-- The native traceless derivation action, with its exact trace normalization. -/
def restrictDerivationIsometry : M.skewDerivations →ₗᵢ[ℝ] SkewOperator M.traceFree where
  toLinearMap := M.restrictDerivation
  norm_map' D := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact M.restrictDerivation_inner D D)

/-- Restrict any real skew derivation subspace to its traceless orthogonal representation. -/
def restrictOperators (K : Submodule ℝ (SkewOperator J)) (hK : K ≤ M.skewDerivations) :
    K →ₗᵢ[ℝ] SkewOperator M.traceFree :=
  M.restrictDerivationIsometry.comp ⟨Submodule.inclusion hK, fun _ => rfl⟩

theorem fixedTraceless_eq_fixedSpace (K : Submodule ℝ (SkewOperator J))
    (hK : K ≤ M.skewDerivations) (T : Submodule ℝ K) :
    M.fixedTraceless (T.map K.subtype) =
      fixedSpace (T.map (M.restrictOperators K hK).toLinearMap) := by
  ext x
  rw [mem_fixedTraceless, mem_fixedSpace]
  constructor
  · intro hx
    rintro ⟨_, D, hD, rfl⟩
    apply Subtype.ext
    exact hx ⟨D.val, ⟨D, hD, rfl⟩⟩
  · intro hx
    rintro ⟨_, D, hD, rfl⟩
    exact congrArg Subtype.val (hx ⟨M.restrictOperators K hK D, ⟨D, hD, rfl⟩⟩)

omit [FiniteDimensional ℝ J] in
theorem unit_disjoint_traceFree : Disjoint (ℝ ∙ M.unit) M.traceFree := by
  apply Submodule.disjoint_def.mpr
  intro x hx ht
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  change M.trace (a • M.unit) = 0 at ht
  rw [map_smul, M.trace_unit, smul_eq_mul] at ht
  have ha : a = 0 := by linarith
  rw [ha, zero_smul]

/-- Two skew derivations commute precisely when their traceless restrictions do. -/
theorem restrictOperators_commute_iff (K : Submodule ℝ (SkewOperator J))
    (hK : K ≤ M.skewDerivations) (A B : K) :
    Commute (M.restrictOperators K hK A).val (M.restrictOperators K hK B).val ↔
      Commute A.val.val B.val.val := by
  constructor
  · intro h
    change A.val.val * B.val.val = B.val.val * A.val.val
    apply LinearMap.ext
    intro x
    have hA : A.val.val x = A.val.val (M.center x).val := by
      change A.val.val x = A.val.val (x - (M.trace x / 3) • M.unit)
      simp only [map_sub, map_smul, M.derivation_unit_zero (hK A.property), smul_zero, sub_zero]
    have hB : B.val.val x = B.val.val (M.center x).val := by
      change B.val.val x = B.val.val (x - (M.trace x / 3) • M.unit)
      simp only [map_sub, map_smul, M.derivation_unit_zero (hK B.property), smul_zero, sub_zero]
    have he := congrArg Subtype.val (LinearMap.congr_fun h.eq (M.center x))
    change A.val.val (B.val.val (M.center x).val) = B.val.val (A.val.val (M.center x).val) at he
    change A.val.val (B.val.val x) = B.val.val (A.val.val x)
    rwa [hA, hB]
  · intro h
    change (M.restrictOperators K hK A).val * (M.restrictOperators K hK B).val =
      (M.restrictOperators K hK B).val * (M.restrictOperators K hK A).val
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun h.eq x.val

end TraceJordanData

end

end ThirteenPlanes.Cartan
