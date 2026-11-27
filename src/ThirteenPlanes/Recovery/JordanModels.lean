module

public import ThirteenPlanes.Recovery.JordanExtension
public import ThirteenPlanes.Recovery.JordanTrace
public import ThirteenPlanes.NativeFramesCarrier

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open AlbertSequential AlbertSequential.NativeAnalysis
open scoped BigOperators RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- The literal Hermitian carrier in six matrix coordinates, with the raw trace metric. -/
abbrev hermitianTraceCarrier (B : NativeJordanSubalgebra) :=
  ↥(B.carrier.map recoveredCoordinateEquiv.toLinearMap)

def hermitianCoordinates (B : NativeJordanSubalgebra) :
    B.carrier ≃ₗ[ℝ] hermitianTraceCarrier B :=
  recoveredCoordinateEquiv.submoduleMap B.carrier

theorem hermitianCoordinates_apply (B : NativeJordanSubalgebra) (x : B.carrier) :
    (hermitianCoordinates B x : Glennie.Albert) = recoveredCoordinateEquiv x.val := rfl

def hermitianUnit (B : NativeJordanSubalgebra) : hermitianTraceCarrier B :=
  hermitianCoordinates B ⟨albertUnit, B.unit_mem⟩

private theorem hermitianUnit_coe (B : NativeJordanSubalgebra) :
    (hermitianUnit B : Glennie.Albert) = 1 :=
  recoveredCoordinateEquiv_unit

theorem hermitianTrace_eq (B : NativeJordanSubalgebra) (x : hermitianTraceCarrier B) :
    ⟪hermitianUnit B, x⟫ = Glennie.trace (x : Glennie.Albert) := by
  change Glennie.inner (hermitianUnit B) x = _
  rw [hermitianUnit_coe, Glennie.inner_unit_left]

private theorem hermitianUnit_normSq (B : NativeJordanSubalgebra) :
    ⟪hermitianUnit B, hermitianUnit B⟫ = 3 := by
  rw [hermitianTrace_eq, hermitianUnit_coe, Glennie.trace_unit]

private theorem nativeB_prod_mem (B : NativeJordanSubalgebra) (x y : hermitianTraceCarrier B) :
    Glennie.jordan (x : Glennie.Albert) y ∈ B.carrier.map recoveredCoordinateEquiv.toLinearMap := by
  obtain ⟨u, rfl⟩ := (hermitianCoordinates B).surjective x
  obtain ⟨v, rfl⟩ := (hermitianCoordinates B).surjective y
  exact ⟨jordanMul u.val v.val, B.product_mem _ u.property _ v.property,
    recoveredCoordinateEquiv_jordanMul _ _⟩

def hermitianJordanProduct (B : NativeJordanSubalgebra) :
    hermitianTraceCarrier B →ₗ[ℝ] hermitianTraceCarrier B →ₗ[ℝ] hermitianTraceCarrier B :=
  let e := (B.carrier.map recoveredCoordinateEquiv.toLinearMap).subtype
  (Glennie.jordanLinear.compl₁₂ e e).codRestrict₂ e Subtype.val_injective
    (fun x y => ⟨⟨Glennie.jordan x y, nativeB_prod_mem B x y⟩, rfl⟩)

private theorem hermitianJordanProduct_coe (B : NativeJordanSubalgebra) (x y : hermitianTraceCarrier B) :
    (hermitianJordanProduct B x y : Glennie.Albert) = Glennie.jordan x y := by
  let e := (B.carrier.map recoveredCoordinateEquiv.toLinearMap).subtype
  exact LinearMap.codRestrict₂_apply (Glennie.jordanLinear.compl₁₂ e e) e _ _ x y

theorem hermitianCoordinates_product (B : NativeJordanSubalgebra) (x y : B.carrier) :
    hermitianCoordinates B ⟨jordanMul x.val y.val, B.product_mem _ x.property _ y.property⟩ =
      hermitianJordanProduct B (hermitianCoordinates B x) (hermitianCoordinates B y) :=
  Subtype.ext (by
    rw [hermitianCoordinates_apply, hermitianJordanProduct_coe, hermitianCoordinates_apply,
      hermitianCoordinates_apply, recoveredCoordinateEquiv_jordanMul])

private def hermitianFullCubic (B : NativeJordanSubalgebra) : SymmetricCubic (hermitianTraceCarrier B) :=
  SymmetricCubic.ofProduct (hermitianJordanProduct B)
    (fun x y => Subtype.ext (by
      rw [hermitianJordanProduct_coe, hermitianJordanProduct_coe, Glennie.jordan_comm]))
    (fun x y z => by
      change Glennie.inner (hermitianJordanProduct B x y) z =
        Glennie.inner (hermitianJordanProduct B x z) y
      rw [hermitianJordanProduct_coe, hermitianJordanProduct_coe]
      rw [Glennie.inner_jordan_associative, Glennie.inner_jordan_associative,
        Glennie.jordan_comm (y : Glennie.Albert) z])

private theorem hermitianFullCubic_unit (B : NativeJordanSubalgebra) (x : hermitianTraceCarrier B) :
    (hermitianFullCubic B).L (hermitianUnit B) x = x := by
  apply Subtype.ext
  change (hermitianJordanProduct B (hermitianUnit B) x : Glennie.Albert) = _
  rw [hermitianJordanProduct_coe, hermitianUnit_coe, Glennie.jordan_unit_left]

abbrev hermitianTraceZero (B : NativeJordanSubalgebra) := traceZero (hermitianUnit B)

def hermitianCartanCubic (B : NativeJordanSubalgebra) : SymmetricCubic (hermitianTraceZero B) :=
  traceCubic (hermitianFullCubic B) (hermitianUnit B)

theorem hermitianCartanCubic_apply (B : NativeJordanSubalgebra) (x y z : hermitianTraceZero B) :
    (hermitianCartanCubic B).apply x y z =
      Glennie.trace (Glennie.jordan (Glennie.jordan x.val.val y.val.val) z.val.val) := by
  unfold hermitianCartanCubic traceCubic
  rw [SymmetricCubic.pullback_apply]
  change Glennie.inner (hermitianJordanProduct B x.val y.val) z.val = _
  rw [hermitianJordanProduct_coe]
  rfl

def hermitianAutomorphism (B : NativeJordanSubalgebra) (F : JordanSubalgebraIso B B) :
    hermitianTraceCarrier B ≃ₗ[ℝ] hermitianTraceCarrier B :=
  (hermitianCoordinates B).symm.trans (F.toLinearEquiv.trans (hermitianCoordinates B))

private theorem hermitianAutomorphism_eq (B : NativeJordanSubalgebra) (F : JordanSubalgebraIso B B)
    (x : B.carrier) :
    hermitianAutomorphism B F (hermitianCoordinates B x) =
      hermitianCoordinates B (F.toLinearEquiv x) := by
  simp [hermitianAutomorphism]

private theorem hermitianAutomorphism_trace {B : NativeJordanSubalgebra}
    (diag : ∀ i : Fin 3, diagAtom i ∈ B.carrier) (F : JordanSubalgebraIso B B)
    (x : hermitianTraceCarrier B) :
    ⟪hermitianUnit B, hermitianAutomorphism B F x⟫ = ⟪hermitianUnit B, x⟫ := by
  obtain ⟨y, rfl⟩ := (hermitianCoordinates B).surjective x
  rw [hermitianAutomorphism_eq, hermitianTrace_eq, hermitianTrace_eq,
    hermitianCoordinates_apply, hermitianCoordinates_apply, recoveredCoordinateEquiv_trace,
    recoveredCoordinateEquiv_trace, jordanIso_preserves_matrixTrace diag F]

private theorem hermitianAutomorphism_product (B : NativeJordanSubalgebra)
    (F : JordanSubalgebraIso B B) (x y : hermitianTraceCarrier B) :
    hermitianAutomorphism B F (hermitianJordanProduct B x y) =
      hermitianJordanProduct B (hermitianAutomorphism B F x) (hermitianAutomorphism B F y) := by
  obtain ⟨u, rfl⟩ := (hermitianCoordinates B).surjective x
  obtain ⟨v, rfl⟩ := (hermitianCoordinates B).surjective y
  rw [← hermitianCoordinates_product, hermitianAutomorphism_eq, hermitianAutomorphism_eq,
    hermitianAutomorphism_eq, ← hermitianCoordinates_product, F.map_jordan]

private theorem hermitianAutomorphism_inner {B : NativeJordanSubalgebra}
    (diag : ∀ i : Fin 3, diagAtom i ∈ B.carrier) (F : JordanSubalgebraIso B B)
    (x y : hermitianTraceCarrier B) :
    ⟪hermitianAutomorphism B F x, hermitianAutomorphism B F y⟫ = ⟪x, y⟫ := by
  have hpair (u v : hermitianTraceCarrier B) :
      ⟪u, v⟫ = ⟪hermitianUnit B, hermitianJordanProduct B u v⟫ := by
    rw [hermitianTrace_eq]
    change Glennie.inner u v = Glennie.trace (hermitianJordanProduct B u v)
    rw [hermitianJordanProduct_coe]
    rfl
  rw [hpair (hermitianAutomorphism B F x), ← hermitianAutomorphism_product,
    hermitianAutomorphism_trace diag F, ← hpair]

private def fromHermitianAutomorphism (B : NativeJordanSubalgebra)
    (F : hermitianTraceCarrier B ≃ₗ[ℝ] hermitianTraceCarrier B)
    (hu : F (hermitianUnit B) = hermitianUnit B)
    (hp : ∀ x y, F (hermitianJordanProduct B x y) = hermitianJordanProduct B (F x) (F y)) :
    JordanSubalgebraIso B B where
  toLinearEquiv := (hermitianCoordinates B).trans (F.trans (hermitianCoordinates B).symm)
  map_unit := by
    apply (hermitianCoordinates B).injective
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    exact hu
  map_jordan := by
    intro x y
    apply (hermitianCoordinates B).injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [hermitianCoordinates_product, hp, hermitianCoordinates_product,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

private theorem fromHermitianAutomorphism_eq (B : NativeJordanSubalgebra)
    (F : hermitianTraceCarrier B ≃ₗ[ℝ] hermitianTraceCarrier B)
    (hu : F (hermitianUnit B) = hermitianUnit B)
    (hp : ∀ x y, F (hermitianJordanProduct B x y) = hermitianJordanProduct B (F x) (F y)) :
    hermitianAutomorphism B (fromHermitianAutomorphism B F hu hp) = F := by
  apply LinearEquiv.ext
  intro x
  simp only [hermitianAutomorphism, fromHermitianAutomorphism,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- On each actual Hermitian matrix model, cubic symmetries are restrictions of the
unital Jordan automorphisms. These automorphisms preserve the matrix trace automatically. -/
theorem hermitianCartan_stabilizer_iff (k : CDLevel)
    (g : OrthogonalMap (hermitianTraceZero (H3Subalgebra k))) :
    cubicPreserved (hermitianCartanCubic (H3Subalgebra k)) g ↔
    ∃ F : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k),
      ∀ x : hermitianTraceZero (H3Subalgebra k),
        hermitianAutomorphism (H3Subalgebra k) F x.val = (g x).val := by
  let B := H3Subalgebra k
  have ht := traceCubic_stabilizer_iff (hermitianUnit_normSq B) (hermitianFullCubic_unit B) g
  constructor
  · intro hg
    obtain ⟨F, hu, hp, _, hg⟩ := ht.mp hg
    change ∀ x y, F (hermitianJordanProduct B x y) = hermitianJordanProduct B (F x) (F y) at hp
    refine ⟨fromHermitianAutomorphism B F hu hp, ?_⟩
    rw [fromHermitianAutomorphism_eq]
    exact hg
  · rintro ⟨F, hF⟩
    have hu : hermitianAutomorphism B F (hermitianUnit B) = hermitianUnit B := by
      rw [hermitianUnit, hermitianAutomorphism_eq, F.map_unit]
    exact ht.mpr ⟨hermitianAutomorphism B F, hu, hermitianAutomorphism_product B F,
      hermitianAutomorphism_trace (diagAtom_mem_H3Subalgebra k) F, hF⟩

/-- Each unital Jordan automorphism acts isometrically on the actual trace kernel. -/
theorem hermitianAutomorphism_restricts (k : CDLevel)
    (F : JordanSubalgebraIso (H3Subalgebra k) (H3Subalgebra k)) :
    ∃ g : OrthogonalMap (hermitianTraceZero (H3Subalgebra k)),
      cubicPreserved (hermitianCartanCubic (H3Subalgebra k)) g ∧
      ∀ x : hermitianTraceZero (H3Subalgebra k),
        hermitianAutomorphism (H3Subalgebra k) F x.val = (g x).val := by
  let B := H3Subalgebra k
  let A := hermitianAutomorphism B F
  have ht := hermitianAutomorphism_trace (diagAtom_mem_H3Subalgebra k) F
  let f : hermitianTraceZero B →ₗ[ℝ] hermitianTraceZero B :=
    (A.toLinearMap.comp (hermitianTraceZero B).subtype).codRestrict (hermitianTraceZero B) (by
      intro x
      change ⟪hermitianUnit B, A (x : hermitianTraceCarrier B)⟫ = 0
      rw [ht, traceZero_inner])
  have hn (x : hermitianTraceZero B) : ‖f x‖ = ‖x‖ := by
    change ‖A (x : hermitianTraceCarrier B)‖ = ‖(x : hermitianTraceCarrier B)‖
    rw [← Real.sqrt_sq (norm_nonneg (A (x : hermitianTraceCarrier B))),
      ← Real.sqrt_sq (norm_nonneg (x : hermitianTraceCarrier B)), ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, hermitianAutomorphism_inner (diagAtom_mem_H3Subalgebra k) F]
  let fi : hermitianTraceZero B →ₗᵢ[ℝ] hermitianTraceZero B := ⟨f, hn⟩
  let g := LinearIsometryEquiv.ofSurjective fi (LinearMap.surjective_of_injective (f := f) fi.injective)
  exact ⟨g, (hermitianCartan_stabilizer_iff k g).mpr ⟨F, fun _ => rfl⟩, fun _ => rfl⟩

end
end ThirteenPlanes.RoundCubics
