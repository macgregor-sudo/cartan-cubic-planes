module

public import ThirteenPlanes.ClosedPieces
public import ThirteenPlanes.Peirce.SlotClosedPlaneIdentification
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

set_option backward.privateInPublic true

/-! Compression of a skew derivation and the lower bound on its Gram eigenspace. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

open RoundCubics

noncomputable section

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

private theorem isometry_adjoint_apply (F : V →ₗᵢ[ℝ] W) (v : V) :
    F.adjoint (F v) = v :=
  LinearMap.congr_fun F.adjoint_comp_self' v

private theorem isometry_adjoint_recovers_range (F : V →ₗᵢ[ℝ] W) {w : W}
    (hw : w ∈ F.toLinearMap.range) : F (F.adjoint w) = w := by
  obtain ⟨v, rfl⟩ := hw
  change F (F.adjoint (F v)) = F v
  rw [isometry_adjoint_apply]

/-- The compression of two isometric embeddings is isometric along the
preimage of the intersection of their ranges, giving a Gram eigenspace lower bound. -/
theorem scaledOverlap_eigenspace_finrank (F G : V →ₗᵢ[ℝ] W) (t : ℝ) :
    let D : Module.End ℝ V := t • (F.adjoint.comp G.toLinearMap)
    Module.finrank ℝ V + Module.finrank ℝ V ≤
      Module.finrank ℝ W + Module.finrank ℝ (LinearMap.ker (D.adjoint.comp D - t ^ 2 • LinearMap.id)) := by
  dsimp only
  let R := F.toLinearMap.range ⊓ G.toLinearMap.range
  let D : Module.End ℝ V := t • (F.adjoint.comp G.toLinearMap)
  let E := LinearMap.ker (D.adjoint.comp D - t ^ 2 • LinearMap.id)
  have hker (r : R) : G.adjoint r.val ∈ E := by
    have hF : F.toLinearMap (F.adjoint r.val) = r.val :=
      isometry_adjoint_recovers_range F r.property.1
    have hG : G.toLinearMap (G.adjoint r.val) = r.val :=
      isometry_adjoint_recovers_range G r.property.2
    change ((D.adjoint.comp D - t ^ 2 • (LinearMap.id : Module.End ℝ V) : Module.End ℝ V)
      (G.adjoint r.val)) = 0
    have hD : D.adjoint = t • (G.adjoint.comp F.toLinearMap) := by
      change (LinearMap.adjoint (𝕜 := ℝ) (t • (F.adjoint.comp G.toLinearMap))) = _
      rw [map_smul, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      hD, D, map_smul, smul_smul, hG, hF, pow_two, sub_self]
  let e : R →ₗ[ℝ] E := (G.adjoint.comp R.subtype).codRestrict E hker
  have hinj : Function.Injective e := by
    intro x y hxy
    have hx := isometry_adjoint_recovers_range G x.property.2
    have hy := isometry_adjoint_recovers_range G y.property.2
    have he := congrArg (fun v : E => G v.val) hxy
    change G (G.adjoint x.val) = G (G.adjoint y.val) at he
    rw [hx, hy] at he
    exact Subtype.ext he
  have hb := LinearMap.finrank_le_finrank_of_injective hinj
  have hi := Submodule.finrank_sup_add_finrank_inf_eq F.toLinearMap.range G.toLinearMap.range
  rw [LinearMap.finrank_range_of_inj F.injective, LinearMap.finrank_range_of_inj G.injective] at hi
  have hs := Submodule.finrank_le (F.toLinearMap.range ⊔ G.toLinearMap.range)
  change Module.finrank ℝ V + Module.finrank ℝ V ≤ Module.finrank ℝ W + Module.finrank ℝ E
  change _ + Module.finrank ℝ R = _ at hi
  omega

/-- The pairing of the product of two isometric embeddings with their scalar factor. -/
theorem inner_scaledOverlap (F G : V →ₗ[ℝ] W) (a : ℝ) (x y : V) :
    ⟪(a • (F.adjoint.comp G)) x, y⟫ = a * ⟪G x, F y⟫ := by
  change ⟪a • F.adjoint (G x), y⟫ = _
  rw [real_inner_smul_left, LinearMap.adjoint_inner_left]


section Conjugation

variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- Conjugation precomposes both slots with the inverse isometry. -/
theorem scaledOverlap_conj (I : V ≃ₗᵢ[ℝ] Q) (F G : V →ₗᵢ[ℝ] W) (t : ℝ) :
    I.toLinearEquiv.conj (t • (F.adjoint.comp G.toLinearMap)) =
      t • ((F.comp I.symm.toLinearIsometry).adjoint.comp
        (G.comp I.symm.toLinearIsometry).toLinearMap) := by
  let F' := F.comp I.symm.toLinearIsometry
  let G' := G.comp I.symm.toLinearIsometry
  apply LinearMap.ext
  intro u
  obtain ⟨x, rfl⟩ := I.surjective u
  change I ((t • (F.adjoint.comp G.toLinearMap)) (I.symm (I x))) =
    (t • (F'.adjoint.comp G'.toLinearMap)) (I x)
  rw [I.symm_apply_apply]
  apply ext_inner_right ℝ
  intro v
  obtain ⟨y, rfl⟩ := I.surjective v
  rw [I.inner_map_map, inner_scaledOverlap, inner_scaledOverlap]
  change t * ⟪G x, F y⟫ = t * ⟪G (I.symm (I x)), F (I.symm (I y))⟫
  rw [I.symm_apply_apply, I.symm_apply_apply]

/-- Conjugating a skew derivation along an isometry of scaled cubics preserves
the skewness and derivation identities on the actual target cubic. -/
theorem skewDerivation_conj_of_smul_pullback (I : V ≃ₗᵢ[ℝ] Q)
    {g : SymmetricCubic V} {k : SymmetricCubic Q} {s : ℝ} (hs : s ≠ 0)
    (hI : g = s • k.pullback I.toLinearMap) (E : Module.End ℝ V)
    (hEder : ∀ x y, E (g.L x y) = g.L (E x) y + g.L x (E y))
    (hEskew : ∀ x y, ⟪E x, y⟫ = -⟪x, E y⟫) :
    let D := I.toLinearEquiv.conj E
    (∀ u v, D (k.L u v) = k.L (D u) v + k.L u (D v)) ∧
    (∀ u v, ⟪D u, v⟫ = -⟪u, D v⟫) := by
  dsimp only
  let D := I.toLinearEquiv.conj E
  have hD (x : V) : D (I x) = I (E x) := by
    change I (E (I.symm (I x))) = I (E x)
    rw [I.symm_apply_apply]
  have hp (x y : V) : I (g.L x y) = s • k.L (I x) (I y) := by
    rw [hI]
    change I (s • (k.pullback I.toLinearMap).L x y) = _
    rw [I.map_smul, Peirce.pullback_intertwines_product I rfl]
  constructor
  · intro u v
    obtain ⟨x, rfl⟩ := I.surjective u
    obtain ⟨y, rfl⟩ := I.surjective v
    change D (k.L (I x) (I y)) = k.L (D (I x)) (I y) + k.L (I x) (D (I y))
    apply smul_right_injective _ hs
    dsimp only
    rw [← D.map_smul, ← hp, hD, smul_add, hD, hD, ← hp, ← hp, ← I.map_add]
    exact congrArg I (hEder x y)
  · intro u v
    obtain ⟨x, rfl⟩ := I.surjective u
    obtain ⟨y, rfl⟩ := I.surjective v
    change ⟪D (I x), I y⟫ = -⟪I x, D (I y)⟫
    rw [hD, hD, I.inner_map_map, I.inner_map_map]
    exact hEskew x y

end Conjugation

variable {h : SymmetricCubic V} {U : Submodule ℝ V}

/-- The actual orthogonal compression of an ambient linear operator to a block. -/
def compressToBlock (U : Submodule ℝ V) (D : Module.End ℝ V) : Module.End ℝ U :=
  U.orthogonalProjectionOnto.toLinearMap.comp (D.comp U.subtype)

theorem inner_compressToBlock_left (D : Module.End ℝ V) (x y : U) :
    ⟪compressToBlock U D x, y⟫ = ⟪D x.val, y.val⟫ := by
  change ⟪U.orthogonalProjectionOnto (D x.val), y⟫ = _
  exact U.inner_orthogonalProjectionOnto_eq_of_mem_right y _

theorem compressToBlock_skew {D : Module.End ℝ V}
    (hD : ∀ x y, ⟪D x, y⟫ = -⟪x, D y⟫) (x y : U) :
    ⟪compressToBlock U D x, y⟫ = -⟪x, compressToBlock U D y⟫ := by
  calc
    _ = ⟪D x.val, y.val⟫ := inner_compressToBlock_left D x y
    _ = -⟪x.val, D y.val⟫ := hD x.val y.val
    _ = -⟪D y.val, x.val⟫ := congrArg Neg.neg (real_inner_comm (D y.val) x.val)
    _ = -⟪compressToBlock U D y, x⟫ := congrArg Neg.neg (inner_compressToBlock_left D y x).symm
    _ = _ := congrArg Neg.neg (real_inner_comm x (compressToBlock U D y))

/-- Orthogonal compression preserves the derivation rule on the actual
restricted product of a closed subspace. -/
theorem compressToBlock_derivation
    (closed : IsClosedPiece h U) {D : Module.End ℝ V}
    (hD : ∀ x y, D (h.L x y) = h.L (D x) y + h.L x (D y)) (x y : U) :
    let g := h.pullback U.subtype
    let E := compressToBlock U D
    E (g.L x y) = g.L (E x) y + g.L x (E y) := by
  dsimp only
  let g := h.pullback U.subtype
  have inner_cyclic (a b c : V) : ⟪h.L a b, c⟫ = ⟪a, h.L b c⟫ := by
    have h1 := h.L_comm a b
    rw [h1, h.L_isSymmetric b]
  have inner_cyclic' (a b c : U) : ⟪g.L a b, c⟫ = ⟪a, g.L b c⟫ := by
    have h1 := g.L_comm a b
    rw [h1, g.L_isSymmetric b]
  apply ext_inner_right ℝ
  intro z
  change ⟪compressToBlock U D (g.L x y), z⟫ =
    ⟪g.L (compressToBlock U D x) y + g.L x (compressToBlock U D y), z⟫
  rw [inner_compressToBlock_left, closedSubspace_restriction_product closed, hD, inner_add_left,
    inner_add_left, inner_cyclic, h.L_isSymmetric x.val,
    inner_cyclic', g.L_isSymmetric x, inner_compressToBlock_left,
    inner_compressToBlock_left, closedSubspace_restriction_product closed,
    closedSubspace_restriction_product closed]

end

end ThirteenPlanes.ClosedBlocks
