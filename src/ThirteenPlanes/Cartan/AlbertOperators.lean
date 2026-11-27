module

public import ThirteenPlanes.Cartan.AlbertInvariant
public import ThirteenPlanes.Cartan.JordanAction
public import ThirteenPlanes.Cartan.OperatorFrames
public import ThirteenPlanes.JordanFrames.Albert

@[expose] public section

set_option backward.privateInPublic true

/-! The section 7 operators on the actual compact Albert representation. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- Identify the trace kernel of the Cartesian Jordan model with the established native carrier. -/
def albertTraceEquiv : albertJordan.traceFree ≃ₗᵢ[ℝ] NativeTraceless :=
  LinearIsometryEquiv.ofEq _ _ albertJordan_traceFree_eq

@[simp] theorem albertTraceEquiv_val (x : albertJordan.traceFree) :
    (albertTraceEquiv x).val = x.val := rfl

/-- The actual compact Albert automorphisms as Jordan trace isometries. -/
def albertJordanAction (g : Glennie.CompactAutomorphism) : albertJordan.Automorphism where
  action :=
    { g.equiv with
      norm_map' := fun x => (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
        rw [Glennie.native_norm_sq, Glennie.native_norm_sq, g.inner_map]) }
  unit_fixed := g.map_unit
  product_map := g.map_jordan

private theorem albert_action_commutes (g : Glennie.CompactAutomorphism)
    (x : albertJordan.traceFree) :
    albertTraceEquiv ((albertJordanAction g).traceAction albertJordan x) =
      albertTracelessAction g (albertTraceEquiv x) := by
  apply Subtype.ext
  rfl

/-- Every operator commuting with the actual compact Albert action on the trace kernel is scalar. -/
/- The paper uses Gabriele Höhn's description of invariant polynomials on the trace-zero
Albert algebra (arXiv:2609.25086, Lemma 5.1, p. 21). This theorem proves scalarity
of the commutant by transporting the concrete native Albert action. -/
theorem albertJordan_commuting_eq_smul_id (S : Module.End ℝ albertJordan.traceFree)
    (hS : ∀ (g : Glennie.CompactAutomorphism) (x : albertJordan.traceFree),
      S ((albertJordanAction g).traceAction albertJordan x) =
        (albertJordanAction g).traceAction albertJordan (S x)) :
    ∃ a : ℝ, S = a • LinearMap.id := by
  let f := albertTraceEquiv.toLinearEquiv
  obtain ⟨a, ha⟩ := albert_commuting_eq_smul_id (f.conj S) (by
    intro g x
    obtain ⟨x, rfl⟩ := albertTraceEquiv.surjective x
    rw [← albert_action_commutes]
    change albertTraceEquiv (S (albertTraceEquiv.symm
        (albertTraceEquiv ((albertJordanAction g).traceAction albertJordan x)))) =
      albertTracelessAction g (albertTraceEquiv (S (albertTraceEquiv.symm (albertTraceEquiv x))))
    rw [albertTraceEquiv.symm_apply_apply, albertTraceEquiv.symm_apply_apply,
      hS, albert_action_commutes])
  refine ⟨a, LinearMap.ext fun x => albertTraceEquiv.injective ?_⟩
  have hx := LinearMap.congr_fun ha (albertTraceEquiv x)
  change albertTraceEquiv (S (albertTraceEquiv.symm (albertTraceEquiv x))) =
    a • albertTraceEquiv x at hx
  rw [albertTraceEquiv.symm_apply_apply] at hx
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, map_smul] using hx

/-- The native Albert derivation operators on the traceless representation, with the paper's metric. -/
abbrev albertDerivationOperators : Submodule ℝ (SkewOperator albertJordan.traceFree) :=
  LinearMap.range albertJordan.restrictDerivation

/-- The full compact Albert Casimir has the exact trace-normalized dimension ratio. -/
theorem albertFullCasimir :
    operatorCasimir albertDerivationOperators =
      (Module.finrank ℝ albertDerivationOperators / (26 : ℝ)) • LinearMap.id := by
  have hn : Module.finrank ℝ albertJordan.traceFree = 26 :=
    albertTraceEquiv.toLinearEquiv.finrank_eq.trans nativeTraceless_finrank
  have h := fullCasimir_eq_finrank_div
    (fun g : Glennie.CompactAutomorphism => (albertJordanAction g).traceAction albertJordan)
    albertDerivationOperators (by rw [hn]; decide)
    (fun g => (albertJordanAction g).normalizes_restrictedDerivations albertJordan)
    albertJordan_commuting_eq_smul_id
  simpa only [hn, Nat.cast_ofNat] using h

/-- Lift a native ordered Albert frame into the actual trace-kernel operator model. -/
def albertJordanFrame {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) : albertJordan.Frame where
  point := p
  trace_one a := (albertJordan_trace (p a)).trans (hp.trace_one a)
  mul_point a b := by
    change Glennie.jordan (p a) (p b) = _
    split_ifs with hab
    · subst b
      exact hp.idempotent a
    · exact hp.orthogonal a b hab
  sum_unit := by
    change (∑ a, p a) = (1 : Glennie.Albert)
    simpa only [Fin.sum_univ_three] using hp.sum_unit

private theorem albert_map_traceCubic_L (x y : albertJordan.traceFree) :
    albertTraceEquiv (albertJordan.traceCubic.L x y) =
      nativeEqualCubic.L (albertTraceEquiv x) (albertTraceEquiv y) := by
  apply Subtype.ext
  rw [albertJordan.traceCubic_L]
  change Glennie.jordan x.val y.val - (albertJordan.trace (Glennie.jordan x.val y.val) / 3) • 1 =
    ((nativeEqualCubic.L (albertTraceEquiv x) (albertTraceEquiv y)) : Glennie.Albert)
  simp only [albertJordan_trace, nativeEqualCubic, SymmetricCubic.L_ofProduct,
    nativeCenteredJordan_apply, nativeCenter_coe, Glennie.traceless, albertTraceEquiv_val]

private theorem albertJordanFrame_plane {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    ((albertJordanFrame hp).plane albertJordan).map albertTraceEquiv.toLinearMap =
      nativeFramePlane p := by
  rw [JordanFrames.native_framePlane_eq_centered_span hp, TraceJordanData.Frame.plane, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext a
  apply Subtype.ext
  change p a - (albertJordan.trace (p a) / 3) • 1 = _
  rw [albertJordan_trace]
  rfl

/-- Each actual closed two-plane in the compact Albert carrier is a native frame plane. -/
theorem albertJordan_closedPlane_has_frame (U : Submodule ℝ albertJordan.traceFree)
    (hd : Module.finrank ℝ U = 2) (hc : IsClosedPiece albertJordan.traceCubic U) :
    ∃ F : albertJordan.Frame, U = F.plane albertJordan := by
  let W := U.map albertTraceEquiv.toLinearMap
  have hdW : Module.finrank ℝ W = 2 :=
    (albertTraceEquiv.toLinearEquiv.submoduleMap U).finrank_eq.symm.trans hd
  have hcW : IsClosedPiece nativeEqualCubic W := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    change nativeEqualCubic.L (albertTraceEquiv x) (albertTraceEquiv y) ∈ W
    rw [← albert_map_traceCubic_L]
    exact Submodule.mem_map_of_mem (hc hx hy)
  obtain ⟨p, hp, hW⟩ := nativeClosedPlane_has_frame W hdW hcW
  refine ⟨albertJordanFrame hp, ?_⟩
  apply Submodule.map_injective_of_injective albertTraceEquiv.injective
  rw [albertJordanFrame_plane hp]
  exact hW

end

end ThirteenPlanes.Cartan
