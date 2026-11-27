/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.F4.ChargeAction
public import ThirteenPlanes.Cartan.AlbertOperators
public import ThirteenPlanes.Cartan.GradedActionWitness
public import ThirteenPlanes.AlbertGrading.Grading.Normalization

@[expose] public section

set_option backward.privateInPublic true

/-! Equivariance preserves each real grade plane, with scalar action for symmetric operators. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading
open scoped RealInnerProductSpace

noncomputable section

local notation "ρ" => Graded.nativeGradingHom

private abbrev chargeTraceAction (s : Charge) :=
  (albertJordanAction (nativeChargeAutomorphism s)).traceAction albertJordan

/-- Extend an endomorphism of the trace kernel by zero on the unit. -/
private def traceEndExtension (S : Module.End ℝ albertJordan.traceFree) : Module.End ℝ Glennie.Albert :=
  albertJordan.traceFree.subtype.comp (S.comp (albertTraceEquiv.symm.toLinearMap.comp nativeCenter))

private theorem traceEndExtension_apply (S : Module.End ℝ albertJordan.traceFree)
    (x : albertJordan.traceFree) : traceEndExtension S x.val = (S x).val := by
  change (S (albertTraceEquiv.symm (nativeCenter x.val))).val = _
  rw [show x.val = (albertTraceEquiv x).val from rfl, nativeCenter_of_trace_zero,
    albertTraceEquiv.symm_apply_apply]

private theorem nativeCenter_action (g : Glennie.CompactAutomorphism) (x : Glennie.Albert) :
    nativeCenter (g.equiv x) = albertTracelessAction g (nativeCenter x) := by
  apply Subtype.ext
  change Glennie.traceless (g.equiv x) = g.equiv (Glennie.traceless x)
  rw [Glennie.traceless, Glennie.traceless, g.map_trace, map_sub, map_smul, g.map_unit]

private theorem extension_commutes (S : Module.End ℝ albertJordan.traceFree)
    (hS : ∀ s x, S (chargeTraceAction s x) = chargeTraceAction s (S x)) (s : Charge) (x : Glennie.Albert) :
    traceEndExtension S (Graded.nativeCharacterAction s x) =
      Graded.nativeCharacterAction s (traceEndExtension S x) := by
  let g := nativeChargeAutomorphism s
  change (S (albertTraceEquiv.symm (nativeCenter (g.equiv x)))).val =
    g.equiv ((S (albertTraceEquiv.symm (nativeCenter x))).val)
  rw [nativeCenter_action]
  have he : albertTraceEquiv.symm (albertTracelessAction g (nativeCenter x)) =
      chargeTraceAction s (albertTraceEquiv.symm (nativeCenter x)) := by
    apply Subtype.ext
    rfl
  rw [he, hS]
  rfl

private theorem extension_mem_grade (S : Module.End ℝ albertJordan.traceFree)
    (hS : ∀ s x, S (chargeTraceAction s x) = chargeTraceAction s (S x)) {g : Charge} {z : JC}
    (hz : z ∈ charSpace ρ g) : JC.mapC (traceEndExtension S) z ∈ charSpace ρ g := by
  let L := JC.mapC (traceEndExtension S)
  intro s
  have he : act ρ s (L z) = L (act ρ s z) := by
    apply JC.ext <;>
      exact (extension_commutes S hS s _).symm
  rw [he, hz s, map_smul]

/-- Every endomorphism commuting with the native grading automorphisms preserves
the trace-kernel copy of each real character plane. -/
theorem nativeChargeEquivariant_preserves_plane (S : Module.End ℝ albertJordan.traceFree)
    (hS : ∀ s x, S (chargeTraceAction s x) = chargeTraceAction s (S x)) (p : SignedPlaneIndex)
    {x : albertJordan.traceFree}
    (hx : x ∈ (pointPlane ρ p).map albertTraceEquiv.symm.toLinearMap) :
    S x ∈ (pointPlane ρ p).map albertTraceEquiv.symm.toLinearMap := by
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨albertTraceEquiv (S (albertTraceEquiv.symm w)), ?_, albertTraceEquiv.symm_apply_apply _⟩
  change JC.of (S (albertTraceEquiv.symm w)).val ∈
    charSpace ρ p.val.val ⊔ charSpace ρ (-p.val.val)
  change JC.of w.val ∈ charSpace ρ p.val.val ⊔ charSpace ρ (-p.val.val) at hw
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hw
  let L := JC.mapC (traceEndExtension S)
  have he : L (JC.of w.val) = JC.of (S (albertTraceEquiv.symm w)).val := by
    rw [JC.mapC_of]
    exact congrArg JC.of (traceEndExtension_apply S (albertTraceEquiv.symm w))
  rw [← he, ← huv, map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (extension_mem_grade S hS hu))
    (Submodule.mem_sup_right (extension_mem_grade S hS hv))

private theorem extension_inner_symmetric (S : Module.End ℝ albertJordan.traceFree)
    (hSymm : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫) (u v : Glennie.Albert) :
    Glennie.inner (traceEndExtension S u) v = Glennie.inner u (traceEndExtension S v) := by
  let x := albertTraceEquiv.symm (nativeCenter u)
  let y := albertTraceEquiv.symm (nativeCenter v)
  change Glennie.inner (S x).val v = Glennie.inner u (S y).val
  rw [Glennie.inner_comm (S x).val v]
  change Glennie.inner v ((albertTraceEquiv (S x)).val) =
    Glennie.inner u ((albertTraceEquiv (S y)).val)
  rw [← nativeInner_center_left v (albertTraceEquiv (S x)),
    ← nativeInner_center_left u (albertTraceEquiv (S y)), Glennie.inner_comm]
  have h := hSymm x y
  change ⟪(S x).val, y.val⟫ = ⟪x.val, (S y).val⟫ at h
  rw [Glennie.hilbert_inner_eq_native, Glennie.hilbert_inner_eq_native] at h
  exact h

private theorem extension_ip_symmetric (S : Module.End ℝ albertJordan.traceFree)
    (hSymm : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫) (u v : JC) :
    JC.ip (JC.mapC (traceEndExtension S) u) v =
      JC.ip u (JC.mapC (traceEndExtension S) v) := by
  apply Complex.ext <;>
    simp only [JC.ip_re, JC.ip_im, JC.mapC_re, JC.mapC_im, extension_inner_symmetric S hSymm]

/-- A symmetric charge-equivariant endomorphism is a real scalar on each
traceless plane belonging to a pair of opposite nonzero characters. -/
theorem nativeChargeEquivariant_symmetric_scalar_on_plane (S : Module.End ℝ albertJordan.traceFree)
    (hS : ∀ s x, S (chargeTraceAction s x) = chargeTraceAction s (S x))
    (hSymm : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫) (p : SignedPlaneIndex) :
    ∃ a : ℝ, ∀ x ∈ (pointPlane ρ p).map albertTraceEquiv.symm.toLinearMap, S x = a • x := by
  let g := p.val.val
  let L := JC.mapC (traceEndExtension S)
  have hρ := nativeGradingHom_isTernaryGrading
  obtain ⟨u, hu, hun⟩ := exists_normalized hρ p.val.property
  have hub : JC.conj u ∈ charSpace ρ (-g) := conj_mem_charSpace hu
  have hu0 := ne_zero_of_normalized hun
  obtain ⟨c, hc⟩ := exists_smul_of_mem hρ hu hu0 (extension_mem_grade S hS hu)
  change L u = c • u at hc
  have hcb : L (JC.conj u) = star c • JC.conj u := by
    rw [JC.mapC_conj, hc, JC.conj_smul]
  have hpair : JC.ip u (JC.conj u) = 3 := by
    rw [← JC.mul_one (JC.conj u), ← JC.ip_mul_assoc, hun.2, JC.ip_one_one]
  have hcs := extension_ip_symmetric S hSymm u (JC.conj u)
  change JC.ip (L u) (JC.conj u) = JC.ip u (L (JC.conj u)) at hcs
  rw [hc, hcb, JC.ip_smul_left, JC.ip_smul_right, hpair] at hcs
  have hstar : c = star c := mul_right_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) hcs
  have hreal : c = (c.re : ℂ) := by
    have hi := congrArg Complex.im hstar
    change c.im = -c.im at hi
    exact Complex.ext (Complex.ofReal_re c.re).symm (by rw [Complex.ofReal_im]; linarith)
  refine ⟨c.re, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  change JC.of w.val ∈ charSpace ρ g ⊔ charSpace ρ (-g) at hw
  obtain ⟨v, hv, z, hz, hvz⟩ := Submodule.mem_sup.mp hw
  obtain ⟨d, rfl⟩ := exists_smul_of_mem hρ hu hu0 hv
  obtain ⟨e, rfl⟩ := exists_smul_of_mem hρ hub (conj_ne_zero hu0) hz
  have he : L (JC.of w.val) = c • JC.of w.val := by
    rw [← hvz, map_add, map_smul, map_smul, hc, hcb, ← hstar, smul_add,
      smul_comm d c, smul_comm e c]
  have hw' : L (JC.of w.val) = JC.of (S (albertTraceEquiv.symm w)).val := by
    rw [JC.mapC_of]
    exact congrArg JC.of (traceEndExtension_apply S (albertTraceEquiv.symm w))
  apply Subtype.ext
  apply JC.of_injective
  change JC.of (S (albertTraceEquiv.symm w)).val = JC.of (c.re • w.val)
  rw [← hw', he, JC.of_smul, hreal]
  rfl

end
end ThirteenPlanes.Cartan
