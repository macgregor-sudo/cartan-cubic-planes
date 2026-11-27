module

public import SubalgebraCoordsAndLine

@[expose] public section

set_option backward.privateInPublic true

/-! A six-dimensional native unital subalgebra with a frame and a balanced atom is a real window. -/

namespace ThirteenPlanes.ClosedBlocks

open AlbertSequential

noncomputable section

private def transportSubalgebra (B : NativeJordanSubalgebra) (g : NativeAlbertAutomorphism) :
    NativeJordanSubalgebra where
  carrier := B.carrier.map g.linearEquiv.toLinearMap
  unit_mem := ⟨albertUnit, B.unit_mem, g.preserves_unit⟩
  product_mem := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨jordanMul x y, B.product_mem x hx y hy, g.preserves_product x y⟩

private theorem balanced_slots {p : Albert} (hp : IsAtom p)
    (hdiag : ∀ i, p.1 i = 1 / 3) :
    octNormSq (p.2 0) = 1 / 9 ∧ octNormSq (p.2 2) = 1 / 9 := by
  have h0 := congrArg (fun a : Albert => a.1 0) hp.1
  have h1 := congrArg (fun a : Albert => a.1 1) hp.1
  have h2 := congrArg (fun a : Albert => a.1 2) hp.1
  rw [jordanMul_diag_0, octDot_self, octDot_self, hdiag 0] at h0
  rw [jordanMul_diag_1, octDot_self, octDot_self, hdiag 1] at h1
  rw [jordanMul_diag_2, octDot_self, octDot_self, hdiag 2] at h2
  constructor <;> linarith only [h0, h1, h2]

private theorem standardReal_le (B : NativeJordanSubalgebra) (d : ∀ i, diagAtom i ∈ B.carrier)
    (s01 : slotElem01 octOne ∈ B.carrier) (s12 : slotElem12 octOne ∈ B.carrier) :
    (H3Subalgebra .R).carrier ≤ B.carrier := by
  have s02 := slotElem01_mem_02_of_mem (B := B) s12 s01
  intro x hx
  obtain ⟨h0, h1, h2⟩ := hx
  have hreal {o : Octonion} (ho : o ∈ octRealSubalgebra.carrier) : ∃ r : ℝ, o = r • octOne := by
    obtain ⟨r, rfl⟩ := (assocCD_R.range_embed ▸ ho : o ∈ LinearMap.range assocCD_R.embed)
    refine ⟨r, ?_⟩
    change octonionScalar r = _
    rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
  obtain ⟨r0, hr0⟩ := hreal h0
  obtain ⟨r1, hr1⟩ := hreal h1
  obtain ⟨r2, hr2⟩ := hreal h2
  have hx' : x = x.1 0 • diagAtom 0 + x.1 1 • diagAtom 1 + x.1 2 • diagAtom 2 +
      (slotElem01 (r0 • octOne) + slotElem02 (r1 • octOne) + slotElem12 (r2 • octOne)) := by
    rw [← hr0, ← hr1, ← hr2]
    have add₁ (a b : Albert) (i : Fin 3) : (a + b).1 i = a.1 i + b.1 i := rfl
    have add₂ (a b : Albert) (i : Fin 3) : (a + b).2 i = a.2 i + b.2 i := rfl
    have smul₁ (r : ℝ) (a : Albert) (i : Fin 3) : (r • a).1 i = r * a.1 i := rfl
    have smul₂ (r : ℝ) (a : Albert) (i : Fin 3) : (r • a).2 i = r • a.2 i := rfl
    apply Prod.ext
    · funext i
      simp only [add₁, smul₁]
      fin_cases i <;> norm_num [diagAtom, slotElem01, slotElem02, slotElem12, upperSlot]
    · funext i
      simp only [add₂, smul₂]
      fin_cases i <;> norm_num [diagAtom, slotElem01, slotElem02, slotElem12, upperSlot]
  rw [hx', map_smul, map_smul, map_smul]
  exact B.carrier.add_mem
    (B.carrier.add_mem (B.carrier.add_mem (B.carrier.smul_mem _ (d 0)) (B.carrier.smul_mem _ (d 1)))
      (B.carrier.smul_mem _ (d 2)))
    (B.carrier.add_mem (B.carrier.add_mem (B.carrier.smul_mem _ s01) (B.carrier.smul_mem _ s02))
      (B.carrier.smul_mem _ s12))

/-- A framed six-dimensional native subalgebra containing an atom with all frame overlaps
one third is conjugate to the real symmetric window. -/
theorem nativeFramedRealWindow_to_standard (B : NativeJordanSubalgebra)
    (dim : Module.finrank ℝ B.carrier = 6)
    (F : NativeJordanFrame) (hF : ∀ i, F.atom i ∈ B.carrier)
    (p : Albert) (hp : IsAtom p) (hpB : p ∈ B.carrier)
    (balanced : ∀ i, tracePairing (F.atom i) p = 1 / 3) :
    ∃ g : NativeAlbertAutomorphism, ∀ x : Albert,
      g.linearEquiv x ∈ (H3Subalgebra .R).carrier ↔ x ∈ B.carrier := by
  let : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → (Quaternion ℝ × Quaternion ℝ))))
  obtain ⟨a, ha⟩ := native_frame_to_standardFrame F
  have diag (g : NativeAlbertAutomorphism) (hg : ∀ i, g.linearEquiv (F.atom i) = diagAtom i) :
      ∀ i, (g.linearEquiv p).1 i = 1 / 3 := by
    intro i
    rw [← tracePairing_diagAtom, ← hg i, g.map_tracePairing, balanced]
  obtain ⟨b, hb, r, _, hr⟩ := exists_frameStab_slot01_real (a.linearEquiv p)
  let k := b.comp a
  have hk (i : Fin 3) : k.linearEquiv (F.atom i) = diagAtom i := by
    change b.linearEquiv (a.linearEquiv (F.atom i)) = _
    rw [ha, hb]
  let C := transportSubalgebra B k
  have cd (i : Fin 3) : diagAtom i ∈ C.carrier := ⟨F.atom i, hF i, hk i⟩
  have cp : k.linearEquiv p ∈ C.carrier := ⟨p, hpB, rfl⟩
  have cslot : slotElem01 ((k.linearEquiv p).2 0) ∈ C.carrier := by
    rw [← peirce01_extract]
    exact C.carrier.smul_mem _ (C.product_mem _ (cd 0) _ (C.product_mem _ (cd 1) _ cp))
  have n₀ := (balanced_slots (k.map_isAtom hp) (diag k hk)).1
  change (k.linearEquiv p).2 0 = octonionScalar r at hr
  rw [hr, octonionScalar_eq_smul, ← octOne_eq_scalar, octNormSq_smul, octNormSq_one, mul_one] at n₀
  have rne : r ≠ 0 := by intro h; norm_num [h] at n₀
  have c01 : slotElem01 octOne ∈ C.carrier := by
    rw [hr, octonionScalar_eq_smul, ← octOne_eq_scalar, map_smul] at cslot
    simpa only [smul_smul, inv_mul_cancel₀ rne, one_smul] using C.carrier.smul_mem r⁻¹ cslot
  obtain ⟨c, hc, hc01, s, _, hs⟩ := exists_frameAnd01OneStab_slot12_real (k.linearEquiv p)
  let g := c.comp k
  let D := transportSubalgebra B g
  have hg (i : Fin 3) : g.linearEquiv (F.atom i) = diagAtom i := by
    change c.linearEquiv (k.linearEquiv (F.atom i)) = _
    rw [hk, hc]
  have dd (i : Fin 3) : diagAtom i ∈ D.carrier := ⟨F.atom i, hF i, hg i⟩
  have d01 : slotElem01 octOne ∈ D.carrier := by
    obtain ⟨x, hx, h⟩ := c01
    exact ⟨x, hx, (congrArg c.linearEquiv h).trans hc01⟩
  have dp : g.linearEquiv p ∈ D.carrier := ⟨p, hpB, rfl⟩
  have dslot : slotElem12 ((g.linearEquiv p).2 2) ∈ D.carrier := by
    rw [← peirce12_extract]
    exact D.carrier.smul_mem _ (D.product_mem _ (dd 1) _ (D.product_mem _ (dd 2) _ dp))
  have n₂ := (balanced_slots (g.map_isAtom hp) (diag g hg)).2
  change (g.linearEquiv p).2 2 = octonionScalar s at hs
  rw [hs, octonionScalar_eq_smul, ← octOne_eq_scalar, octNormSq_smul, octNormSq_one, mul_one] at n₂
  have sne : s ≠ 0 := by intro h; norm_num [h] at n₂
  have d12 : slotElem12 octOne ∈ D.carrier := by
    rw [hs, octonionScalar_eq_smul, ← octOne_eq_scalar, map_smul] at dslot
    simpa only [smul_smul, inv_mul_cancel₀ sne, one_smul] using D.carrier.smul_mem s⁻¹ dslot
  have dimD : Module.finrank ℝ D.carrier = 6 :=
    (LinearEquiv.finrank_map_eq g.linearEquiv B.carrier).trans dim
  have eq := Submodule.eq_of_le_of_finrank_eq (standardReal_le D dd d01 d12)
    ((finrank_H3Subalgebra .R).trans dimD.symm)
  refine ⟨g, fun x => ?_⟩
  rw [eq]
  constructor
  · rintro ⟨y, hy, h⟩
    exact g.linearEquiv.injective h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end

end ThirteenPlanes.ClosedBlocks
