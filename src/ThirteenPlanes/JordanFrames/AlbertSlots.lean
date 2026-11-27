module

public import AcceptedRootAtomAdapter

@[expose] public section

set_option backward.privateInPublic true

/-! Simultaneous normalization of the two specified slots by a compact Albert automorphism. -/

namespace ThirteenPlanes.JordanFrames

open AlbertSequential AlbertSequential.NativeAnalysis

noncomputable section

private theorem slot01_image (g : NativeAlbertAutomorphism)
    (hg : ∀ i, g.linearEquiv (diagAtom i) = diagAtom i) (x : Octonion) :
    g.linearEquiv (slotElem01 x) = slotElem01 ((g.linearEquiv (slotElem01 x)).2 0) := by
  rw [← peirce01_extract, ← hg 0, ← hg 1, ← g.preserves_product, ← g.preserves_product, ← map_smul]
  rw [peirce01_extract]
  rfl

private theorem slot12_image (g : NativeAlbertAutomorphism)
    (hg : ∀ i, g.linearEquiv (diagAtom i) = diagAtom i) (x : Octonion) :
    g.linearEquiv (slotElem12 x) = slotElem12 ((g.linearEquiv (slotElem12 x)).2 2) := by
  rw [← peirce12_extract, ← hg 1, ← hg 2, ← g.preserves_product, ← g.preserves_product, ← map_smul]
  rw [peirce12_extract]
  rfl

private theorem slot01_image_norm (g : NativeAlbertAutomorphism)
    (hg : ∀ i, g.linearEquiv (diagAtom i) = diagAtom i) (x : Octonion) :
    octNormSq ((g.linearEquiv (slotElem01 x)).2 0) = octNormSq x := by
  have h := congrArg g.linearEquiv (jordanMul_slotElem01_self x)
  rw [g.preserves_product, map_smul, map_add, hg, hg] at h
  conv_lhs at h => rw [slot01_image g hg x, jordanMul_slotElem01_self]
  have h₀ := congrArg (fun w : Albert => w.1 0) h
  change octNormSq _ * (1 + 0) = octNormSq x * (1 + 0) at h₀
  simpa only [add_zero, mul_one] using h₀

private theorem slot12_image_norm (g : NativeAlbertAutomorphism)
    (hg : ∀ i, g.linearEquiv (diagAtom i) = diagAtom i) (x : Octonion) :
    octNormSq ((g.linearEquiv (slotElem12 x)).2 2) = octNormSq x := by
  have h := congrArg g.linearEquiv (jordanMul_slotElem12_self x)
  rw [g.preserves_product, map_smul, map_add, hg, hg] at h
  conv_lhs at h => rw [slot12_image g hg x, jordanMul_slotElem12_self]
  have h₁ := congrArg (fun w : Albert => w.1 1) h
  change octNormSq _ * (1 + 0) = octNormSq x * (1 + 0) at h₁
  simpa only [add_zero, mul_one] using h₁

private theorem scalar_eq_one_of_unit_nonneg {r : ℝ} (hr : 0 ≤ r)
    (hn : octNormSq (octonionScalar r) = 1) : r = 1 := by
  rw [octonionScalar_eq_smul, ← octOne, octNormSq_smul, octNormSq_one, mul_one] at hn
  nlinarith

/-- The two unit off-diagonal entries can be sent simultaneously to one by an
automorphism fixing each diagonal atom. -/
theorem normalize_two_slots (x y : Octonion) (hx : octNormSq x = 1) (hy : octNormSq y = 1) :
    ∃ g : NativeAlbertAutomorphism,
      (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      g.linearEquiv (slotElem01 x) = slotElem01 octOne ∧
      g.linearEquiv (slotElem12 y) = slotElem12 octOne := by
  obtain ⟨g, hg, r, hr, hslot⟩ := exists_frameStab_slot01_real (slotElem01 x)
  have hgr : r = 1 := scalar_eq_one_of_unit_nonneg hr (by
    rw [← hslot, slot01_image_norm g hg, hx])
  have hgx : g.linearEquiv (slotElem01 x) = slotElem01 octOne := by
    rw [slot01_image g hg x, hslot, hgr]
    rfl
  let z := (g.linearEquiv (slotElem12 y)).2 2
  have hgz : g.linearEquiv (slotElem12 y) = slotElem12 z := slot12_image g hg y
  have hz : octNormSq z = 1 := (slot12_image_norm g hg y).trans hy
  obtain ⟨f, hf, hfix, t, ht, hlast⟩ := exists_frameAnd01OneStab_slot12_real (slotElem12 z)
  have hft : t = 1 := scalar_eq_one_of_unit_nonneg ht (by
    rw [← hlast, slot12_image_norm f hf, hz])
  refine ⟨f.comp g, ?_, ?_, ?_⟩
  · intro i
    change f.linearEquiv (g.linearEquiv (diagAtom i)) = diagAtom i
    rw [hg, hf]
  · change f.linearEquiv (g.linearEquiv (slotElem01 x)) = slotElem01 octOne
    rw [hgx, hfix]
  · change f.linearEquiv (g.linearEquiv (slotElem12 y)) = slotElem12 octOne
    rw [hgz, slot12_image f hf z, hlast, hft]
    rfl

theorem recovered_octNormSq (x : Octonion) :
    Glennie.octNormSq x = octNormSq x := by
  rw [octNormSq_eq_coords]
  simp only [Glennie.octNormSq, Quaternion.normSq_def']
  ring

theorem recovered_diagonalAtom (i : Fin 3) :
    recoveredCoordinateEquiv (diagAtom i) = Glennie.standardFrame i := by
  fin_cases i <;> rfl

/-- Lemma 3-normal(ii) on the compact trace carrier. -/
/- This two-slot normalization corresponds to Yokota's triality transitivity
(arXiv:0902.0431, Proposition 1.16.1 and §1.15, Theorem 1.15.1). The proof here uses
explicit frame-fixing automorphisms and then automorphisms fixing the first normalized slot. -/
theorem native_normalize_two_slots (x y : Glennie.Octonion)
    (hx : Glennie.octNormSq x = 1) (hy : Glennie.octNormSq y = 1) :
    ∃ g : Glennie.CompactAutomorphism,
      (∀ i, g.equiv (Glennie.standardFrame i) = Glennie.standardFrame i) ∧
      g.equiv (⟨0, 0, 0, x, 0, 0⟩ : Glennie.Albert) = ⟨0, 0, 0, Glennie.octScalar 1, 0, 0⟩ ∧
      g.equiv (⟨0, 0, 0, 0, 0, y⟩ : Glennie.Albert) = ⟨0, 0, 0, 0, 0, Glennie.octScalar 1⟩ := by
  obtain ⟨g, hg, h₀, h₁⟩ := normalize_two_slots x y
    ((recovered_octNormSq x).symm.trans hx) ((recovered_octNormSq y).symm.trans hy)
  refine ⟨nativeAutoToCompactAuto g, ?_, ?_, ?_⟩
  · intro i
    rw [← recovered_diagonalAtom i, nativeAutoToCompactAuto_apply,
      LinearEquiv.symm_apply_apply, hg]
  · change (nativeAutoToCompactAuto g).equiv (recoveredCoordinateEquiv (slotElem01 x)) =
      recoveredCoordinateEquiv (slotElem01 octOne)
    rw [nativeAutoToCompactAuto_apply, LinearEquiv.symm_apply_apply, h₀]
  · change (nativeAutoToCompactAuto g).equiv (recoveredCoordinateEquiv (slotElem12 y)) =
      recoveredCoordinateEquiv (slotElem12 octOne)
    rw [nativeAutoToCompactAuto_apply, LinearEquiv.symm_apply_apply, h₁]

end
end ThirteenPlanes.JordanFrames
