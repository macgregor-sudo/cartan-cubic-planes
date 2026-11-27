module

public import ThirteenPlanes.AlbertGrading.Contrast.Bridge

@[expose] public section

/-!
# Contrasts in the Tits coordinates

Under `albertCEquiv`, the contrast `∑_{a ∈ Fin 3} ω^a p_a` of a native frame is `titsContrast` of the same frame carried to `CompactTits` by `nativeCompactTitsEquiv`, with outcomes read
in `ZMod 3` (the identity map `outcome`, `Fin 3 = ZMod 3`).
-/

open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Contrast Contrast.AlbertC Tits

namespace Contrast

theorem albertCEquiv_contrast (p : Fin 3 → Glennie.Albert) :
    albertCEquiv (contrast p) = titsContrast (fun a : ZMod 3 => nativeCompactTitsEquiv (p a)) := by
  simp only [contrast, map_sum, map_smul, albertCEquiv_ofReal]
  rfl

theorem albertCEquiv_conj_contrast (p : Fin 3 → Glennie.Albert) :
    albertCEquiv (conj (contrast p)) =
      compactInvolution (titsContrast (fun a : ZMod 3 => nativeCompactTitsEquiv (p a))) := by
  rw [albertCEquiv_conj, albertCEquiv_contrast]

/-- The other direction: a `ZMod 3`-indexed `CompactTits` family, pulled back to the native algebra. -/
theorem titsContrast_eq_albertCEquiv (q : ZMod 3 → CompactTits) :
    titsContrast q = albertCEquiv (contrast fun a : Fin 3 => nativeCompactTitsEquiv.symm (q a)) := by
  rw [albertCEquiv_contrast]
  simp only [LinearIsometryEquiv.apply_symm_apply]

/-- A native frame remains a frame after transport to `CompactTits` and indexing in `ZMod 3`. -/
theorem isTitsFrame_of_frame {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    IsTitsFrame (fun a : ZMod 3 => nativeCompactTitsEquiv (p a)) := by
  refine ⟨fun a b => ?_, fun a => ?_, ?_⟩
  · rw [← nativeCompactTitsEquiv_product]
    by_cases h : a = b
    · subst h
      rw [if_pos rfl, hp.idempotent a]
    · rw [if_neg h, hp.orthogonal a b h, map_zero]
  · rw [nativeCompactTitsEquiv_trace]; exact hp.trace_one a
  · rw [← nativeCompactTitsEquiv_one, ← hp.sum_unit, map_add, map_add]
    change ∑ a : Fin 3, nativeCompactTitsEquiv (p a) = _
    rw [Fin.sum_univ_three]

end Contrast

end

end ThirteenPlanes.AlbertGrading
