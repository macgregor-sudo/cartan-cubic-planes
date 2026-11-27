module

public import SubalgebraCoordsAndLine
public import NativeIdempotentClassification

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open AlbertSequential AlbertSequential.NativeAnalysis
open scoped BigOperators

private theorem albertTrace_sum (p : Fin 3 → Albert) :
    albertTrace (∑ i, p i) = ∑ i, albertTrace (p i) := by
  simp only [Fin.sum_univ_three, albertTrace_add]

private theorem tracePairing_sum (p : Fin 3 → Albert) (x : Albert) :
    tracePairing (∑ i, p i) x = ∑ i, tracePairing (p i) x := by
  simp only [Fin.sum_univ_three, tracePairing_add_left]

/-- A unital Jordan isomorphism sends the entire diagonal frame to trace-one atoms.
Peirce compression then recovers the trace of every element. -/
theorem jordanIso_preserves_matrixTrace {B C : NativeJordanSubalgebra}
    (diag : ∀ i : Fin 3, diagAtom i ∈ B.carrier) (F : JordanSubalgebraIso B C)
    (x : B.carrier) : albertTrace (F.toLinearEquiv x).val = albertTrace x.val := by
  let b (i : Fin 3) : B.carrier := ⟨diagAtom i, diag i⟩
  let q (i : Fin 3) : Albert := (F.toLinearEquiv (b i)).val
  have hb : ∑ i, b i = ⟨albertUnit, B.unit_mem⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact diagAtom_sum_eq_unit
  have hq : ∑ i, q i = albertUnit := by
    have hs := congrArg F.toLinearEquiv hb
    rw [map_sum, F.map_unit] at hs
    simpa only [Submodule.coe_sum] using congrArg Subtype.val hs
  have hq_nonzero (i : Fin 3) : q i ≠ 0 := by
    intro hz
    have hzi : F.toLinearEquiv (b i) = 0 := Subtype.ext hz
    have hh := F.toLinearEquiv.injective (hzi.trans (map_zero F.toLinearEquiv).symm)
    have ht := (diagAtom_isAtom i).2
    rw [show diagAtom i = 0 from congrArg Subtype.val hh, albertTrace_zero] at ht
    norm_num at ht
  have hq_idem (i : Fin 3) : jordanMul (q i) (q i) = q i := by
    have hx := F.map_jordan (b i) (b i)
    have hx' : (⟨jordanMul (b i).val (b i).val, B.product_mem _ (b i).property _ (b i).property⟩ :
        B.carrier) = b i := Subtype.ext (diagAtom_isAtom i).1
    rw [hx'] at hx
    exact (congrArg Subtype.val hx).symm
  have hq_trace_ge (i : Fin 3) : 1 ≤ albertTrace (q i) := by
    rcases native_idempotent_trace_cases (q i) (hq_idem i) with hz | hz | hz | hz
    · exact (hq_nonzero i
        ((isPositive_trace_eq_zero _ (isPositive_idempotent _ (hq_idem i))).mp hz)).elim
    · norm_num [hz]
    · norm_num [hz]
    · norm_num [hz]
  have hsum : (∑ i, albertTrace (q i)) = 3 := by
    rw [← albertTrace_sum, hq, albertTrace_unit]
  have hq_atom (i : Fin 3) : IsAtom (q i) := by
    refine ⟨hq_idem i, le_antisymm ?_ (hq_trace_ge i)⟩
    rw [Fin.sum_univ_three] at hsum
    fin_cases i
    · change albertTrace (q 0) ≤ 1
      linarith [hq_trace_ge 1, hq_trace_ge 2]
    · change albertTrace (q 1) ≤ 1
      linarith [hq_trace_ge 0, hq_trace_ge 2]
    · change albertTrace (q 2) ≤ 1
      linarith [hq_trace_ge 0, hq_trace_ge 1]
  have hcoeff (i : Fin 3) : tracePairing (q i) (F.toLinearEquiv x).val = tracePairing (b i).val x.val := by
    have hm := F.map_quadraticMap (b i) x
    obtain ⟨v, hv, hmap⟩ : ∃ v : B.carrier, v.val = quadraticMap (b i).val x.val ∧
        (F.toLinearEquiv v).val = quadraticMap (q i) (F.toLinearEquiv x).val := ⟨_, rfl, hm⟩
    have hv' : v = tracePairing (b i).val x.val • b i :=
      Subtype.ext (hv.trans (quadraticMap_atom _ _ (diagAtom_isAtom i)))
    rw [hv', map_smul, Submodule.coe_smul, quadraticMap_atom _ _ (hq_atom i)] at hmap
    exact (smul_left_injective ℝ (hq_nonzero i) hmap).symm
  have hunit (y : Albert) : tracePairing albertUnit y = albertTrace y := by
    unfold tracePairing
    rw [jordanMul_albertUnit_left]
  calc
    _ = ∑ i, tracePairing (q i) (F.toLinearEquiv x).val := by
      rw [← tracePairing_sum, hq, hunit]
    _ = ∑ i, tracePairing (diagAtom i) x.val := Finset.sum_congr rfl fun i _ => hcoeff i
    _ = albertTrace x.val := by rw [← tracePairing_sum, diagAtom_sum_eq_unit, hunit]

end ThirteenPlanes.RoundCubics
