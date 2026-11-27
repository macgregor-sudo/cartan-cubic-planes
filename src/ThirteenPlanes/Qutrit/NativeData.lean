module

public import ThirteenPlanes.Peirce.FrameFormula
public import ThirteenPlanes.Shares.NativeTraceFrames

@[expose] public section

/-! Full and traceless multiplication in the compact Albert algebra. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

open RoundCubics Peirce AlbertSequential

noncomputable section

theorem native_unit_trace (x : Glennie.Albert) :
    ⟪(1 : Glennie.Albert), x⟫ = Glennie.trace x := by
  rw [Glennie.hilbert_inner_eq_native, nativeInner_one_left]

theorem native_jordan_split (x y : NativeTraceless) :
    nativeFullCubic.L (nativeTraceInclusion x) (nativeTraceInclusion y) =
      nativeTraceInclusion (nativeEqualCubic.L x y) + (⟪x, y⟫ / 3) • (1 : Glennie.Albert) := by
  change Glennie.jordan (x : Glennie.Albert) (y : Glennie.Albert) =
    Glennie.traceless (Glennie.jordan (x : Glennie.Albert) (y : Glennie.Albert)) +
      (⟪(x : Glennie.Albert), (y : Glennie.Albert)⟫ / 3) • (1 : Glennie.Albert)
  rw [Glennie.traceless, Glennie.hilbert_inner_eq_native]
  exact (sub_add_cancel _ _).symm

theorem native_traceJordanFrame {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    TraceJordanFrame nativeFullCubic (1 : Glennie.Albert) p := by
  refine ⟨fun i => (native_unit_trace (p i)).trans (hp.trace_one i),
    hp.idempotent, hp.orthogonal, ?_⟩
  simpa only [Fin.sum_univ_three] using hp.sum_unit

end

end ThirteenPlanes.JordanFrames
