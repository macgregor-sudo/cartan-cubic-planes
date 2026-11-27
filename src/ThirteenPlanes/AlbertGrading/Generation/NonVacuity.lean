module

public import ThirteenPlanes.AlbertGrading.Generation.Generation
public import ThirteenPlanes.Graded.Frames

@[expose] public section

/-! Non-vacuity of the hypotheses of the two-plane subalgebra classification and generation by triples of closed planes targets. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading

open AlbertSequential

/-- A unit imaginary octonion exists, and the whole Albert algebra contains `H₃(ℂ_u)`. -/
example : ∃ u : Octonion, octonionReal u = 0 ∧ octNormSq u = 1 ∧
    ∀ x : Albert, (∀ k : Fin 3, x.2 k ∈ complexLine u) → x ∈ (⊤ : NativeJordanSubalgebra).carrier :=
  ⟨octI, rfl, by
    norm_num [octNormSq, octDot, octonionMul, octonionConj, octonionReal, octI],
    fun _ _ => trivial⟩

/-- An actual thirteen-plane system exists (the graded native code), and any two of its
frames have orthogonal frame planes. -/
example : ∃ c : TightNativeCode,
    (nativeFramePlane (c.point 0)).IsOrtho (nativeFramePlane (c.point 1)) ∧
    (nativeFramePlane (c.point 0)).IsOrtho (nativeFramePlane (c.point 2)) ∧
    (nativeFramePlane (c.point 1)).IsOrtho (nativeFramePlane (c.point 2)) :=
  ⟨Graded.nativeCode, Graded.nativeCode.planes_orthogonal (by decide),
    Graded.nativeCode.planes_orthogonal (by decide), Graded.nativeCode.planes_orthogonal (by decide)⟩

end ThirteenPlanes.AlbertGrading
