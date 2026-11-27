module

public import ThirteenPlanes.Qutrit.Marked
public import ThirteenPlanes.Qutrit.NativeData

@[expose] public section

/-! The generated qutrit for arbitrary frames in the compact Albert algebra. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

open RoundCubics Peirce AlbertSequential

noncomputable section

/-- Proposition qutrit on the native compact Albert algebra, including both marked frames. -/
theorem native_framePair_generated_qutrit {p q : Fin 3 → Glennie.Albert}
    (hp : Glennie.Frame p) (hq : Glennie.Frame q)
    (orth : (nativeFramePlane p).IsOrtho (nativeFramePlane q)) :
    let U := nativeFramePlane p
    let Y := nativeFramePlane q
    let W := mixedProductSpace nativeEqualCubic U Y
    let S := (U ⊔ Y) ⊔ W
    let A := framePairGenerated nativeFullCubic 1 p q
    Module.finrank ℝ W = 4 ∧ W.IsOrtho (U ⊔ Y) ∧
    (∀ (x x' : U) (y y' : Y), ⟪nativeEqualCubic.L (x : NativeTraceless) y,
      nativeEqualCubic.L (x' : NativeTraceless) y'⟫ = ((1 : ℝ) / 6 / 2) * (⟪x, x'⟫ * ⟪y, y'⟫)) ∧
    A ⊓ (ℝ ∙ (1 : Glennie.Albert))ᗮ = S.map nativeTraceInclusion.toLinearMap ∧
    ∃ (he : (1 : Glennie.Albert) ∈ A) (hc : IsClosedPiece nativeFullCubic A) (I : A ≃ₗ[ℝ] Hermitian3)
        (σ τ : Equiv.Perm (Fin 3)),
      (I ⟨1, he⟩).val = 1 ∧
      (∀ x : A, (Matrix.trace (I x).val).re = Glennie.trace (x : Glennie.Albert)) ∧
      (∀ x y : A, (I ⟨nativeFullCubic.L (x : Glennie.Albert) (y : Glennie.Albert),
        hc x.property y.property⟩).val = symmetricMatrixProduct (I x).val (I y).val) ∧
      (∀ i, (I ⟨p i, framePairGenerated_point_left p q i⟩).val = qutritMUBProjection 0 (σ i)) ∧
      (∀ i, (I ⟨q i, framePairGenerated_point_right p q i⟩).val = qutritMUBProjection 1 (τ i)) := by
  have round : IsRound nativeEqualCubic (1 / 6) := by
    refine ⟨by norm_num, fun x => ?_⟩
    rw [nativeEqualCubic_squareLaw x]
    ring
  have unit (x : Glennie.Albert) : nativeFullCubic.L 1 x = x := Glennie.jordan_unit_left x
  have orthUnit (x : NativeTraceless) : ⟪(1 : Glennie.Albert), nativeTraceInclusion x⟫ = 0 := by
    rw [native_unit_trace]
    exact x.property
  have closedP : IsClosedPiece nativeEqualCubic (nativeFramePlane p) :=
    fun _ _ hx hy => nativeFramePlane_closed hp hx hy
  have closedQ : IsClosedPiece nativeEqualCubic (nativeFramePlane q) :=
    fun _ _ hx hy => nativeFramePlane_closed hq hx hy
  let F := nativeCenteredTraceFrame hp _ rfl
  let G := nativeCenteredTraceFrame hq _ rfl
  have hF : TraceJordanFrame nativeFullCubic (1 : Glennie.Albert) F.point := native_traceJordanFrame hp
  have hG : TraceJordanFrame nativeFullCubic (1 : Glennie.Albert) G.point := native_traceJordanFrame hq
  have result := twoPlanes_generateComplexQutrit round unit orthUnit native_jordan_split F G hF hG
    orth closedP closedQ (nativeFramePlane_dimension hp) (nativeFramePlane_dimension hq)
  dsimp only at result ⊢
  obtain ⟨dimW, orthoW, gram, traceless, he, hc, I, σ, τ, hIunit, hItrace, hIprod, hIp, hIq⟩ := result
  refine ⟨dimW, orthoW, gram, traceless, he, hc, I, σ, τ, hIunit, ?_, hIprod, hIp, hIq⟩
  intro x
  exact (hItrace x).trans (native_unit_trace (x : Glennie.Albert))

end

end ThirteenPlanes.JordanFrames
