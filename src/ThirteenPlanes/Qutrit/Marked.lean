module

public import ThirteenPlanes.Qutrit.FrameTransport
public import ThirteenPlanes.JordanFrames.ComplexPair

@[expose] public section

/-! The actual unital complex qutrit, with its two frame markings. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

noncomputable section

open RoundCubics Peirce AlbertSequential

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {h : SymmetricCubic V} {g : SymmetricCubic E} {e : E} {J : V →ₗᵢ[ℝ] E}
  {U Y : Submodule ℝ V}

/-- Proposition qutrit. The smallest unital Jordan algebra containing both frames
is a copy of the complex Hermitian algebra with the standard and Fourier frame markings. -/
theorem twoPlanes_generateComplexQutrit (round : IsRound h (1 / 6))
    (unit : ∀ x, g.L e x = x) (orthUnit : ∀ x, ⟪e, J x⟫ = 0)
    (split : ∀ x y, g.L (J x) (J y) = J (h.L x y) + (⟪x, y⟫ / 3) • e)
    (F : CenteredTraceFrame J e U) (G : CenteredTraceFrame J e Y)
    (hF : TraceJordanFrame g e F.point) (hG : TraceJordanFrame g e G.point)
    (orth : U.IsOrtho Y) (closed : IsClosedPiece h U) (closed' : IsClosedPiece h Y)
    (dim : Module.finrank ℝ U = 2) (dim' : Module.finrank ℝ Y = 2) :
    let W := mixedProductSpace h U Y
    let S := (U ⊔ Y) ⊔ W
    let A := framePairGenerated g e F.point G.point
    Module.finrank ℝ W = 4 ∧ W.IsOrtho (U ⊔ Y) ∧
    (∀ (x x' : U) (y y' : Y), ⟪h.L (x : V) y, h.L (x' : V) y'⟫ =
      ((1 : ℝ) / 6 / 2) * (⟪x, x'⟫ * ⟪y, y'⟫)) ∧
    A ⊓ (ℝ ∙ e)ᗮ = S.map J.toLinearMap ∧
    ∃ (he : e ∈ A) (hc : IsClosedPiece g A) (I : A ≃ₗ[ℝ] Hermitian3)
      (σ τ : Equiv.Perm (Fin 3)),
      (I ⟨e, he⟩).val = 1 ∧
      (∀ x : A, (Matrix.trace (I x).val).re = ⟪e, (x : E)⟫) ∧
      (∀ x y : A, (I ⟨g.L (x : E) (y : E), hc x.property y.property⟩).val =
        symmetricMatrixProduct (I x).val (I y).val) ∧
      (∀ i, (I ⟨F.point i, framePairGenerated_point_left F.point G.point i⟩).val =
        qutritMUBProjection 0 (σ i)) ∧
      (∀ i, (I ⟨G.point i, framePairGenerated_point_right F.point G.point i⟩).val =
        qutritMUBProjection 1 (τ i)) := by
  dsimp only
  obtain ⟨hW, hWortho, hGram, hTraceZero, he, hc, I, hIunit, hItrace, hIprod⟩ :=
    twoPlanes_generateComplexQutrit_unmarked round unit orthUnit split F G orth closed closed' dim dim'
  let A := framePairGenerated g e F.point G.point
  let fp := framePairGenerated_point_left (g := g) (e := e) F.point G.point
  let gp := framePairGenerated_point_right (g := g) (e := e) F.point G.point
  let F' : ComplexTraceFrame3 := transportedComplexFrame hF fp he hc I hIunit hItrace hIprod
  let G' : ComplexTraceFrame3 := transportedComplexFrame hG gp he hc I hIunit hItrace hIprod
  have hMU (i j : Fin 3) : tracePairing (F'.point i) (G'.point j) = 1 / 3 := by
    change tracePairing (I ⟨F.point i, fp i⟩).val (I ⟨G.point j, gp j⟩).val = _
    rw [tracePairing_eq_re_trace_jordan, ← hIprod, hItrace]
    change ⟪e, g.L (F.point i) (G.point j)⟫ = _
    have hi : ⟪e, g.L (F.point i) (G.point j)⟫ = ⟪F.point i, G.point j⟫ := by
      calc
        _ = ⟪g.L (F.point i) (G.point j), e⟫ := real_inner_comm _ _
        _ = ⟪G.point j, g.L (F.point i) e⟫ := g.L_isSymmetric (F.point i) _ _
        _ = _ := by rw [g.L_comm _ e, unit, real_inner_comm]
    rw [hi]
    exact traceFrame_inner_of_orthogonal orthUnit F G orth i j
  obtain ⟨D, σ, τ, hD, hD'⟩ := complex_normalize_unbiased_pair F' G' hMU
  let L : A ≃ₗ[ℝ] Hermitian3 := I.trans (complexQutritConjugation D)
  refine ⟨hW, hWortho, hGram, hTraceZero, he, hc, L, σ, τ, ?_, ?_, ?_, ?_, ?_⟩
  · exact complexQutritConjugation_unit D _ hIunit
  · intro x
    change (Matrix.trace (complexQutritConjugation D (I x)).val).re = _
    rw [complexQutritConjugation_trace, hItrace]
  · intro x y
    exact complexQutritConjugation_product D _ _ _ (hIprod x y)
  · intro i
    change (complexQutritConjugation D (I ⟨F.point i, fp i⟩)).val = _
    rw [complexQutritConjugation_coe]
    exact hD i
  · intro i
    change (complexQutritConjugation D (I ⟨G.point i, gp i⟩)).val = _
    rw [complexQutritConjugation_coe]
    exact hD' i

end

end ThirteenPlanes.JordanFrames
