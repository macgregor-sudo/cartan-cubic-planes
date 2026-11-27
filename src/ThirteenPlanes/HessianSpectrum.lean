module

public import ThirteenPlanes.HessianSpectrum.Spectrum
public import ThirteenPlanes.HessianSpectrum.Dimensions
public import ThirteenPlanes.HessianSpectrum.SquaresInvariance

@[expose] public section

/-! The Hessian of the A-function at a floor cubic: decomposition, eigenvalues and multiplicities.

At a cubic `C` with `A(C) = A*` in dimension `n ≥ 1`, the space of symmetric cubics (dimension
`(n+2).choose 3`) is the orthogonal direct sum of the rotation space, the trace space and their
complement, on which the Hessian acts as `0`, `(3n+14)/(n+10)` and `1`
(`hessian_spectral_theorem`). If the infinitesimal stabilizer `{A skew : C.insert A = 0}` has
dimension `s`, the three summands have dimensions `n.choose 2 - s`, `n` and the remainder. At
`n = 26` with `s = 52` these are `273`, `26`, `2977`, and the middle eigenvalue is `23/9`. The value
`s = 52` (the derivation algebra of the exceptional Jordan algebra) is a hypothesis here. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The infinitesimal stabilizer of `C`: skew-adjoint `A` with `C.insert A = 0`. -/
def skewStabilizer (C : SymmetricCubic V) : Submodule ℝ (skewEnd V) :=
  LinearMap.ker ((insertLin C).domRestrict (skewEnd V))

theorem mem_skewStabilizer {C : SymmetricCubic V} {A : skewEnd V} :
    A ∈ skewStabilizer C ↔ C.insert (A : V →ₗ[ℝ] V) = 0 := Iff.rfl

/-- **Rank–nullity for the infinitesimal action:** `dim (rotation space) + dim (stabilizer) = n.choose 2`. -/
theorem finrank_rotationSpace_add_skewStabilizer (C : SymmetricCubic V) :
    Module.finrank ℝ (rotationSpace C) + Module.finrank ℝ (skewStabilizer C) =
      (Module.finrank ℝ V).choose 2 := by
  have h := @LinearMap.finrank_range_add_finrank_ker ℝ (skewEnd V) _ _ _ inferInstance inferInstance
    (SymmetricCubic V) inferInstance inferInstance _ ((insertLin C).domRestrict (skewEnd V))
  rw [LinearMap.range_domRestrict, finrank_skewEnd] at h
  exact h

/-- At a floor cubic the three summands have total dimension `(n+2).choose 3`. -/
theorem finrank_three_summands (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) :
    Module.finrank ℝ (rotationSpace C) + Module.finrank ℝ (traceSpace V) +
      Module.finrank ℝ (complementSpace C) = (Module.finrank ℝ V + 2).choose 3 := by
  have h1 := @Submodule.finrank_add_eq_of_isCompl ℝ (SymmetricCubic V) _ inferInstance inferInstance _
    _ _ (isCompl_complementSpace C)
  have h2 := @Submodule.finrank_sup_add_finrank_inf_eq ℝ (SymmetricCubic V) _ inferInstance
    inferInstance (rotationSpace C) (traceSpace V) _ _
  rw [rotation_inf_trace hn hfl, finrank_bot] at h2
  rw [finrank_symmetricCubic] at h1
  omega

/-- **Multiplicities, conditional form.** At a floor cubic in dimension `n ≥ 1` whose infinitesimal
stabilizer has dimension `s`, the eigenvalues `0`, `(3n+14)/(n+10)`, `1` of the Hessian have
multiplicities `n.choose 2 - s`, `n` and `(n+2).choose 3 - (n.choose 2 - s) - n`. -/
theorem hessian_multiplicities (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) {s : ℕ}
    (hs : Module.finrank ℝ (skewStabilizer C) = s) :
    Module.finrank ℝ (rotationSpace C) = (Module.finrank ℝ V).choose 2 - s ∧
    Module.finrank ℝ (traceSpace V) = Module.finrank ℝ V ∧
    Module.finrank ℝ (complementSpace C) =
      (Module.finrank ℝ V + 2).choose 3 - ((Module.finrank ℝ V).choose 2 - s) -
        Module.finrank ℝ V := by
  have h1 := finrank_rotationSpace_add_skewStabilizer C
  have h2 := finrank_three_summands hn hfl
  have h3 := finrank_traceSpace (V := V)
  refine ⟨by omega, h3, by omega⟩

theorem traceEigenvalue_twentySix : traceEigenvalue 26 = 23 / 9 := by
  norm_num [traceEigenvalue]

/-- **The F₄ point in 26 variables.** If `dim V = 26`, `A(C) = A*`, and the infinitesimal stabilizer
of `C` has dimension `52` (hypothesis `hstab`), then the space of symmetric cubics has dimension
`3276`, the skew endomorphisms `325`, and the Hessian eigenvalues `0`, `23/9`, `1` have
multiplicities `273`, `26`, `2977`. -/
theorem hessian_multiplicities_twentySix (h26 : Module.finrank ℝ V = 26) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V))
    (hstab : Module.finrank ℝ (skewStabilizer C) = 52) :
    Module.finrank ℝ (SymmetricCubic V) = 3276 ∧ Module.finrank ℝ (skewEnd V) = 325 ∧
    Module.finrank ℝ (rotationSpace C) = 273 ∧ Module.finrank ℝ (traceSpace V) = 26 ∧
    Module.finrank ℝ (complementSpace C) = 2977 ∧
    traceEigenvalue (Module.finrank ℝ V) = 23 / 9 := by
  have hn : 0 < Module.finrank ℝ V := by omega
  have hS := six_mul_finrank_symmetricCubic (V := V)
  have hK := two_mul_finrank_skewEnd (V := V)
  have hK' := finrank_skewEnd (V := V)
  have hS' := finrank_symmetricCubic (V := V)
  rw [h26] at hS hK hK' hS'
  norm_num at hS hK
  obtain ⟨hR, hT, hW⟩ := hessian_multiplicities hn hfl hstab
  rw [h26] at hR hT hW
  refine ⟨by omega, by omega, by omega, hT, by omega, by rw [h26]; exact traceEigenvalue_twentySix⟩

end

end ThirteenPlanes
