module

public import ThirteenPlanes.SphereFloor.Algebra
public import ThirteenPlanes.Quartic

@[expose] public section

/-!
# The floor identity for the A-function

For a real symmetric cubic `κ` in `N ≥ 1` variables with vanishing trace vector and scalar double
contraction, with `x = ⟨κ, κ⟩`, `x* = N(N+2)/(N+10)` and `A* = -x*/8`,

  `A(κ) - A* = (N+10)/(8N(N+2)) (x - x*)² + 2N(N+2)(N+4)(N+6) Var(U_κ)`,

where `U_κ(φ) = ‖Q_κ(φ)‖²/8` and `Var` is the variance over the unit sphere with the uniform
probability measure.
-/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace SymmetricCubic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

/-- `|S|² = 3 tr M² + 6 P` for the symmetrized quartic array `S` of a cubic (proved in the quartic
toolkit, `ThirteenPlanes.Quartic`). -/
theorem sum_sq_symmetrizedArray (h : SymmetricCubic V) :
    ∑ a, ∑ b, ∑ c, ∑ d, h.symmetrizedArray e a b c d ^ 2 =
      3 * h.doubleTraceSq + 6 * h.tetrahedron :=
  sum_sq_symmetrizedArray' e h

end SymmetricCubic

open SymmetricCubic

/-- **Floor identity.**  For a trace-free real symmetric cubic with scalar double contraction,
`A(κ) - A* = (N+10)/(8N(N+2)) (x - x*)² + 2N(N+2)(N+4)(N+6) Var(U_κ)`, with `x = ⟨κ,κ⟩`,
`x* = N(N+2)/(N+10)`, `A* = -x*/8` and `U_κ = ‖Q_κ‖²/8`. -/
theorem aFunction_floor_identity [Nontrivial V] (κ : SymmetricCubic V) (hv : κ.TraceFree)
    (hM : ∃ m : ℝ, κ.doubleContraction = m • (LinearMap.id : V →ₗ[ℝ] V)) :
    let N : ℝ := Module.finrank ℝ V
    let x := κ.tensorPairing κ
    let xStar := N * (N + 2) / (N + 10)
    aFunction κ - (-xStar / 8) =
      (N + 10) / (8 * N * (N + 2)) * (x - xStar) ^ 2 +
        2 * N * (N + 2) * (N + 4) * (N + 6) * sphereVariance (fun φ => ‖κ.squareMap φ‖ ^ 2 / 8) := by
  intro N x xStar
  obtain ⟨m, hM⟩ := hM
  let e := stdOrthonormalBasis ℝ V
  have hN : (0 : ℝ) < N := by simp only [N]; exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (Fin (Module.finrank ℝ V)) : ℝ) = N := by simp [N]
  -- the scalar is x / N
  have hx : x = m * N := by
    show κ.tensorPairing κ = _
    rw [tensorPairing_self, hM, map_smul, LinearMap.trace_id, smul_eq_mul]
  have htrM : κ.doubleTraceSq = m ^ 2 * N := by
    simp only [doubleTraceSq, hM, smul_mul_smul_comm, map_smul, smul_eq_mul]
    rw [show (LinearMap.id : V →ₗ[ℝ] V) * LinearMap.id = LinearMap.id from rfl, LinearMap.trace_id]
    ring
  set lam : ℝ := 2 * m / (N + 2) with hlam
  set S := κ.symmetrizedArray e
  have hS : IsSymmetric4 S := isSymmetric4_symmetrizedArray e κ
  have htrS : ∀ c d, ∑ t, S t t c d = 2 * m * (if c = d then 1 else 0) :=
    symmetrizedArray_trace e κ hv m hM
  have hH : IsTraceFree4 fun a b c d => S a b c d - lam * pairingArray a b c d := by
    intro c d
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htrS, pairingArray_trace, hcard, hlam]
    field_simp
    ring
  have hVar := sphereVariance_energy_of_traceFree e κ lam hH
  -- the norm of `H = S - λ Π`
  have hSPi : ∑ a, ∑ b, ∑ c, ∑ d, S a b c d * pairingArray a b c d = 6 * m * N := by
    rw [sum_mul_pairingArray hS, Finset.sum_comm]
    simp only [htrS]
    simp [N]
    ring
  have hPiPi : ∑ a, ∑ b, ∑ c, ∑ d, pairingArray (ι := Fin (Module.finrank ℝ V)) a b c d *
      pairingArray a b c d = 3 * N * (N + 2) := by
    rw [sum_mul_pairingArray isSymmetric4_pairingArray, Finset.sum_comm]
    simp only [pairingArray_trace, hcard]
    simp [N]
    ring
  have hHH : ∑ a, ∑ b, ∑ c, ∑ d, (S a b c d - lam * pairingArray a b c d) ^ 2 =
      (∑ a, ∑ b, ∑ c, ∑ d, S a b c d ^ 2) -
        2 * lam * (∑ a, ∑ b, ∑ c, ∑ d, S a b c d * pairingArray a b c d) +
        lam ^ 2 * ∑ a, ∑ b, ∑ c, ∑ d, pairingArray (ι := Fin (Module.finrank ℝ V)) a b c d *
          pairingArray a b c d := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hQ := sum_sq_symmetrizedArray e κ
  have hD : (N + 2) * (N + 4) * (N + 6) * N ≠ 0 := by positivity
  have hNc : ((Module.finrank ℝ V : ℕ) : ℝ) = N := rfl
  rw [hVar, hHH, hSPi, hPiPi, hQ, htrM]
  simp only [hNc]
  unfold aFunction
  change -(1 / 4) * x + 3 / 8 * κ.doubleTraceSq + 1 / 2 * κ.tetrahedron - -xStar / 8 = _
  rw [htrM, hx, hlam]
  simp only [xStar]
  field_simp
  ring

end

end ThirteenPlanes
