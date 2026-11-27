module

public import ThirteenPlanes.JordanFrames.AlbertNormal

@[expose] public section

set_option backward.privateInPublic true

/-! The normalized compact Albert frame in the manuscript's matrix-entry convention. -/

namespace ThirteenPlanes.JordanFrames

noncomputable section

/-- The primitive cube root in the complex slice with imaginary unit `u`. -/
def nativeCubeRoot (u : Glennie.Octonion) : Glennie.Octonion :=
  (-1 / 2 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 2) • u

/-- Powers taken by repeated octonion multiplication, starting at the real unit. -/
def nativeOctPow (a : Glennie.Octonion) : ℕ → Glennie.Octonion
  | 0 => Glennie.octScalar 1
  | m + 1 => Glennie.octMul (nativeOctPow a m) a

private theorem native_conj_neg {u : Glennie.Octonion} (hu : Glennie.octRe u = 0) :
    Glennie.octConj u = -u :=
  AlbertSequential.octonionConj_eq_neg_of_real_zero hu

private theorem native_imag_mul_self {u : Glennie.Octonion}
    (hu : Glennie.octRe u = 0) (hn : Glennie.octNormSq u = 1) :
    Glennie.octMul u u = (-1 : ℝ) • Glennie.octScalar 1 := by
  have h := AlbertSequential.octonionMul_imag_sq (u := u) hu
  have hn' := (recovered_octNormSq u).symm.trans hn
  rw [hn'] at h
  exact h

private theorem nativeCubeRoot_conj (u : Glennie.Octonion) (hu : Glennie.octRe u = 0) :
    Glennie.octConj (nativeCubeRoot u) = nativeCubeRoot (-u) := by
  simp only [nativeCubeRoot, Glennie.octConj_add, Glennie.octConj_smul,
    Glennie.octConj_scalar, native_conj_neg hu]

private theorem nativeCubeRoot_sq (u : Glennie.Octonion)
    (hu : Glennie.octRe u = 0) (hn : Glennie.octNormSq u = 1) :
    Glennie.octMul (nativeCubeRoot u) (nativeCubeRoot u) =
      Glennie.octConj (nativeCubeRoot u) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [nativeCubeRoot_conj u hu]
  simp only [nativeCubeRoot, Glennie.octMul_add_left, Glennie.octMul_add_right,
    Glennie.octMul_smul_left, Glennie.octMul_smul_right, Glennie.octMul_scalar_left,
    one_smul, Glennie.octMul_scalar_right, native_imag_mul_self hu hn, smul_smul]
  match_scalars <;> nlinarith

private theorem native_phase_scaled (u : Glennie.Octonion) :
    (nativeFourierPhase u).o01 = (1 / 3 : ℝ) • nativeCubeRoot u := by
  change (-1 / 6 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 6) • u =
    (1 / 3 : ℝ) • ((-1 / 2 : ℝ) • Glennie.octScalar 1 + (Real.sqrt 3 / 2) • u)
  module

private theorem native_scalar_third :
    Glennie.octScalar (1 / 3) = (1 / 3 : ℝ) • Glennie.octScalar 1 :=
  AlbertSequential.octonionScalar_eq_smul _

set_option maxHeartbeats 800000 in
/-- The literal entry of the Fourier frame is `ω_u ^ (k(i-j)) / 3`,
with the exponent reduced modulo three. -/
theorem nativeFourier_matrix_entry (u : Glennie.Octonion)
    (hu : Glennie.octRe u = 0) (hn : Glennie.octNormSq u = 1) (k i j : Fin 3) :
    Glennie.toMatrix (nativeFourierFrame u k) i j =
      (1 / 3 : ℝ) • nativeOctPow (nativeCubeRoot u) ((k.val * (i.val + 3 - j.val)) % 3) := by
  have hconj := nativeCubeRoot_conj u hu
  have hpow1 : nativeOctPow (nativeCubeRoot u) 1 = nativeCubeRoot u := by
    simp [nativeOctPow]
  have hpow2 : nativeOctPow (nativeCubeRoot u) 2 = Glennie.octConj (nativeCubeRoot u) := by
    change Glennie.octMul (nativeOctPow (nativeCubeRoot u) 1) (nativeCubeRoot u) = _
    rw [hpow1, nativeCubeRoot_sq u hu hn]
  have h₀ (x : Glennie.Octonion) : (nativeFourierPhase x).o12 = (nativeFourierPhase x).o01 := rfl
  have h₁ (x : Glennie.Octonion) : (nativeFourierPhase x).o02 =
      Glennie.octConj ((nativeFourierPhase x).o01) := rfl
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [Glennie.toMatrix, nativeFourierFrame, native_scalar_third, nativeFourierZero,
      nativeOctPow, h₀, h₁, native_phase_scaled, ← hconj, Glennie.octConj_smul,
      nativeCubeRoot_sq u hu hn, hpow1, hpow2]
  all_goals exact native_scalar_third

/-- Every entry of the normalized Fourier matrix belongs to the real plane spanned by (1,u). -/
theorem nativeFourier_entry_in_complex_slice (u : Glennie.Octonion)
    (hu : Glennie.octRe u = 0) (hn : Glennie.octNormSq u = 1) (k i j : Fin 3) :
    ∃ a b : ℝ, Glennie.toMatrix (nativeFourierFrame u k) i j =
      a • Glennie.octScalar 1 + b • u := by
  rw [nativeFourier_matrix_entry u hu hn]
  let n := (k.val * (i.val + 3 - j.val)) % 3
  have hn' : n < 3 := Nat.mod_lt _ (by decide)
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  change ∃ a b : ℝ, (1 / 3 : ℝ) • nativeOctPow (nativeCubeRoot u) n =
    a • Glennie.octScalar 1 + b • u
  rcases hcases with h | h | h
  · exact ⟨1 / 3, 0, by simp [h, nativeOctPow]⟩
  · refine ⟨-1 / 6, Real.sqrt 3 / 6, ?_⟩
    simp only [h, nativeOctPow, Glennie.octMul_scalar_left, one_smul, nativeCubeRoot]
    module
  · refine ⟨-1 / 6, -(Real.sqrt 3 / 6), ?_⟩
    rw [h]
    change (1 / 3 : ℝ) • Glennie.octMul
      (Glennie.octMul (Glennie.octScalar 1) (nativeCubeRoot u)) (nativeCubeRoot u) = _
    rw [Glennie.octMul_scalar_left, one_smul, nativeCubeRoot_sq u hu hn, nativeCubeRoot_conj u hu]
    unfold nativeCubeRoot
    module

end
end ThirteenPlanes.JordanFrames
