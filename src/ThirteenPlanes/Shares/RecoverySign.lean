module

public import ThirteenPlanes.RoundContractions
public import ThirteenPlanes.Shares.ComplexCoordinates
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped RealInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {h g : SymmetricCubic V} {c : ℝ}

private theorem scalar_of_symmetric_commutant (round : IsRound h c) (hdim : 0 < Module.finrank ℝ V)
    (S : Module.End ℝ V) (symm : S.IsSymmetric)
    (comm : ∀ x y : V, S (h.L x y) = h.L x (S y)) :
    ∃ realScalar : ℝ, S = realScalar • (1 : Module.End ℝ V) := by
  let b := symm.eigenvectorBasis rfl
  let a := symm.eigenvalues rfl
  let zeroIndex : Fin (Module.finrank ℝ V) := ⟨0, hdim⟩
  have eigen (i : Fin (Module.finrank ℝ V)) : S (b i) = a i • b i :=
    symm.apply_eigenvectorBasis rfl i
  have product_eigen (i : Fin (Module.finrank ℝ V)) :
      S (h.L (b i) (b i)) = a i • h.L (b i) (b i) := by
    rw [comm, eigen, map_smul]
  have hsame (i j : Fin (Module.finrank ℝ V)) : a i = a j := by
    by_contra hne
    have hvalues :
        a i • h.L (b i) (b j) = a j • h.L (b i) (b j) := by
      calc
        _ = S (h.L (b j) (b i)) := by rw [comm, eigen, map_smul, h.L_comm (b j)]
        _ = _ := by rw [h.L_comm (b j), comm, eigen, map_smul]
    have cross_zero : h.L (b i) (b j) = 0 := by
      have hz : (a i - a j) • h.L (b i) (b j) = 0 := by rw [sub_smul, hvalues, sub_self]
      exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
    have ho := symm (h.L (b i) (b i)) (h.L (b j) (b j))
    rw [product_eigen, product_eigen, real_inner_smul_left, real_inner_smul_right] at ho
    have hprod : (a i - a j) * ⟪h.L (b i) (b i), h.L (b j) (b j)⟫ = 0 := by
      linear_combination ho
    have hinner := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
    have hij : i ≠ j := fun he => hne (congrArg a he)
    have horth : ⟪b i, b j⟫ = 0 := by
      rw [orthonormal_iff_ite.mp b.orthonormal, ite_eq_right hij]
    have hp := pair round (b i) (b j)
    rw [cross_zero, norm_zero, hinner, horth, b.orthonormal.norm_eq_one i,
      b.orthonormal.norm_eq_one j] at hp
    norm_num at hp
    exact round.positive.ne' hp.symm
  refine ⟨a zeroIndex, b.toBasis.ext fun i => ?_⟩
  change S (b i) = a zeroIndex • b i
  rw [eigen, hsame i zeroIndex]

omit [FiniteDimensional ℝ V] in
private theorem eq_of_cubic_diagonal (equal : ∀ x : V, h.apply x x x = g.apply x x x) : h = g := by
  apply SymmetricCubic.ext
  intro x y z
  have h₁ := threeInputCubic_eq h x y z
  have h₂ := threeInputCubic_eq g x y z
  rw [equal, equal, equal, equal, equal, equal, equal] at h₁
  exact (mul_left_cancel₀ (by norm_num : (6 : ℝ) ≠ 0)) (h₁.symm.trans h₂)

private theorem isometry_adjoint (R : V ≃ₗᵢ[ℝ] V) :
    R.toLinearEquiv.toLinearMap.adjoint = R.symm.toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [LinearMap.adjoint_inner_left]
  change ⟪x, R y⟫ = ⟪R.symm x, y⟫
  rw [← R.inner_map_map (R.symm x) y, R.apply_symm_apply]

/-- At a fixed round strength in dimension greater than two, an orthogonal map carrying
all products to the corresponding products of a second harmonic round cubic is a single sign
on the cubic. -/
theorem roundCubic_eq_sign_of_product_isometry
    (round : IsRound h c) (round' : IsRound g c) (tf : h.TraceFree) (tf' : g.TraceFree)
    (hdim : 2 < Module.finrank ℝ V) (R : V ≃ₗᵢ[ℝ] V)
    (same : ∀ x y : V, g.L x y = R (h.L x y)) : g = h ∨ g = -h := by
  let A := R.toLinearEquiv.toLinearMap
  let B := A.adjoint
  have hB : B = R.symm.toLinearEquiv.toLinearMap := isometry_adjoint R
  have hBA : B * A = (1 : Module.End ℝ V) := by
    rw [hB]
    exact LinearMap.ext R.symm_apply_apply
  have hAB : A * B = (1 : Module.End ℝ V) := by
    rw [hB]
    exact LinearMap.ext R.apply_symm_apply
  have move (x : V) : g.L x = A * h.L x := LinearMap.ext (same x)
  have cross (x : V) : A * h.L x = h.L x * B := by
    calc
      _ = g.L x := (move x).symm
      _ = (g.L x).adjoint := (g.L_isSymmetric x).adjoint_eq.symm
      _ = _ := by
        rw [move, Module.End.mul_eq_comp, LinearMap.adjoint_comp, (h.L_isSymmetric x).adjoint_eq]
        rfl
  have cross' (x : V) : B * h.L x = h.L x * A := by
    have hz := congrArg (fun T => B * T * A) (cross x)
    change B * (A * h.L x) * A = B * (h.L x * B) * A at hz
    rw [← mul_assoc B A, hBA, one_mul, mul_assoc B (h.L x * B), mul_assoc (h.L x) B,
      hBA, mul_one] at hz
    exact hz.symm
  let S := (1 / 2 : ℝ) • (A + B)
  have hS : S.IsSymmetric := by
    intro x y
    change ⟪(1 / 2 : ℝ) • (A x + A.adjoint x), y⟫ = ⟪x, (1 / 2 : ℝ) • (A y + A.adjoint y)⟫
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, add_comm]
  have hcomm (x y : V) : S (h.L x y) = h.L x (S y) := by
    have he : S * h.L x = h.L x * S := by
      change ((1 / 2 : ℝ) • (A + B)) * h.L x = h.L x * ((1 / 2 : ℝ) • (A + B))
      rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, cross, cross', add_comm]
    exact LinearMap.congr_fun he y
  obtain ⟨γ, hγ⟩ := scalar_of_symmetric_commutant round (by omega) S hS hcomm
  have cubes (x : V) : (g.L x) ^ 3 = A * (h.L x) ^ 3 := by
    let L := h.L x
    have hsq : (A * L) ^ 2 = L ^ 2 := by
      rw [pow_two, pow_two]
      calc
        (A * L) * (A * L) = A * (L * A) * L := by noncomm_ring
        _ = A * (B * L) * L := by rw [cross']
        _ = L * L := by rw [← mul_assoc A B, hAB, one_mul]
    rw [move]
    change (A * L) ^ 3 = _
    rw [pow_succ' (A * L) 2, hsq, mul_assoc, ← pow_succ' L 2]
  have third (x : V) : LinearMap.trace ℝ V ((g.L x) ^ 3) =
      γ * LinearMap.trace ℝ V ((h.L x) ^ 3) := by
    let L := h.L x
    have hLA : (L ^ 3).adjoint = L ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
        show L.adjoint = L from (h.L_isSymmetric x).adjoint_eq, LinearMap.comp_assoc]
    have htrace : LinearMap.trace ℝ V (A * L ^ 3) = LinearMap.trace ℝ V (B * L ^ 3) := by
      rw [← SymmetricCubic.trace_adjoint_eq (A * L ^ 3), Module.End.mul_eq_comp, LinearMap.adjoint_comp,
        hLA, ← Module.End.mul_eq_comp]
      exact LinearMap.trace_mul_comm ℝ _ _
    have htrS : LinearMap.trace ℝ V (S * L ^ 3) = γ * LinearMap.trace ℝ V (L ^ 3) := by
      rw [hγ, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
    change LinearMap.trace ℝ V (A * L ^ 3) = LinearMap.trace ℝ V (B * L ^ 3) at htrace
    change LinearMap.trace ℝ V ((g.L x) ^ 3) = γ * LinearMap.trace ℝ V (L ^ 3)
    rw [cubes]
    change LinearMap.trace ℝ V (A * L ^ 3) = _
    change LinearMap.trace ℝ V (((1 / 2 : ℝ) • (A + B)) * L ^ 3) = _ at htrS
    rw [smul_mul_assoc, add_mul, map_smul, map_add, smul_eq_mul, ← htrace] at htrS
    linear_combination htrS
  have hdiag (x : V) : g.apply x x x = (γ • h).apply x x x := by
    have he := third x
    have htrace (f : SymmetricCubic V) (r : IsRound f c) (tr : f.TraceFree) :
        LinearMap.trace ℝ V ((f.L x) ^ 3) =
          -(c * ((Module.finrank ℝ V : ℝ) - 2) / 4) * f.apply x x x := by
      have h := congrArg (fun f : SymmetricCubic V => f.apply x x x)
        (triangleContraction_of_round r tr)
      simpa only [SymmetricCubic.apply_triangleContraction, SymmetricCubic.apply_smul,
        pow_succ, pow_zero, one_mul] using h
    rw [htrace g round' tf', htrace h round tf] at he
    rw [SymmetricCubic.apply_smul]
    have hk : -(c * ((Module.finrank ℝ V : ℝ) - 2) / 4) ≠ 0 := by
      have hn : (2 : ℝ) < (Module.finrank ℝ V : ℝ) := by exact_mod_cast hdim
      exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero round.positive.ne' (sub_pos.mpr hn).ne') (by norm_num))
    apply mul_left_cancel₀ hk
    linear_combination he
  have hg := eq_of_cubic_diagonal hdiag
  let i : Fin (Module.finrank ℝ V) := ⟨0, by omega⟩
  let x := stdOrthonormalBasis ℝ V i
  have hx : ‖x‖ = 1 := (stdOrthonormalBasis ℝ V).orthonormal.norm_eq_one i
  have hs := round'.square_norm x
  rw [hg, SymmetricCubic.squareMap_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    round.square_norm, hx] at hs
  norm_num at hs
  have hgamma_sq : γ ^ 2 = 1 := by
    apply mul_right_cancel₀ round.positive.ne'
    simpa using hs
  rcases sq_eq_one_iff.mp hgamma_sq with hγ₁ | hγ₁
  · exact Or.inl (by rw [hg, hγ₁, one_smul])
  · right
    calc
      g = (-1 : ℝ) • h := by rw [hg, hγ₁]
      _ = -h := neg_one_smul ℝ h

end
end ThirteenPlanes.RoundCubics
