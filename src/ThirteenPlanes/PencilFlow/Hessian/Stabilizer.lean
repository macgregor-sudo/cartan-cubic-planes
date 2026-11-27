module

public import ThirteenPlanes.PencilFlow.Hessian.Spectrum

@[expose] public section

set_option backward.privateInPublic true

/-! A skew generator lies in the infinitesimal stabilizer exactly when its one-parameter rotations fix the cubic. -/

open Filter Set
open scoped BigOperators RealInnerProductSpace Topology

namespace ThirteenPlanes.PencilFlow.HessianBridge

noncomputable section

open SymmetricCubic Statements

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

local instance : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
local instance : NormedAlgebra ℚ (V →L[ℝ] V) := NormedAlgebra.restrictScalars ℚ ℝ _

private theorem pullback_rotation_apply (C : SymmetricCubic V) (Ω : skewEnd V) (s : ℝ)
    (x y z : V) :
    let A : skewEnd V := s • Ω
    (C.pullback (skewRotation A.val (mem_skewEnd.mp A.property)).toLinearMap).apply x y z =
      C.apply (NormedSpace.exp (s • (Ω : V →ₗ[ℝ] V).toContinuousLinearMap) x)
        (NormedSpace.exp (s • (Ω : V →ₗ[ℝ] V).toContinuousLinearMap) y)
        (NormedSpace.exp (s • (Ω : V →ₗ[ℝ] V).toContinuousLinearMap) z) := by
  intro A
  have hA : (A.val : V →ₗ[ℝ] V).toContinuousLinearMap =
      s • (Ω : V →ₗ[ℝ] V).toContinuousLinearMap := by
    change (s • (Ω : V →ₗ[ℝ] V)).toContinuousLinearMap = _
    exact map_smul _ s _
  simp only [pullback_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    skewRotation_apply, hA]

private theorem apply_expand (C : SymmetricCubic V) (u v w : V) :
    C.apply u v w = ∑ i, ⟪stdOrthonormalBasis ℝ V i, u⟫ * ∑ j, ⟪stdOrthonormalBasis ℝ V j, v⟫ *
      ∑ k, ⟪stdOrthonormalBasis ℝ V k, w⟫ * C.apply (stdOrthonormalBasis ℝ V k)
        (stdOrthonormalBasis ℝ V j) (stdOrthonormalBasis ℝ V i) := by
  set e := stdOrthonormalBasis ℝ V
  conv_lhs => rw [← e.sum_repr' u, apply_sum₁ e]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [C.apply_swap₁₂]
  conv_lhs => rw [← e.sum_repr' v, apply_sum₁ e]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [C.apply_swap₂₃, C.apply_swap₁₂]
  conv_lhs => rw [← e.sum_repr' w, apply_sum₁ e]

private theorem hasDerivAt_rotated_apply (C : SymmetricCubic V) (Ω : V →ₗ[ℝ] V) (x y z : V)
    (s : ℝ) :
    HasDerivAt (fun s : ℝ => C.apply (NormedSpace.exp (s • Ω.toContinuousLinearMap) x)
        (NormedSpace.exp (s • Ω.toContinuousLinearMap) y)
        (NormedSpace.exp (s • Ω.toContinuousLinearMap) z))
      ((C.insert Ω).apply (NormedSpace.exp (s • Ω.toContinuousLinearMap) x)
        (NormedSpace.exp (s • Ω.toContinuousLinearMap) y)
        (NormedSpace.exp (s • Ω.toContinuousLinearMap) z)) s := by
  set B := Ω.toContinuousLinearMap
  set e := stdOrthonormalBasis ℝ V
  set E : ℝ → V →L[ℝ] V := fun s => NormedSpace.exp (s • B)
  have hE (v : V) : HasDerivAt (fun s : ℝ => E s v) (B (E s v)) s := by
    have := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B s).clm_apply (hasDerivAt_const s v)
    simpa [E] using this
  have hc (v : V) (i) : HasDerivAt (fun s : ℝ => ⟪e i, E s v⟫) ⟪e i, B (E s v)⟫ s := by
    have := (hasDerivAt_const s (e i)).inner ℝ (hE v)
    simpa using this
  have hk (i j) := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (hc z k).mul_const (C.apply (e k) (e j) (e i))
  have hj (i) := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hc y j).mul (hk i j)
  have hi := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hc x i).mul (hj i)
  have hfun : (fun s : ℝ => C.apply (E s x) (E s y) (E s z)) = fun s => ∑ i, ⟪e i, E s x⟫ *
      ∑ j, ⟪e j, E s y⟫ * ∑ k, ⟪e k, E s z⟫ * C.apply (e k) (e j) (e i) :=
    funext fun s => apply_expand C _ _ _
  change HasDerivAt (fun s : ℝ => C.apply (E s x) (E s y) (E s z)) _ s
  rw [hfun]
  refine hi.congr_deriv ?_
  rw [apply_insert]
  change _ = C.apply (B (E s x)) (E s y) (E s z) + C.apply (E s x) (B (E s y)) (E s z) +
    C.apply (E s x) (E s y) (B (E s z))
  rw [apply_expand C (B _), apply_expand C (E s x) (B _), apply_expand C (E s x) (E s y) (B _)]
  simp only [e, Pi.mul_apply, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  ring_nf

theorem mem_skewStabilizer_iff_rotation (C : SymmetricCubic V) (Ω : skewEnd V) :
    Ω ∈ skewStabilizer C ↔
      ∀ s : ℝ,
        let A : skewEnd V := s • Ω
        C.pullback (skewRotation A.val (mem_skewEnd.mp A.property)).toLinearMap = C := by
  rw [mem_skewStabilizer]
  set Ωl : V →ₗ[ℝ] V := (Ω : V →ₗ[ℝ] V)
  constructor
  · intro h0 s A
    apply SymmetricCubic.ext
    intro x y z
    rw [pullback_rotation_apply]
    have hd (t : ℝ) := hasDerivAt_rotated_apply C Ωl x y z t
    simp only [h0, apply_zero] at hd
    have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) s 0
    rw [hc]
    simp
  · intro h
    apply SymmetricCubic.ext
    intro x y z
    have hd := hasDerivAt_rotated_apply C Ωl x y z 0
    have hconst : (fun s : ℝ => C.apply (NormedSpace.exp (s • Ωl.toContinuousLinearMap) x)
        (NormedSpace.exp (s • Ωl.toContinuousLinearMap) y)
        (NormedSpace.exp (s • Ωl.toContinuousLinearMap) z)) = fun _ => C.apply x y z := by
      funext s
      rw [← pullback_rotation_apply C Ω s x y z]
      exact congrArg (fun D : SymmetricCubic V => D.apply x y z) (h s)
    rw [hconst] at hd
    have := hd.unique (hasDerivAt_const (0 : ℝ) (C.apply x y z))
    simpa using this

end

end ThirteenPlanes.PencilFlow.HessianBridge
