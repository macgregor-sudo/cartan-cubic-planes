module

public import ThirteenPlanes.Recovery.Symmetry
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped RealInnerProductSpace
open Polynomial

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {h : SymmetricCubic V} {P : PlaneDecomposition V ι} {c : ℝ}

private def planeMaximizers (P : PlaneDecomposition V ι) (h : SymmetricCubic V) (c : ℝ)
    (i : ι) : Set V :=
  {x | x ∈ P.plane i ∧ ‖x‖ = 1 ∧ h.apply x x x = Real.sqrt c}

omit [Fintype ι] in
private theorem planeMaximizer_coordinates (round : IsRound h c) (closed : IsClosedPlaneSystem h P)
    (i : ι) :
    ∃ z : P.plane i ≃ₗᵢ[ℝ] ℂ, ∀ u : P.plane i,
      (u : V) ∈ planeMaximizers P h c i ↔ (z u) ^ 3 = 1 := by
  obtain ⟨_, z, hz⟩ := binaryPlaneNormalForm (restriction_isRound round closed i) (P.dimension i)
  refine ⟨z, fun u => ?_⟩
  have he := hz u
  rw [P.restriction_apply] at he
  have hc := Real.sqrt_pos.mpr round.positive
  constructor
  · rintro ⟨_, hn, hd⟩
    have hre : ((z u) ^ 3).re = 1 := by
      rw [hd] at he
      exact (mul_left_cancel₀ hc.ne' ((mul_one _).trans he)).symm
    have hnorm : ‖(z u) ^ 3‖ = 1 := by rw [norm_pow, z.norm_map]; change ‖u‖ = 1 at hn; rw [hn, one_pow]
    have him : ((z u) ^ 3).im = 0 := by
      have hs := Complex.normSq_eq_norm_sq ((z u) ^ 3)
      rw [Complex.normSq_apply, hre, hnorm] at hs
      nlinarith
    exact Complex.ext (by simpa using hre) (by simpa using him)
  · intro hr
    have hn := congrArg norm hr
    rw [norm_pow, z.norm_map, norm_one] at hn
    have hu := (pow_left_inj₀ (norm_nonneg u) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp
      (hn.trans (one_pow 3).symm)
    refine ⟨u.property, hu, ?_⟩
    rw [hr, Complex.one_re, mul_one] at he
    exact he

omit [Fintype ι] in
private theorem planeMaximizers_finite (round : IsRound h c) (closed : IsClosedPlaneSystem h P)
    (i : ι) : (planeMaximizers P h c i).Finite := by
  obtain ⟨z, hz⟩ := planeMaximizer_coordinates round closed i
  let p : ℂ[X] := X ^ 3 - C 1
  have hp : p.Monic := monic_X_pow_sub_C 1 (by decide)
  apply ((rootSet_finite p ℂ).image (fun w => (z.symm w : V))).subset
  rintro x (hx : x ∈ P.plane i ∧ _)
  let u : P.plane i := ⟨x, hx.1⟩
  have hr := (hz u).mp hx
  refine ⟨z u, hp.mem_rootSet.mpr ?_, congrArg Subtype.val (z.symm_apply_apply u)⟩
  simp [p, hr]

private theorem cubeRoot_span : ∃ w : ℂ, w ^ 3 = 1 ∧ w.im ≠ 0 := by
  let w : ℂ := ⟨-1/2, Real.sqrt 3 / 2⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hpos := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)
  refine ⟨w, ?_, ?_⟩
  · apply Complex.ext <;>
      simp only [w, pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im,
        Complex.one_re, Complex.one_im] <;> nlinarith only [hs, congrArg (· * Real.sqrt 3) hs]
  · change Real.sqrt 3 / 2 ≠ 0
    positivity

/-- The plane-permuting cubic stabilizer is a finite group. -/
theorem planeCubicStabilizer_finite (round : IsRound h c) (closed : IsClosedPlaneSystem h P) :
    Finite (planeCubicStabilizer h P) := by
  let S : Set V := ⋃ i, planeMaximizers P h c i
  have hf : S.Finite := Set.finite_iUnion (planeMaximizers_finite round closed)
  let := hf.fintype
  have hspan : Submodule.span ℝ S = ⊤ := by
    apply top_unique
    rw [← P.exhaustive]
    apply iSup_le
    intro i x hx
    obtain ⟨z, hz⟩ := planeMaximizer_coordinates round closed i
    obtain ⟨w, hw, hwi⟩ := cubeRoot_span
    let u : P.plane i := ⟨x, hx⟩
    let bw := (z u).im / w.im
    let aw := (z u).re - bw * w.re
    have he : aw • (1 : ℂ) + bw • w = z u := by
      apply Complex.ext
      · simp [aw]
      · simp [bw, div_mul_cancel₀ _ hwi]
    have hlin := congrArg (fun v : ℂ => ((z.symm v : P.plane i) : V)) he
    simp only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, z.symm_apply_apply] at hlin
    change aw • (z.symm 1 : V) + bw • (z.symm w : V) = x at hlin
    rw [← hlin]
    apply (Submodule.span ℝ S).add_mem
    · exact (Submodule.span ℝ S).smul_mem aw (Submodule.subset_span
        (Set.mem_iUnion.mpr ⟨i, (hz _).mpr (by rw [z.apply_symm_apply, one_pow])⟩))
    · exact (Submodule.span ℝ S).smul_mem bw (Submodule.subset_span
        (Set.mem_iUnion.mpr ⟨i, (hz _).mpr (by rwa [z.apply_symm_apply])⟩))
  let restrict (g : planeCubicStabilizer h P) (x : S) : S :=
    ⟨g.val x.val, by
      obtain ⟨hd, e, he⟩ := g.property
      obtain ⟨i, hi, hn, hc⟩ := Set.mem_iUnion.mp x.property
      refine Set.mem_iUnion.mpr ⟨e.symm i, (he (e.symm i) x).mpr ?_, ?_, ?_⟩
      · rwa [e.apply_symm_apply]
      · rwa [g.val.norm_map]
      · rwa [(cubicPreserved_iff _).mp hd]⟩
  apply Finite.of_injective restrict
  intro g k he
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro x
  have hx : x ∈ Submodule.span ℝ S := by rw [hspan]; exact Submodule.mem_top
  exact Submodule.span_induction (p := fun y _ => g.val y = k.val y)
    (fun y hy => congrArg Subtype.val (congrFun he ⟨y, hy⟩))
    (by simp)
    (fun y z _ _ hy hz => by rw [map_add, map_add, hy, hz])
    (fun r y _ hy => by rw [map_smul, map_smul, hy])
    hx

end

end ThirteenPlanes.RoundCubics
