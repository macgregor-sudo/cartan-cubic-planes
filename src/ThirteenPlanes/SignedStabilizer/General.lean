module

public import ThirteenPlanes.Cubic
public import Mathlib.Topology.Sequences

@[expose] public section

set_option backward.privateInPublic true

/-! A symmetric cubic with no nonzero skew infinitesimal symmetry has a finite group of
isometric symmetries.  Pure consequence of `Cubic.lean` and Mathlib. -/

open Filter Topology
open scoped RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

namespace SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable [FiniteDimensional ℝ V]

/-- A symmetric cubic is jointly continuous in its three arguments. -/
theorem continuous_apply (h : SymmetricCubic V) :
    Continuous fun p : V × V × V => h.apply p.1 p.2.1 p.2.2 := by
  let L1 : V →ₗ[ℝ] (V →L[ℝ] V) :=
    (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] V) ≃ₗ[ℝ] (V →L[ℝ] V)).toLinearMap ∘ₗ h.L
  have hL1 : Continuous L1 := LinearMap.continuous_of_finiteDimensional L1
  have key : (fun p : V × V × V => h.apply p.1 p.2.1 p.2.2) =
      fun p => ⟪L1 p.1 p.2.1, p.2.2⟫ := rfl
  rw [key]
  exact ((hL1.comp continuous_fst).clm_apply (continuous_fst.comp continuous_snd)).inner
    (continuous_snd.comp continuous_snd)

private theorem continuous_apply₃ (h : SymmetricCubic V) {X : Type*} [TopologicalSpace X]
    {f g k : X → V} (hf : Continuous f) (hg : Continuous g) (hk : Continuous k) :
    Continuous fun p => h.apply (f p) (g p) (k p) :=
  h.continuous_apply.comp (hf.prodMk (hg.prodMk hk))

/-- Continuous linear maps that preserve the inner product and the cubic. -/
private def clmStabilizer (h : SymmetricCubic V) : Set (V →L[ℝ] V) :=
  {g | (∀ x y, ⟪g x, g y⟫ = ⟪x, y⟫) ∧ ∀ x y z, h.apply (g x) (g y) (g z) = h.apply x y z}

private theorem clmStabilizer_isCompact (h : SymmetricCubic V) :
    IsCompact (clmStabilizer h) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have ev : ∀ x : V, Continuous fun g : V →L[ℝ] V => g x :=
      fun x => continuous_id.clm_apply continuous_const
    rw [clmStabilizer, Set.ofPred_and]
    apply IsClosed.inter
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_eq ((ev x).inner (ev y)) continuous_const
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
        isClosed_eq (continuous_apply₃ h (ev x) (ev y) (ev z)) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : V →L[ℝ] V)) (r := 1)).subset ?_
    intro g hg
    rw [Metric.mem_closedBall, dist_zero_right]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => le_of_eq ?_
    rw [one_mul, norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hg.1 x x]

/-- If no nonzero skew endomorphism annihilates the cubic, only finitely many linear isometries
preserve it. -/
theorem finite_isometry_stabilizer (h : SymmetricCubic V)
    (hinf : ∀ A : V →ₗ[ℝ] V, (∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) → h.insert A = 0 → A = 0) :
    {g : V ≃ₗᵢ[ℝ] V | ∀ x y z, h.apply (g x) (g y) (g z) = h.apply x y z}.Finite := by
  classical
  -- Reduce to the compact set of continuous linear maps.
  suffices hT : (clmStabilizer h).Finite by
    let f : (V ≃ₗᵢ[ℝ] V) → (V →L[ℝ] V) := fun g => (g.toContinuousLinearEquiv : V →L[ℝ] V)
    have hinj : Function.Injective f := by
      intro g g' hgg
      ext x
      exact congrArg (fun k : V →L[ℝ] V => k x) hgg
    refine (hT.preimage hinj.injOn).subset ?_
    intro g hg
    exact ⟨fun x y => g.inner_map_map x y, hg⟩
  by_contra hTinf
  obtain ⟨g₀, hg₀, hacc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hTinf (clmStabilizer_isCompact h) subset_rfl
  have hex : ∀ n : ℕ, ∃ y, y ∈ Metric.ball g₀ (1 / ((n : ℝ) + 1)) ∩ clmStabilizer h ∧ y ≠ g₀ :=
    fun n => accPt_iff_nhds.mp hacc _ (Metric.ball_mem_nhds _ (by positivity))
  choose g hgmem hgne using hex
  have hgT : ∀ n, g n ∈ clmStabilizer h := fun n => (hgmem n).2
  have hglim : Tendsto g atTop (𝓝 g₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (Metric.mem_ball.mp (hgmem n).1))
      tendsto_one_div_add_atTop_nhds_zero_nat
  -- Differences, their norms and normalized directions.
  set B : ℕ → V →L[ℝ] V := fun n => g n - g₀ with hB
  set r : ℕ → ℝ := fun n => ‖B n‖ with hr
  have hrpos : ∀ n, 0 < r n := fun n => norm_pos_iff.mpr (sub_ne_zero.mpr (hgne n))
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have : Tendsto B atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr hglim
    simpa [r] using this.norm
  set C : ℕ → V →L[ℝ] V := fun n => (r n)⁻¹ • B n with hC
  have hCs : ∀ n, C n ∈ Metric.sphere (0 : V →L[ℝ] V) 1 := by
    intro n
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (hrpos n)]
    exact inv_mul_cancel₀ (hrpos n).ne'
  have hgC : ∀ n, g n = g₀ + r n • C n := by
    intro n
    simp only [C, smul_inv_smul₀ (hrpos n).ne', B]
    abel
  obtain ⟨C₀, hC₀s, φ, hφ, hCφ⟩ := (isCompact_sphere (0 : V →L[ℝ] V) 1).tendsto_subseq hCs
  have hrφ : Tendsto (r ∘ φ) atTop (𝓝 0) := hrlim.comp hφ.tendsto_atTop
  have hp : Tendsto (fun n => (C (φ n), r (φ n))) atTop (𝓝 (C₀, 0)) := hCφ.prodMk_nhds hrφ
  have ev : ∀ x : V, Continuous fun q : (V →L[ℝ] V) × ℝ => q.1 x :=
    fun x => continuous_fst.clm_apply continuous_const
  have cst : ∀ x : V, Continuous fun _ : (V →L[ℝ] V) × ℝ => g₀ x := fun x => continuous_const
  -- First-order invariance of the cubic in the limit direction.
  have hF : ∀ x y z, h.apply (C₀ x) (g₀ y) (g₀ z) + h.apply (g₀ x) (C₀ y) (g₀ z) +
      h.apply (g₀ x) (g₀ y) (C₀ z) = 0 := by
    intro x y z
    let Φ : (V →L[ℝ] V) × ℝ → ℝ := fun q =>
      h.apply (q.1 x) (g₀ y) (g₀ z) + h.apply (g₀ x) (q.1 y) (g₀ z) + h.apply (g₀ x) (g₀ y) (q.1 z) +
      q.2 * (h.apply (q.1 x) (q.1 y) (g₀ z) + h.apply (q.1 x) (g₀ y) (q.1 z) +
        h.apply (g₀ x) (q.1 y) (q.1 z)) + q.2 ^ 2 * h.apply (q.1 x) (q.1 y) (q.1 z)
    have hΦ : Continuous Φ := by
      have c := fun {f g k : (V →L[ℝ] V) × ℝ → V} (hf : Continuous f) (hg : Continuous g)
        (hk : Continuous k) => continuous_apply₃ h hf hg hk
      exact ((((c (ev x) (cst y) (cst z)).add (c (cst x) (ev y) (cst z))).add
        (c (cst x) (cst y) (ev z))).add (continuous_snd.mul
          (((c (ev x) (ev y) (cst z)).add (c (ev x) (cst y) (ev z))).add
            (c (cst x) (ev y) (ev z))))).add
        ((continuous_snd.pow 2).mul (c (ev x) (ev y) (ev z)))
    have hzero : ∀ n, Φ (C n, r n) = 0 := by
      intro n
      have e := (hgT n).2 x y z
      rw [← hg₀.2 x y z, hgC n] at e
      simp only [add_apply, smul_apply, apply_add₁,
        apply_add₂, apply_add₃, apply_smul₁, apply_smul₂, apply_smul₃] at e
      apply mul_left_cancel₀ (hrpos n).ne'
      simp only [Φ]
      linear_combination e
    have h1 : Tendsto (fun n => Φ (C (φ n), r (φ n))) atTop (𝓝 (Φ (C₀, 0))) :=
      (hΦ.tendsto _).comp hp
    have h2 : Tendsto (fun n => Φ (C (φ n), r (φ n))) atTop (𝓝 0) := by
      simp only [hzero]; exact tendsto_const_nhds
    have := tendsto_nhds_unique h1 h2
    simpa [Φ] using this
  -- First-order invariance of the inner product in the limit direction.
  have hS : ∀ x y, ⟪C₀ x, g₀ y⟫ + ⟪g₀ x, C₀ y⟫ = 0 := by
    intro x y
    let Ψ : (V →L[ℝ] V) × ℝ → ℝ := fun q => ⟪q.1 x, g₀ y⟫ + ⟪g₀ x, q.1 y⟫ + q.2 * ⟪q.1 x, q.1 y⟫
    have hΨ : Continuous Ψ :=
      (((ev x).inner (cst y)).add ((cst x).inner (ev y))).add
        (continuous_snd.mul ((ev x).inner (ev y)))
    have hzero : ∀ n, Ψ (C n, r n) = 0 := by
      intro n
      have e := (hgT n).1 x y
      rw [← hg₀.1 x y, hgC n] at e
      simp only [add_apply, smul_apply, inner_add_left,
        inner_add_right, real_inner_smul_left, real_inner_smul_right] at e
      apply mul_left_cancel₀ (hrpos n).ne'
      simp only [Ψ]
      linear_combination e
    have h1 : Tendsto (fun n => Ψ (C (φ n), r (φ n))) atTop (𝓝 (Ψ (C₀, 0))) :=
      (hΨ.tendsto _).comp hp
    have h2 : Tendsto (fun n => Ψ (C (φ n), r (φ n))) atTop (𝓝 0) := by
      simp only [hzero]; exact tendsto_const_nhds
    have := tendsto_nhds_unique h1 h2
    simpa [Ψ] using this
  -- Pull the limit direction back through the invertible isometry `g₀`.
  have hinj : Function.Injective (g₀ : V →ₗ[ℝ] V) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hxx := hg₀.1 x x
    change g₀ x = 0 at hx
    rw [hx, inner_zero_left] at hxx
    exact inner_self_eq_zero.mp hxx.symm
  let e : V ≃ₗ[ℝ] V := LinearEquiv.ofBijective (g₀ : V →ₗ[ℝ] V)
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let A : V →ₗ[ℝ] V := e.symm.toLinearMap ∘ₗ (C₀ : V →ₗ[ℝ] V)
  have hA : ∀ x, g₀ (A x) = C₀ x := fun x => e.apply_symm_apply (C₀ x)
  have hskew : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫ := by
    intro x y
    rw [← hg₀.1 (A x) y, ← hg₀.1 x (A y), hA, hA]
    linarith [hS x y]
  have hins : h.insert A = 0 := by
    ext x y z
    rw [apply_insert, apply_zero, ← hg₀.2 (A x) y z, ← hg₀.2 x (A y) z, ← hg₀.2 x y (A z),
      hA, hA, hA]
    exact hF x y z
  have hA0 := hinf A hskew hins
  have hC0 : C₀ = 0 := by
    ext x
    rw [← hA x, hA0]
    simp
  rw [hC0, mem_sphere_zero_iff_norm, norm_zero] at hC₀s
  exact zero_ne_one hC₀s

end SymmetricCubic

end

end ThirteenPlanes
