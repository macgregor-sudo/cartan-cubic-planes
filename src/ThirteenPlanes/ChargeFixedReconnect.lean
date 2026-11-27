module

public import ThirteenPlanes.Potential.Contractions

@[expose] public section

set_option backward.privateInPublic true

/-! Linearized contractions in reconnecting directions at a block-diagonal tensor. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes
namespace ChargeFixed

noncomputable section

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι B : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V) (block : ι → B)

/-- Every nonzero coefficient of the product tensor stays in one factor block. -/
def IsBlockDiagonal (h : SymmetricCubic V) : Prop :=
  ∀ i j k, h.coefficient e i j k ≠ 0 → block i = block j ∧ block j = block k

/-- A reconnecting tensor has entries on triples of distinct factor blocks. -/
def ConnectsDistinctBlocks (δ : SymmetricCubic V) : Prop :=
  ∀ i j k, δ.coefficient e i j k ≠ 0 → block i ≠ block j ∧ block i ≠ block k ∧ block j ≠ block k

private theorem affinePath (a b : ℝ) : HasDerivAt (fun s : ℝ => a+s*b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

private theorem affinePath_mul (a b c d : ℝ) :
    HasDerivAt (fun s : ℝ => (a+s*b)*(c+s*d)) (b*c+a*d) 0 := by
  convert (affinePath a b).mul (affinePath c d) using 1
  simp

private theorem affinePath_mul₃ (a b c d f g : ℝ) :
    HasDerivAt (fun s : ℝ => (a+s*b)*(c+s*d)*(f+s*g)) (b*c*f+a*d*f+a*c*g) 0 := by
  convert ((affinePath a b).mul (affinePath c d)).mul (affinePath f g) using 1
  simp
  ring

/-- The mass matrix has zero first variation in a reconnecting direction. -/
theorem reconnecting_mass_hasDerivAt {h δ : SymmetricCubic V}
    (hh : IsBlockDiagonal e block h) (hδ : ConnectsDistinctBlocks e block δ) (i j : ι) :
    HasDerivAt (fun s : ℝ => ⟪(h+s • δ).doubleContraction (e i), e j⟫) 0 0 := by
  simp_rw [inner_doubleContraction_eq_sum e, apply_add, apply_smul]
  change HasDerivAt (fun s : ℝ => ∑ p, ∑ q,
    (h.coefficient e i p q+s*δ.coefficient e i p q)*
      (h.coefficient e j p q+s*δ.coefficient e j p q)) 0 0
  have hterm (p q : ι) : HasDerivAt (fun s : ℝ =>
      (h.coefficient e i p q+s*δ.coefficient e i p q)*
        (h.coefficient e j p q+s*δ.coefficient e j p q)) 0 0 := by
    have hA : δ.coefficient e i p q*h.coefficient e j p q=0 := by
      by_cases ha : δ.coefficient e i p q=0
      · rw [ha,zero_mul]
      · have hc : h.coefficient e j p q = 0 := by
          by_contra hb
          exact (hδ i p q ha).2.2 (hh j p q hb).2
        rw [hc,mul_zero]
    have hB : h.coefficient e i p q*δ.coefficient e j p q=0 := by
      by_cases hb : δ.coefficient e j p q=0
      · rw [hb,mul_zero]
      · have hc : h.coefficient e i p q = 0 := by
          by_contra ha
          exact (hδ j p q hb).2.2 (hh i p q ha).2
        rw [hc,zero_mul]
    simpa only [hA,hB,add_zero] using affinePath_mul
      (h.coefficient e i p q) (δ.coefficient e i p q) (h.coefficient e j p q) (δ.coefficient e j p q)
  have hsum (p : ι) : HasDerivAt (fun s : ℝ => ∑ q,
    (h.coefficient e i p q+s*δ.coefficient e i p q)*
      (h.coefficient e j p q+s*δ.coefficient e j p q)) 0 0 := by
    simpa only [Finset.sum_const_zero] using HasDerivAt.fun_sum (fun q (_ : q ∈ Finset.univ) => hterm p q)
  simpa only [Finset.sum_const_zero] using HasDerivAt.fun_sum (fun p (_ : p ∈ Finset.univ) => hsum p)

omit [FiniteDimensional ℝ V] in
private theorem mixed_triangle_term_zero {h δ : SymmetricCubic V}
    (hh : IsBlockDiagonal e block h) (hδ : ConnectsDistinctBlocks e block δ)
    (i j k p q r : ι) :
    h.coefficient e i p q*h.coefficient e j q r*δ.coefficient e k r p=0 := by
  by_cases hi : h.coefficient e i p q=0
  · simp [hi]
  by_cases hj : h.coefficient e j q r=0
  · simp [hj]
  have hz : δ.coefficient e k r p = 0 := by
    by_contra hnon
    exact (hδ k r p hnon).2.2 (((hh i p q hi).2.trans (hh j q r hj).2).symm)
  simp [hz]

/-- Every triangle term linear in a reconnecting tensor vanishes. -/
theorem reconnecting_triangle_hasDerivAt {h δ : SymmetricCubic V}
    (hh : IsBlockDiagonal e block h) (hδ : ConnectsDistinctBlocks e block δ) (i j k : ι) :
    HasDerivAt (fun s : ℝ => (h+s • δ).triangleContraction.coefficient e i j k) 0 0 := by
  simp_rw [coefficient, apply_triangleContraction_eq_sum e, apply_add, apply_smul]
  change HasDerivAt (fun s : ℝ => ∑ p, ∑ q, ∑ r,
    (h.coefficient e i p q+s*δ.coefficient e i p q)*
      (h.coefficient e j q r+s*δ.coefficient e j q r)*
      (h.coefficient e k r p+s*δ.coefficient e k r p)) 0 0
  have hterm (p q r : ι) : HasDerivAt (fun s : ℝ =>
      (h.coefficient e i p q+s*δ.coefficient e i p q)*
        (h.coefficient e j q r+s*δ.coefficient e j q r)*
        (h.coefficient e k r p+s*δ.coefficient e k r p)) 0 0 := by
    have ha : δ.coefficient e i p q*h.coefficient e j q r*h.coefficient e k r p = 0 := by
      rw [show ∀ a b c : ℝ, a*b*c=b*c*a by intros; ring]
      exact mixed_triangle_term_zero e block hh hδ j k i q r p
    have hb : h.coefficient e i p q*δ.coefficient e j q r*h.coefficient e k r p = 0 := by
      rw [show ∀ a b c : ℝ, a*b*c=c*a*b by intros; ring]
      exact mixed_triangle_term_zero e block hh hδ k i j r p q
    have hc := mixed_triangle_term_zero e block hh hδ i j k p q r
    simpa only [ha,hb,hc,add_zero] using affinePath_mul₃
      (h.coefficient e i p q) (δ.coefficient e i p q)
      (h.coefficient e j q r) (δ.coefficient e j q r)
      (h.coefficient e k r p) (δ.coefficient e k r p)
  have hsum_r (p q : ι) := HasDerivAt.fun_sum (fun r (_ : r ∈ Finset.univ) => hterm p q r)
  have hsum_q (p : ι) := HasDerivAt.fun_sum (fun q (_ : q ∈ Finset.univ) => hsum_r p q)
  simpa only [Finset.sum_const_zero] using
    HasDerivAt.fun_sum (fun p (_ : p ∈ Finset.univ) => hsum_q p)

private theorem reconnecting_insertion_slot {h δ : SymmetricCubic V}
    (hh : IsBlockDiagonal e block h) (hδ : ConnectsDistinctBlocks e block δ) (m : ι → ℝ)
    (hm : ∀ i, h.doubleContraction (e i) = m i • e i) (i j k : ι) :
    HasDerivAt (fun s : ℝ => (h+s • δ).apply ((h+s • δ).doubleContraction (e i)) (e j) (e k))
      (m i*δ.coefficient e i j k) 0 := by
  classical
  have hsum (s : ℝ) : (h+s • δ).apply ((h+s • δ).doubleContraction (e i)) (e j) (e k) =
    ∑ p, ⟪(h+s • δ).doubleContraction (e i),e p⟫ * (h+s • δ).apply (e p) (e j) (e k) := by
    simp_rw [apply_doubleContraction₁ e, inner_doubleContraction_eq_sum e]
  simp_rw [hsum]
  have hderiv (p : ι) : HasDerivAt (fun s : ℝ =>
      ⟪(h+s • δ).doubleContraction (e i),e p⟫ * (h+s • δ).apply (e p) (e j) (e k))
      ((if i=p then m i else 0)*δ.coefficient e p j k) 0 := by
    have hc : HasDerivAt (fun s : ℝ => (h+s • δ).apply (e p) (e j) (e k)) (δ.coefficient e p j k) 0 := by
      simpa only [coefficient, apply_add, apply_smul] using affinePath (h.coefficient e p j k) (δ.coefficient e p j k)
    have hd := (reconnecting_mass_hasDerivAt e block hh hδ i p).mul hc
    convert hd using 1
    simp only [zero_smul, add_zero, hm, real_inner_smul_left, e.inner_eq_ite, zero_mul]
    split_ifs <;> ring
  convert HasDerivAt.fun_sum (fun p (_ : p ∈ Finset.univ) => hderiv p) using 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro p _ hp
    simp [Ne.symm hp]
  · simp

/-- The normalized signed beta field for rescaled critical couplings. -/
def normalizedBeta (h : SymmetricCubic V) : SymmetricCubic V :=
  (1/2 : ℝ) • h - (1/2 : ℝ) • h.insert h.doubleContraction - (2 : ℝ) • h.triangleContraction

theorem normalizedBeta_eq_rescaled_oneLoopBeta (h : SymmetricCubic V) :
    normalizedBeta h = (16 * Real.pi^2) • oneLoopBeta (16 * Real.pi^2)⁻¹ h := by
  have hden : (16 : ℝ) * Real.pi^2 ≠ 0 := by positivity
  have hhalf : 8 * Real.pi^2 * (16 * Real.pi^2)⁻¹ = (1/2 : ℝ) := by
    field_simp
    ring
  simp only [oneLoopBeta, smul_smul, mul_inv_cancel₀ hden, one_smul, hhalf, normalizedBeta]

omit [FiniteDimensional ℝ V] in
private theorem apply_sub' (a b : SymmetricCubic V) (x y z : V) :
    (a-b).apply x y z = a.apply x y z - b.apply x y z := by
  simp [SymmetricCubic.apply, SymmetricCubic.L, inner_sub_left]

/-- In reconnecting directions, only the engineering dimension and the three external-leg
mass insertions contribute to the Jacobian. -/
theorem reconnecting_beta_hasDerivAt {h δ : SymmetricCubic V}
    (hh : IsBlockDiagonal e block h) (hδ : ConnectsDistinctBlocks e block δ) (m : ι → ℝ)
    (hm : ∀ i, h.doubleContraction (e i) = m i • e i) (i j k : ι) :
    HasDerivAt (fun s : ℝ => (normalizedBeta (h+s • δ)).coefficient e i j k)
      ((1-m i-m j-m k)/2*δ.coefficient e i j k) 0 := by
  have hi := reconnecting_insertion_slot e block hh hδ m hm i j k
  have hj := reconnecting_insertion_slot e block hh hδ m hm j i k
  have hk := reconnecting_insertion_slot e block hh hδ m hm k i j
  have hj' : HasDerivAt (fun s : ℝ => (h+s • δ).apply (e i) ((h+s • δ).doubleContraction (e j)) (e k))
      (m j*δ.coefficient e i j k) 0 := by
    convert hj using 1
    · funext s; rw [apply_swap₁₂]
    · rw [coefficient,coefficient,δ.apply_swap₁₂ (e i) (e j)]
  have hk' : HasDerivAt (fun s : ℝ => (h+s • δ).apply (e i) (e j) ((h+s • δ).doubleContraction (e k)))
      (m k*δ.coefficient e i j k) 0 := by
    convert hk using 1
    · funext s; rw [apply_swap₂₃ _ (e i) (e j), apply_swap₁₂ _ (e i)]
    · simp only [coefficient]; rw [δ.apply_swap₂₃ (e i) (e j),δ.apply_swap₁₂ (e i)]
  have hpath : HasDerivAt (fun s : ℝ => (h+s • δ).coefficient e i j k) (δ.coefficient e i j k) 0 := by
    simpa only [coefficient,apply_add,apply_smul] using affinePath (h.coefficient e i j k) (δ.coefficient e i j k)
  have ht := reconnecting_triangle_hasDerivAt e block hh hδ i j k
  convert (((hpath.const_mul (1/2)).sub (((hi.add hj').add hk').const_mul (1/2))).sub (ht.const_mul 2)) using 1
  · funext s
    simp only [normalizedBeta,coefficient,apply_sub',apply_smul,apply_insert,
      Pi.add_apply, Pi.sub_apply]
  · ring

/-- With one marked mass 5/9 and two exterior masses 1/3, the normalized exponent is 1/9. -/
theorem reconnecting_beta_exponent {h δ : SymmetricCubic V}
    (hh : IsBlockDiagonal e block h) (hδ : ConnectsDistinctBlocks e block δ) (m : ι → ℝ)
    (hm : ∀ i, h.doubleContraction (e i) = m i • e i)
    (hweight : ∀ i j k, δ.coefficient e i j k ≠ 0 → m i+m j+m k=11/9) (i j k : ι) :
    HasDerivAt (fun s : ℝ => (normalizedBeta (h+s • δ)).coefficient e i j k)
      (-(1/9 : ℝ)*δ.coefficient e i j k) 0 := by
  convert reconnecting_beta_hasDerivAt e block hh hδ m hm i j k using 1
  by_cases hzero : δ.coefficient e i j k=0
  · simp [hzero]
  · linear_combination (δ.coefficient e i j k/2) * hweight i j k hzero

end
end ChargeFixed
end ThirteenPlanes
