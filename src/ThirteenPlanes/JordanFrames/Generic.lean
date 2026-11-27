module

public import ThirteenPlanes.PlaneShares
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-! Uniqueness in the span of a Jordan frame and the dimension count for orthogonal planes. -/

open scoped BigOperators RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

noncomputable section

section Algebra

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- The trace-one idempotents in a frame span are its three frame points. -/
theorem eq_framePoint_of_mem_span (L : J →ₗ[ℝ] J →ₗ[ℝ] J) (tr : J →ₗ[ℝ] ℝ)
    {p : Fin 3 → J} (htr : ∀ i, tr (p i) = 1)
    (hmul : ∀ i j, L (p i) (p j) = if i = j then p i else 0)
    {x : J} (hx : x ∈ Submodule.span ℝ (Set.range p)) (hxtr : tr x = 1)
    (hxx : L x x = x) : ∃ i, x = p i := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  have hsum : ∑ i, a i = 1 := by
    simpa only [map_sum, map_smul, htr, smul_eq_mul, mul_one, hxtr] using congrArg tr ha
  have hcoord (b : Fin 3) : L x (p b) = a b • p b := by
    rw [← ha, map_sum, LinearMap.sum_apply, Finset.sum_eq_single b]
    · rw [map_smul, LinearMap.smul_apply, hmul, ite_eq_left rfl]
    · intro i _ hib
      rw [map_smul, LinearMap.smul_apply, hmul, ite_eq_right hib, smul_zero]
    · simp
  have hcoeff (i : Fin 3) : a i = 0 ∨ a i = 1 := by
    have hmat : (∑ j, (a j * a j) • p j) = x := by
      calc
        _ = L x x := by
          calc
            _ = L x (∑ j, a j • p j) := by
              rw [map_sum]
              simp only [map_smul, hcoord, smul_smul]
            _ = L x x := by rw [ha]
        _ = x := hxx
    have test := congrArg (fun z => tr (L z (p i))) hmat
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      hmul, apply_ite, map_zero, htr, smul_eq_mul, hcoord, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at test
    have hfactor : a i * (a i - 1) = 0 := by nlinarith only [test]
    exact (mul_eq_zero.mp hfactor).imp id sub_eq_zero.mp
  have hex : ∃ i, a i = 1 := by
    by_contra! hn
    have hz (i : Fin 3) : a i = 0 := (hcoeff i).resolve_right (hn i)
    simp only [hz, Finset.sum_const_zero, zero_ne_one] at hsum
  obtain ⟨i, hi⟩ := hex
  have hz (j : Fin 3) (hji : j ≠ i) : a j = 0 := by
    rcases hcoeff j with hj | hj
    · exact hj
    · have hle := Finset.sum_nonneg (s := (Finset.univ.erase i).erase j)
        (fun k _ => (hcoeff k).elim (fun hk => hk.symm ▸ le_rfl) (fun hk => hk.symm ▸ zero_le_one))
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
        ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩),
        hi, hj] at hsum
      linarith
  refine ⟨i, ?_⟩
  rw [← ha, Finset.sum_eq_single i]
  · rw [hi, one_smul]
  · intro j _ hji
    rw [hz j hji, zero_smul]
  · simp

/-- Equal centered spans force equality of the actual idempotents up to permutation. -/
theorem relabel_of_centered_span_eq
    (L : J →ₗ[ℝ] J →ₗ[ℝ] J) (tr : J →ₗ[ℝ] ℝ) (e : J) {p q : Fin 3 → J}
    (hp : ∀ i, tr (p i) = 1) (hq : ∀ i, tr (q i) = 1)
    (hpp : ∀ i j, L (p i) (p j) = if i = j then p i else 0)
    (hqq : ∀ i j, L (q i) (q j) = if i = j then q i else 0)
    (hpe : ∑ i, p i = e)
    (hS : Submodule.span ℝ (Set.range (fun i => p i - (1/3 : ℝ) • e)) =
      Submodule.span ℝ (Set.range (fun i => q i - (1/3 : ℝ) • e))) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i, q i = p (σ i) := by
  let S := Submodule.span ℝ (Set.range p)
  have he : e ∈ S := by
    rw [← hpe]
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, rfl⟩
  have hle : Submodule.span ℝ (Set.range fun i => p i - (1/3 : ℝ) • e) ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact S.sub_mem (Submodule.subset_span ⟨i, rfl⟩) (S.smul_mem _ he)
  have hqS (i : Fin 3) : q i ∈ S := by
    have hc : q i - (1/3 : ℝ) • e ∈ S :=
      hle (hS.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
    simpa only [sub_add_cancel] using S.add_mem hc (S.smul_mem (1/3 : ℝ) he)
  choose σ hσ using fun i => eq_framePoint_of_mem_span L tr hp hpp (hqS i) (hq i)
    (by rw [hqq, ite_eq_left rfl])
  have hinj : Function.Injective σ := by
    intro i j hij
    by_contra hn
    have heq := (hσ i).trans ((congrArg p hij).trans (hσ j).symm)
    have hz : q i = 0 := by
      calc
        q i = L (q i) (q i) := by rw [hqq, ite_eq_left rfl]
        _ = L (q i) (q j) := congrArg (L (q i)) heq
        _ = 0 := by rw [hqq, ite_eq_right hn]
    simpa only [hz, map_zero, zero_ne_one] using hq i
  exact ⟨Equiv.ofBijective σ ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hσ⟩

end Algebra

section Count

open RoundCubics

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The span of an indexed orthogonal family of two-planes has twice the index cardinality. -/
theorem orthogonalPlaneSpan_finrank {ι : Type*} [Fintype ι]
    (U : ι → Submodule ℝ V) (dim : ∀ i, Module.finrank ℝ (U i) = 2)
    (orth : Pairwise fun i j => (U i).IsOrtho (U j)) :
    Module.finrank ℝ (↥(⨆ i, U i)) = 2 * Fintype.card ι := by
  classical
  have hO : OrthogonalFamily ℝ (fun i => U i) (fun i => (U i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise orth
  rw [Submodule.iSup_eq_range_dfinsupp_lsum,
    LinearMap.finrank_range_of_inj hO.independent.dfinsupp_lsum_injective]
  change Module.finrank ℝ (DirectSum ι (fun i => ↥(U i))) = _
  rw [Module.finrank_directSum]
  simp [dim, Nat.mul_comm]

/-- In dimension `2*m`, a pairwise orthogonal family of two-planes is complete precisely at size `m`. -/
theorem orthogonalPlaneFamily_capacity {ι : Type*} [Fintype ι] {m : ℕ}
    (hV : Module.finrank ℝ V = 2 * m)
    (U : ι → Submodule ℝ V) (dim : ∀ i, Module.finrank ℝ (U i) = 2)
    (orth : Pairwise fun i j => (U i).IsOrtho (U j)) :
    Fintype.card ι ≤ m ∧ ((⨆ i, U i) = ⊤ ↔ Fintype.card ι = m) := by
  have h := orthogonalPlaneSpan_finrank U dim orth
  have hle := Submodule.finrank_le (⨆ i, U i)
  rw [h, hV] at hle
  refine ⟨by omega, ?_, ?_⟩
  · intro htop
    rw [htop, finrank_top, hV] at h
    omega
  · intro hcard
    apply Submodule.eq_top_of_finrank_eq
    rw [h, hcard, hV]

/-- A pairwise orthogonal family of two-planes indexed by any set is finite and
reaches the dimension bound precisely when its span is the entire space. -/
theorem orthogonalPlaneSet_capacity {F : Type*} {m : ℕ}
    (hV : Module.finrank ℝ V = 2 * m) (U : F → Submodule ℝ V)
    (dim : ∀ f, Module.finrank ℝ (U f) = 2) (S : Set F)
    (orth : S.Pairwise fun f g => (U f).IsOrtho (U g)) :
    S.Finite ∧ S.ncard ≤ m ∧ ((⨆ s : S, U s.val) = ⊤ ↔ S.ncard = m) := by
  have hfinite : S.Finite := by
    by_contra hinfinite
    let e : Fin (m + 1) ↪ S := Fin.valEmbedding.trans (Set.Infinite.natEmbedding S hinfinite)
    have hO : Pairwise fun i j => (U (e i).val).IsOrtho (U (e j).val) := by
      intro i j hij
      exact orth (e i).property (e j).property
        (fun heq => hij (e.injective (Subtype.ext heq)))
    have hb := (orthogonalPlaneFamily_capacity hV (fun i => U (e i).val) (fun i => dim _) hO).1
    rw [Fintype.card_fin] at hb
    omega
  let := hfinite.fintype
  refine ⟨hfinite, ?_⟩
  simpa only [Set.fintypeCard_eq_ncard] using
    orthogonalPlaneFamily_capacity hV (fun s : S => U s.val) (fun s => dim _)
      (fun s t hst => orth s.property t.property (fun heq => hst (Subtype.ext heq)))

end Count

end
end ThirteenPlanes.JordanFrames
