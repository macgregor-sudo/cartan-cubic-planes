module

public import ThirteenPlanes.NativeTits

@[expose] public section

set_option backward.privateInPublic true

open scoped BigOperators

namespace ThirteenPlanes

noncomputable section

private def indicator (i j : Fin 3) : ℝ := if i = j then 1 else 0

private def nativeDiagonalUnit (i : Fin 3) : Glennie.Albert :=
  ⟨indicator i 0, indicator i 1, indicator i 2, 0, 0, 0⟩

private def nativeDiagonalCoordinate (x : Glennie.Albert) : Fin 3 → ℝ := ![x.d0, x.d1, x.d2]

set_option maxHeartbeats 3000000 in
private theorem nativeDiagonal_left (i : Fin 3) (x : Glennie.Albert) :
    Glennie.jordan (nativeDiagonalUnit i) x =
      ⟨indicator i 0 * x.d0, indicator i 1 * x.d1, indicator i 2 * x.d2,
        ((indicator i 0 + indicator i 1) / 2) • x.o01,
        ((indicator i 0 + indicator i 2) / 2) • x.o02,
        ((indicator i 1 + indicator i 2) / 2) • x.o12⟩ := by
  fin_cases i
  all_goals apply Glennie.Albert.ext
  all_goals try (apply Prod.ext <;> apply Quaternion.ext)
  all_goals
    simp [nativeDiagonalUnit, indicator, Glennie.jordan, Glennie.fromMatrix,
      Glennie.toMatrix, Glennie.matrixMul, Glennie.octRe, Glennie.octMul, Glennie.octConj,
      Glennie.octScalar, Fin.sum_univ_three]
  all_goals ring

private theorem nativeDiagonal_projection (i : Fin 3) (x : Glennie.Albert) :
    (2 : ℝ) • Glennie.jordan (nativeDiagonalUnit i)
      (Glennie.jordan (nativeDiagonalUnit i) x) - Glennie.jordan (nativeDiagonalUnit i) x =
        nativeDiagonalCoordinate x i • nativeDiagonalUnit i := by
  rw [nativeDiagonal_left i (Glennie.jordan (nativeDiagonalUnit i) x), nativeDiagonal_left i x]
  fin_cases i
  all_goals apply Glennie.Albert.ext
  all_goals try (apply Prod.ext <;> apply Quaternion.ext)
  all_goals norm_num [nativeDiagonalUnit, nativeDiagonalCoordinate, indicator]
  all_goals ring

private def nativeConnector (i j : Fin 3) : Glennie.Albert :=
  ⟨0, 0, 0,
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then Glennie.octScalar 1 else 0,
    if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then Glennie.octScalar 1 else 0,
    if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then Glennie.octScalar 1 else 0⟩

private theorem nativeDiagonal_connector {i j : Fin 3} (hij : i ≠ j) :
    Glennie.jordan (nativeDiagonalUnit i) (nativeConnector i j) =
      (1 / 2 : ℝ) • nativeConnector i j := by
  rw [nativeDiagonal_left]
  fin_cases i <;> fin_cases j
  all_goals try contradiction
  all_goals apply Glennie.Albert.ext
  all_goals norm_num [nativeConnector, indicator]

set_option maxHeartbeats 3000000 in
private theorem nativeConnector_square {i j : Fin 3} (hij : i ≠ j) :
    Glennie.jordan (nativeConnector i j) (nativeConnector i j) =
      nativeDiagonalUnit i + nativeDiagonalUnit j := by
  fin_cases i <;> fin_cases j
  all_goals try contradiction
  all_goals apply Glennie.Albert.ext
  all_goals try (apply Prod.ext <;> apply Quaternion.ext)
  all_goals norm_num [nativeConnector, nativeDiagonalUnit, indicator, Glennie.jordan,
    Glennie.fromMatrix, Glennie.toMatrix, Glennie.matrixMul, Glennie.octRe, Glennie.octMul,
    Glennie.octConj, Glennie.octScalar, QuaternionAlgebra.re_ofNat, Fin.sum_univ_three]

private theorem nativeDiagonal_sum :
    nativeDiagonalUnit 0 + nativeDiagonalUnit 1 + nativeDiagonalUnit 2 = (1 : Glennie.Albert) := by
  apply Glennie.Albert.ext <;> norm_num [nativeDiagonalUnit, indicator]

/-- Every native Jordan ideal is zero or the entire algebra. -/
theorem nativeAlbert_simple (I : Submodule ℝ Glennie.Albert)
    (hIdeal : ∀ a b : Glennie.Albert, b ∈ I → Glennie.jordan a b ∈ I) :
    I = ⊥ ∨ I = ⊤ := by
  classical
  by_cases h : ∃ x : Glennie.Albert, x ∈ I ∧ x ≠ 0
  · obtain ⟨x, hx, hx₀⟩ := h
    let y := Glennie.jordan x x
    have hy : y ∈ I := hIdeal x x hx
    have hn : 0 < Glennie.trace y := by
      change 0 < Glennie.inner x x
      rw [← Glennie.native_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hx₀)
    obtain ⟨i, hi⟩ : ∃ i, nativeDiagonalCoordinate y i ≠ 0 := by
      by_contra hzero
      push Not at hzero
      have h0 := hzero 0
      have h1 := hzero 1
      have h2 := hzero 2
      change y.d0 = 0 at h0
      change y.d1 = 0 at h1
      change y.d2 = 0 at h2
      simp [Glennie.trace, h0, h1, h2] at hn
    have hdiag_scaled : nativeDiagonalCoordinate y i • nativeDiagonalUnit i ∈ I := by
      rw [← nativeDiagonal_projection]
      exact I.sub_mem (I.smul_mem 2 (hIdeal _ _ (hIdeal _ _ hy))) (hIdeal _ _ hy)
    have hdiag : nativeDiagonalUnit i ∈ I := by
      simpa only [smul_smul, inv_mul_cancel₀ hi, one_smul] using
        I.smul_mem (nativeDiagonalCoordinate y i)⁻¹ hdiag_scaled
    have hall (j : Fin 3) : nativeDiagonalUnit j ∈ I := by
      by_cases hj : i = j
      · exact hj ▸ hdiag
      · have hz := hIdeal (nativeConnector i j) (nativeDiagonalUnit i) hdiag
        rw [Glennie.jordan_comm, nativeDiagonal_connector hj] at hz
        have hconn : nativeConnector i j ∈ I := by
          have hh := I.smul_mem (2 : ℝ) hz
          norm_num [smul_smul] at hh
          exact hh
        have hsq := hIdeal (nativeConnector i j) (nativeConnector i j) hconn
        rw [nativeConnector_square hj] at hsq
        have hh := I.sub_mem hsq hdiag
        simpa only [add_comm (nativeDiagonalUnit i), add_sub_cancel_right] using hh
    have h1 : (1 : Glennie.Albert) ∈ I := by
      rw [← nativeDiagonal_sum]
      exact I.add_mem (I.add_mem (hall 0) (hall 1)) (hall 2)
    right
    apply top_unique
    intro a _
    simpa using hIdeal a (1 : Glennie.Albert) h1
  · left
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    by_contra hx₀
    exact h ⟨x, hx, hx₀⟩

/-- The actual compact first Tits fixed algebra is simple. -/
theorem compactTits_simple (I : Submodule ℝ Tits.CompactTits)
    (hIdeal : ∀ a b : Tits.CompactTits, b ∈ I → Tits.CompactTits.product a b ∈ I) :
    I = ⊥ ∨ I = ⊤ := by
  let J := I.comap nativeCompactTitsEquiv.toLinearMap
  have hj (a b : Glennie.Albert) (hb : b ∈ J) : Glennie.jordan a b ∈ J := by
    change nativeCompactTitsEquiv (Glennie.jordan a b) ∈ I
    rw [nativeCompactTitsEquiv_product]
    exact hIdeal _ _ hb
  rcases nativeAlbert_simple J hj with h | h
  · left
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨x, rfl⟩ := nativeCompactTitsEquiv.surjective y
    have hx : x ∈ J := hy
    rw [h] at hx
    change x = 0 at hx
    simp [hx]
  · right
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := nativeCompactTitsEquiv.surjective y
    have hx : x ∈ J := by rw [h]; exact Submodule.mem_top
    exact hx

private def nativeDegreeThree : Glennie.Albert := ⟨0, 1, 2, 0, 0, 0⟩

private theorem nativeDegreeThree_witness (a b : ℝ) :
    Glennie.jordan nativeDegreeThree nativeDegreeThree ≠
      a • nativeDegreeThree + b • (1 : Glennie.Albert) := by
  intro h
  have h0 := congrArg Glennie.Albert.d0 h
  have h1 := congrArg Glennie.Albert.d1 h
  have h2 := congrArg Glennie.Albert.d2 h
  norm_num [nativeDegreeThree, Glennie.jordan, Glennie.fromMatrix, Glennie.toMatrix,
    Glennie.matrixMul, Glennie.octRe, Glennie.octMul, Glennie.octScalar,
    QuaternionAlgebra.re_ofNat, Fin.sum_univ_three] at h0 h1 h2
  linarith

/-- The diagonal element with entries 0, 1 and 2 satisfies no monic quadratic relation. -/
theorem compactTits_degreeThree_witness :
    ∃ x : Tits.CompactTits, ∀ a b : ℝ,
      Tits.CompactTits.square x ≠ a • x + b • Tits.CompactTits.one := by
  refine ⟨nativeCompactTitsEquiv nativeDegreeThree, fun a b h => ?_⟩
  apply nativeDegreeThree_witness a b
  apply nativeCompactTitsEquiv.injective
  change nativeToCompactTits (Glennie.jordan nativeDegreeThree nativeDegreeThree) =
    nativeToCompactTits (a • nativeDegreeThree + b • (1 : Glennie.Albert))
  rw [nativeToCompactTits_square, map_add, map_smul, map_smul, nativeToCompactTits_one]
  exact h

end

end ThirteenPlanes
