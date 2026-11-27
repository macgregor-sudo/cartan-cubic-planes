module

public import ThirteenPlanes.AlbertGrading.Generation.Statements

@[expose] public section

set_option backward.privateInPublic true

/-! Two-plane subalgebra classification: unital subalgebras of the Albert algebra containing `H₃(ℂ_u)`.

Route: the coordinate reconstruction `AlbertSequential.lem_five_coord`
(`albert-sequential-measurements` v2.0.0, `SubalgebraCoordsAndLine.lean`) recovers `S = H₃(K)` from
the three diagonal idempotents and two real unit slots, with `K = {a | a in slot 01 of S}`; the
dimension ladder below then excludes dimension one because `u ∈ K`.

`octSubalgebra_finrank_mem'` is ported by hand from the private
`octSubalgebra_finrank_mem` in `PentadArityAndHelly.lean` of the same pinned package (project code,
Apache-2.0); only the zero-coordinate step is rewritten. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading

open AlbertSequential

private theorem oct_finrank_eight : Module.finrank ℝ Octonion = 8 := by
  let eqv : Octonion ≃ₗ[ℝ] (Fin 8 → ℝ) :=
    { toFun := fun x => ![x.1.re, x.1.imI, x.1.imJ, x.1.imK,
          x.2.re, x.2.imI, x.2.imJ, x.2.imK]
      invFun := fun f => (⟨f 0, f 1, f 2, f 3⟩, ⟨f 4, f 5, f 6, f 7⟩)
      left_inv := fun ⟨p, q⟩ => by apply Prod.ext <;> apply Quaternion.ext <;> rfl
      right_inv := fun f => by funext i; fin_cases i <;> rfl
      map_add' := fun a b => by funext i; fin_cases i <;> rfl
      map_smul' := fun r a => by funext i; fin_cases i <;> rfl }
  rw [eqv.finrank_eq, Module.finrank_fin_fun]

private theorem octOne_ne_zero : octOne ≠ 0 := by
  intro h
  have := congrArg (fun x : Octonion => x.1.re) h
  change (1 : ℝ) = 0 at this
  exact one_ne_zero this

/-- Hurwitz's dimension ladder for native octonion subalgebras (ported, see the header). -/
theorem octSubalgebra_finrank_mem' (G : OctSubalgebra) :
    Module.finrank ℝ G.carrier ∈ ({1, 2, 4, 8} : Set ℕ) := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  by_cases h1 : G.carrier ≤ Submodule.span ℝ ({octOne} : Set Octonion)
  · have h1_le : Submodule.span ℝ ({octOne} : Set Octonion) ≤ G.carrier :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr G.one_mem)
    have hfin1 : Module.finrank ℝ (Submodule.span ℝ ({octOne} : Set Octonion)) = 1 :=
      finrank_span_singleton octOne_ne_zero
    rw [le_antisymm h1 h1_le, hfin1]
    simp
  · obtain ⟨u, huG, hu_not⟩ := Set.not_subset.mp h1
    obtain ⟨φ, hφ, ⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := exists_quatEmbedding_containing_pair octOne u
    let H := OctSubalgebra.generated ({u} : Set Octonion)
    have hHG : H.carrier ≤ G.carrier :=
      OctSubalgebra.generated_le _ G (Set.singleton_subset_iff.mpr huG)
    have hH_le : H.carrier ≤ LinearMap.range φ := by
      refine OctSubalgebra.generated_le _
        { carrier := LinearMap.range φ
          one_mem := ⟨1, by rw [hφ.map_one]; rfl⟩
          mul_mem := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, hφ.map_mul a b⟩
          conj_mem := by rintro _ ⟨a, rfl⟩; exact ⟨star a, hφ.map_star a⟩ }
        (Set.singleton_subset_iff.mpr ⟨q2, hq2⟩)
    have hH_mem := octSubalgebra_le_quatEmbedding_finrank H φ hφ hH_le
    have hH_ne1 : Module.finrank ℝ H.carrier ≠ 1 := fun h => by
      have hspan := (octSubalgebra_le_quatEmbedding_finrank_one_iff H φ hφ hH_le).mp h
      apply hu_not
      rw [← hspan]
      exact OctSubalgebra.subset_generated _ rfl
    have hH24 : Module.finrank ℝ H.carrier = 2 ∨ Module.finrank ℝ H.carrier = 4 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH_mem
      rcases hH_mem with h | h | h
      · exact absurd h hH_ne1
      · exact Or.inl h
      · exact Or.inr h
    by_cases hHG_eq : H.carrier = G.carrier
    · rw [← hHG_eq]
      rcases hH24 with h2 | h4
      · simp [h2]
      · simp [h4]
    · have hHG_lt : H.carrier < G.carrier := lt_of_le_of_ne hHG hHG_eq
      rcases hH24 with hH2 | hH4
      · obtain ⟨v, hvG, hvH⟩ := Set.not_subset.mp (fun h => hHG_eq (le_antisymm hHG h))
        obtain ⟨ψ, hψ, ⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ := exists_quatEmbedding_containing_pair u v
        let K := OctSubalgebra.generated ({u, v} : Set Octonion)
        have hKG : K.carrier ≤ G.carrier := OctSubalgebra.generated_le _ G (fun z hz => by
          rcases hz with rfl | rfl <;> assumption)
        have hHK : H.carrier ≤ K.carrier :=
          OctSubalgebra.generated_le _ K
            (Set.singleton_subset_iff.mpr (OctSubalgebra.subset_generated _ (Or.inl rfl)))
        have hK_le : K.carrier ≤ LinearMap.range ψ := by
          refine OctSubalgebra.generated_le _
            { carrier := LinearMap.range ψ
              one_mem := ⟨1, by rw [hψ.map_one]; rfl⟩
              mul_mem := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, hψ.map_mul a b⟩
              conj_mem := by rintro _ ⟨a, rfl⟩; exact ⟨star a, hψ.map_star a⟩ }
            (fun z hz => by rcases hz with rfl | rfl; exact ⟨p1, hp1⟩; exact ⟨p2, hp2⟩)
        have hHK_lt : H.carrier < K.carrier := lt_of_le_of_ne hHK fun h =>
          hvH (h ▸ OctSubalgebra.subset_generated _ (Or.inr rfl))
        have hK_gt2 : 2 < Module.finrank ℝ K.carrier := by
          rw [← hH2]; exact Submodule.finrank_lt_finrank_of_lt hHK_lt
        have hK_mem := octSubalgebra_le_quatEmbedding_finrank K ψ hψ hK_le
        have hK4 : Module.finrank ℝ K.carrier = 4 := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK_mem
          omega
        have hK_eq := (octSubalgebra_le_quatEmbedding_finrank_four_iff K ψ hψ hK_le).mp hK4
        by_cases hKG_eq : K.carrier = G.carrier
        · rw [← hKG_eq, hK4]; simp
        · have hG_top := octSubalgebra_strict_gt_quatEmbedding_eq_top G ψ hψ
            (hK_eq ▸ lt_of_le_of_ne hKG hKG_eq)
          have hfin8 : Module.finrank ℝ G.carrier = 8 := by
            rw [hG_top, finrank_top, oct_finrank_eight]
          rw [hfin8]; simp
      · have hH_eq := (octSubalgebra_le_quatEmbedding_finrank_four_iff H φ hφ hH_le).mp hH4
        have hG_top := octSubalgebra_strict_gt_quatEmbedding_eq_top G φ hφ (hH_eq ▸ hHG_lt)
        have hfin8 : Module.finrank ℝ G.carrier = 8 := by
          rw [hG_top, finrank_top, oct_finrank_eight]
        rw [hfin8]; simp

/-- A unit imaginary octonion is not a real multiple of the unit. -/
private theorem not_mem_span_one {u : Octonion} (hre : octonionReal u = 0) (hn : octNormSq u = 1) :
    u ∉ Submodule.span ℝ ({octOne} : Set Octonion) := by
  intro hu
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hu
  have hre' : octonionReal (r • octOne) = r := by
    change r * (1 : ℝ) = r
    ring
  rw [hr, hre] at hre'
  rw [← hr, ← hre', zero_smul] at hn
  have h0 : octNormSq (0 : Octonion) = 0 := (octNormSq_eq_zero 0).mpr rfl
  rw [h0] at hn
  exact zero_ne_one hn

/-- Two-plane subalgebra classification. -/
theorem subalgebrasContainingComplexWindow : Statements.SubalgebrasContainingComplexWindow := by
  intro u hre hn S hS
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have one_mem : octOne ∈ complexLine u := Submodule.subset_span (Set.mem_insert _ _)
  have zero_mem : (0 : Octonion) ∈ complexLine u := (complexLine u).zero_mem
  have hd (i : Fin 3) : diagAtom i ∈ S.carrier := by
    apply hS
    intro k
    exact zero_mem
  have hslot (a : Octonion) (ha : a ∈ complexLine u) : slotElem01 a ∈ S.carrier := by
    apply hS
    intro k
    fin_cases k
    · exact ha
    · exact zero_mem
    · exact zero_mem
  have h01 : slotElem01 (octonionScalar 1) ∈ S.carrier := hslot _ one_mem
  have h02 : slotElem02 (octonionScalar 1) ∈ S.carrier := by
    apply hS
    intro k
    fin_cases k
    · exact zero_mem
    · exact one_mem
    · exact zero_mem
  obtain ⟨K, hK, hSK, hdim⟩ := lem_five_coord S (hd 0) (hd 1) (hd 2) (Or.inl ⟨h01, h02⟩)
  have hCK : complexLine u ≤ K.carrier := by
    intro a ha
    have h : a ∈ (K.carrier : Set Octonion) := by
      rw [hK]
      exact hslot a ha
    exact h
  have hKmem := octSubalgebra_finrank_mem' K
  have hK1 : Module.finrank ℝ K.carrier ≠ 1 := by
    intro h1
    have hle : Submodule.span ℝ ({octOne} : Set Octonion) ≤ K.carrier :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr K.one_mem)
    have hfin1 : Module.finrank ℝ (Submodule.span ℝ ({octOne} : Set Octonion)) = 1 :=
      finrank_span_singleton octOne_ne_zero
    have heq : Submodule.span ℝ ({octOne} : Set Octonion) = K.carrier :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin1, h1])
    apply not_mem_span_one hre hn
    rw [heq]
    exact hCK (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hK248 : Module.finrank ℝ K.carrier = 2 ∨ Module.finrank ℝ K.carrier = 4 ∨
      Module.finrank ℝ K.carrier = 8 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hKmem
    rcases hKmem with h | h | h | h
    · exact absurd h hK1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine ⟨K, hCK, hK248, hSK, ?_⟩
  rw [hdim]
  rcases hK248 with h | h | h <;> rw [h] <;> norm_num

end ThirteenPlanes.AlbertGrading
