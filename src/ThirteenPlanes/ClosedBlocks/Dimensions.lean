module

public import ThirteenPlanes.ClosedBlocks.Transport
public import ThirteenPlanes.Peirce.CartanIdentification
public import ThirteenPlanes.Peirce.UnitIdempotent
public import ThirteenPlanes.Peirce.Count

@[expose] public section

set_option backward.privateInPublic true

/-! Dimension constraints for proper exhaustive closed decompositions of harmonic round cubics. -/

open scoped BigOperators InnerProductSpace

namespace ThirteenPlanes.ClosedBlocks

noncomputable section

open RoundCubics Peirce

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {h : SymmetricCubic V} {c : ℝ}

/-- A closed decomposition has nonzero all closed pieces, pairwise orthogonality and exhaustiveness. -/
structure Decomposition (h : SymmetricCubic V) (ι : Type*) where
  piece : ι → Submodule ℝ V
  nonzero : ∀ i, piece i ≠ ⊥
  orthogonal : Pairwise fun i j => (piece i).IsOrtho (piece j)
  exhaustive : ⨆ i, piece i = ⊤
  closed : ∀ i, IsClosedPiece h (piece i)

/-- An exhaustive orthogonal decomposition has the sum of its actual dimensions. -/
theorem Decomposition.finrank_eq_sum {ι : Type*} [Fintype ι] (d : Decomposition h ι) :
    Module.finrank ℝ V = ∑ i, Module.finrank ℝ (d.piece i) := by
  classical
  have hor : OrthogonalFamily ℝ (fun i => d.piece i) (fun i => (d.piece i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise d.orthogonal
  have hh : Module.finrank ℝ ↥(⨆ i, d.piece i) = ∑ i, Module.finrank ℝ (d.piece i) := by
    rw [Submodule.iSup_eq_range_dfinsupp_lsum,
      LinearMap.finrank_range_of_inj hor.independent.dfinsupp_lsum_injective]
    change Module.finrank ℝ (DirectSum ι (fun i => ↥(d.piece i))) = _
    rw [Module.finrank_directSum]
  rwa [d.exhaustive, finrank_top] at hh

/-- The checked harmonic Cartan dimensions, with the binary case included. -/
theorem harmonicRound_dim_cases (round : IsRound h c) (tf : h.TraceFree) (hn : 0 < Module.finrank ℝ V) :
    let n := Module.finrank ℝ V
    n = 2 ∨ n = 5 ∨ n = 8 ∨ n = 14 ∨ n = 26 := by
  have h1 := finrank_ne_one_of_round_traceFree round tf
  by_cases h2 : Module.finrank ℝ V = 2
  · exact Or.inl h2
  have hn' : 3 ≤ Module.finrank ℝ V := by omega
  let : Nontrivial V := Module.nontrivial_of_finrank_pos hn
  have gr := unitNormalize_isRound round
  have gt : (unitNormalize h c).TraceFree := unitNormalize_traceFree tf
  obtain ⟨a, ha⟩ := exists_unitIdempotent _ gr
  obtain ⟨_, hd, hc, _⟩ := harmonicRoundCubic_identification gr gt ha hn'
  exact Or.inr (by rcases hc with hcase | hcase | hcase | hcase <;> omega)

private theorem Decomposition.dim_pos {ι : Type*} (d : Decomposition h ι) (i : ι) :
    0 < Module.finrank ℝ (d.piece i) := by
  by_contra! hz
  exact d.nonzero i (Submodule.finrank_eq_zero.mp (by omega))

/-- In a harmonic closed decomposition each block has one of the checked Cartan dimensions. -/
theorem Decomposition.piece_dim_cases {ι : Type*} [Fintype ι] (d : Decomposition h ι)
    (round : IsRound h c) (tf : h.TraceFree) (i : ι) :
    let n := Module.finrank ℝ (d.piece i)
    n = 2 ∨ n = 5 ∨ n = 8 ∨ n = 14 ∨ n = 26 := by
  have ht := (closedPieces_traceFree_iff d.orthogonal d.exhaustive d.closed).mp tf i
  exact harmonicRound_dim_cases (closedSubspace_restriction_isRound round (d.closed i)) ht (d.dim_pos i)

/-- A nonzero block in a proper decomposition has an actual distinct nonzero block. -/
private theorem other_index_of_proper {ι : Type*} [Fintype ι] (hp : 1 < Fintype.card ι) (i : ι) :
    ∃ j : ι, i ≠ j := by
  classical
  by_contra! h
  have hs : Subsingleton ι := ⟨fun x y => (h x).symm.trans (h y)⟩
  exact (not_lt_of_ge (Fintype.card_le_one_iff_subsingleton.mpr hs)) hp

/-- The general mixed dimension bound for any two distinct blocks. -/
theorem Decomposition.mixed_dim_bound {ι : Type*} (d : Decomposition h ι) (round : IsRound h c)
    {i j : ι} (hij : i ≠ j) :
    let x := Module.finrank ℝ (d.piece i)
    let y := Module.finrank ℝ (d.piece j)
    x + y + max x y ≤ Module.finrank ℝ V :=
  (mixedProductLaw round (d.orthogonal hij) (d.closed i) (d.closed j)).2 (d.nonzero i) (d.nonzero j)

private theorem Decomposition.twice_block_dim_add_two_le {ι : Type*} [Fintype ι] (d : Decomposition h ι)
    (round : IsRound h c) (tf : h.TraceFree) (proper : 1 < Fintype.card ι) (i : ι) :
    2 * Module.finrank ℝ (d.piece i) + 2 ≤ Module.finrank ℝ V := by
  obtain ⟨j, hij⟩ := other_index_of_proper proper i
  have hb := d.mixed_dim_bound round hij
  have hm := le_max_left (Module.finrank ℝ (d.piece i)) (Module.finrank ℝ (d.piece j))
  have hj : 2 ≤ Module.finrank ℝ (d.piece j) := by
    have hp := d.piece_dim_cases round tf j
    omega
  dsimp only at hb
  omega

private theorem Decomposition.all_two_card {ι : Type*} [Fintype ι] (d : Decomposition h ι)
    (hh : ∀ i, Module.finrank ℝ (d.piece i) = 2) : Module.finrank ℝ V = 2 * Fintype.card ι := by
  rw [d.finrank_eq_sum]
  simp [hh, Nat.mul_comm]

/-- The full low-dimensional part of the harmonic closed decomposition classification. -/
theorem harmonic_decomposition_dim_eight_or_twentySix {ι : Type*} [Fintype ι] (d : Decomposition h ι)
    (round : IsRound h c) (tf : h.TraceFree) (proper : 1 < Fintype.card ι) :
    (Module.finrank ℝ V = 8 ∧ Fintype.card ι = 4 ∧ ∀ i, Module.finrank ℝ (d.piece i) = 2) ∨
      (Module.finrank ℝ V = 26 ∧ ∀ i,
        Module.finrank ℝ (d.piece i) = 2 ∨ Module.finrank ℝ (d.piece i) = 5 ∨ Module.finrank ℝ (d.piece i) = 8) := by
  classical
  let : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_one.trans proper)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hn : 0 < Module.finrank ℝ V := (d.dim_pos i₀).trans_le (Submodule.finrank_le _)
  have hb := d.twice_block_dim_add_two_le round tf proper
  have hp := d.piece_dim_cases round tf
  rcases harmonicRound_dim_cases round tf hn with hd | hd | hd | hd | hd
  · have hi := hb i₀
    have hi' := d.dim_pos i₀
    omega
  · have ha (i : ι) : Module.finrank ℝ (d.piece i) = 2 := by
      have hi := hb i
      have hi' := hp i
      omega
    have hh := d.all_two_card ha
    omega
  · have ha (i : ι) : Module.finrank ℝ (d.piece i) = 2 := by
      have hi := hb i
      have hi' := hp i
      omega
    have hh := d.all_two_card ha
    exact Or.inl ⟨hd, by omega, ha⟩
  · exfalso
    have htwofive (i : ι) : Module.finrank ℝ (d.piece i) = 2 ∨ Module.finrank ℝ (d.piece i) = 5 := by
      have hi := hb i
      have hi' := hp i
      omega
    have hnotfive (i : ι) : Module.finrank ℝ (d.piece i) ≠ 5 := by
      intro hi
      have hothers (j : ι) (hij : j ≠ i) : Module.finrank ℝ (d.piece j) = 2 := by
        have hmix := d.mixed_dim_bound round hij.symm
        have hcase := htwofive j
        dsimp only at hmix
        rcases hcase with hj | hj
        · exact hj
        · rw [hi, hj, max_self, hd] at hmix
          omega
      have hh := d.finrank_eq_sum
      have hsum : ∑ j ∈ Finset.univ.erase i, Module.finrank ℝ (d.piece j) =
          2 * (Fintype.card ι - 1) := by
        rw [show (∑ j ∈ Finset.univ.erase i, Module.finrank ℝ (d.piece j)) =
            ∑ _j ∈ Finset.univ.erase i, 2 from Finset.sum_congr rfl
              (fun j hj => hothers j (Finset.ne_of_mem_erase hj)), Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, nsmul_eq_mul, Nat.mul_comm]
        rfl
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hsum, hi] at hh
      omega
    have hall (i : ι) : Module.finrank ℝ (d.piece i) = 2 := (htwofive i).resolve_right (hnotfive i)
    let P : PlaneDecomposition V ι := ⟨d.piece, hall, d.orthogonal, d.exhaustive⟩
    have hc := planeCount_one_four_thirteen (planes := P) round d.closed proper.le
    have hcard := d.all_two_card hall
    omega
  · exact Or.inr ⟨hd, fun i => by
      have hi := hb i
      have hi' := hp i
      omega⟩

end

end ThirteenPlanes.ClosedBlocks
