module

public import ThirteenPlanes.ClosedBlocks.DecompositionPatterns
public import ThirteenPlanes.Quaternionic.NativeTraceModel

@[expose] public section

set_option backward.privateInPublic true

/-! Real, complex, and quaternionic cases of the closed-block model classification. -/

open scoped BigOperators

namespace ThirteenPlanes.ClosedBlocks

open RoundCubics Peirce

noncomputable section

/-- The allowed dimensions of a plane or a traceless Hermitian three-by-three block. -/
def ModelPieceDimension (n : ℕ) : Prop :=
  n = 2 ∨ n = 5 ∨ n = 8 ∨ n = 14 ∨ n = 26

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {h : SymmetricCubic V} {c : ℝ} {ι : Type*} [Fintype ι]

private theorem exists_distinct (proper : 1 < Fintype.card ι) (i : ι) : ∃ j : ι, i ≠ j := by
  classical
  by_contra! h
  have hi : Subsingleton ι := ⟨fun x y => (h x).symm.trans (h y)⟩
  exact (not_lt_of_ge (Fintype.card_le_one_iff_subsingleton.mpr hi)) proper

private theorem Decomposition.finrank_piece_lt_ambient (d : Decomposition h ι)
    (proper : 1 < Fintype.card ι) (i : ι) :
    Module.finrank ℝ (d.piece i) < Module.finrank ℝ V := by
  obtain ⟨j, hij⟩ := exists_distinct proper i
  have hj : 0 < Module.finrank ℝ (d.piece j) :=
    Nat.pos_of_ne_zero fun h => d.nonzero j (Submodule.finrank_eq_zero.mp h)
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (d.piece i) (d.piece j)
  rw [(d.orthogonal hij).disjoint.eq_bot, finrank_bot, add_zero] at hs
  have hp := Submodule.finrank_le (d.piece i ⊔ d.piece j)
  omega

private theorem Decomposition.card_times_two (d : Decomposition h ι)
    (h₂ : ∀ i, Module.finrank ℝ (d.piece i) = 2) :
    Module.finrank ℝ V = Fintype.card ι * 2 := by
  rw [d.finrank_eq_sum]
  simp only [h₂, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl

/-- Real trace model has no proper closed-block decomposition of the allowed kinds. -/
theorem realModel_no_proper_closedBlocks (d : Decomposition realCartanCubic ι)
    (proper : 1 < Fintype.card ι)
    (dim : ∀ i, ModelPieceDimension (Module.finrank ℝ (d.piece i))) : False := by
  have hV : Module.finrank ℝ RealTracelessSymmetric3 = 5 := by
    rw [← realCartanEquiv.finrank_eq]
    norm_num [Module.finrank_prod]
  have h₂ (i : ι) : Module.finrank ℝ (d.piece i) = 2 := by
    have hi := d.finrank_piece_lt_ambient proper i
    have hh := dim i
    unfold ModelPieceDimension at hh
    omega
  have hs := d.card_times_two h₂
  omega

/-- Every proper closed-block decomposition in the complex model consists of exactly four planes. -/
theorem complexModel_closedBlocks (d : Decomposition complexCartanCubic ι)
    (proper : 1 < Fintype.card ι)
    (dim : ∀ i, ModelPieceDimension (Module.finrank ℝ (d.piece i))) :
    Fintype.card ι = 4 ∧ ∀ i, Module.finrank ℝ (d.piece i) = 2 := by
  have hV : Module.finrank ℝ TracelessHermitian3 = 8 := by
    simpa using Peirce.finrank_eq_twice_card fourPlaneDecomposition
  have h₂ (i : ι) : Module.finrank ℝ (d.piece i) = 2 := by
    have hi := d.finrank_piece_lt_ambient proper i
    have hh := dim i
    unfold ModelPieceDimension at hh
    rcases hh with h | h | h | h | h
    · exact h
    · exfalso
      by_cases hother : ∃ j, j ≠ i ∧ Module.finrank ℝ (d.piece j) = 5
      · obtain ⟨j, hj, hj₅⟩ := hother
        have hs := Submodule.finrank_sup_add_finrank_inf_eq (d.piece i) (d.piece j)
        rw [(d.orthogonal hj.symm).disjoint.eq_bot, finrank_bot, add_zero, h, hj₅] at hs
        have hp := Submodule.finrank_le (d.piece i ⊔ d.piece j)
        omega
      have ha (j : ι) (hj : j ≠ i) : Module.finrank ℝ (d.piece j) = 2 := by
        have hj' := d.finrank_piece_lt_ambient proper j
        have hc := dim j
        unfold ModelPieceDimension at hc
        have hn : Module.finrank ℝ (d.piece j) ≠ 5 := fun hd => hother ⟨j, hj, hd⟩
        omega
      have hs := d.finrank_eq_piece_add_twice_card_sub_one i ha
      omega
    all_goals omega
  have hcard := d.card_times_two h₂
  exact ⟨by omega, h₂⟩

/-- Quaternionic trace model has no proper closed-block decomposition of the allowed kinds. -/
theorem quaternionicModel_no_proper_closedBlocks
    (d : Decomposition quaternionCartanCubic ι)
    (proper : 1 < Fintype.card ι)
    (dim : ∀ i, ModelPieceDimension (Module.finrank ℝ (d.piece i))) : False := by
  classical
  let d' : Decomposition QuaternionicMUB.quaternionTraceCubic ι :=
    ⟨d.piece, d.nonzero, d.orthogonal, d.exhaustive, fun i =>
      (isClosedPiece_smul_iff (by positivity : Real.sqrt 6 ≠ 0) (d.piece i)).mp (d.closed i)⟩
  let : Nonempty ι := Fintype.card_pos_iff.mp (Nat.zero_lt_one.trans proper)
  let round := QuaternionicMUB.quaternionTraceCubic_round
  have hV : Module.finrank ℝ QuaternionicMUB.TracelessHilbert = 14 :=
    QuaternionicMUB.finrank_TracelessHilbert
  have hp (i : ι) : Module.finrank ℝ (d'.piece i) = 2 ∨ Module.finrank ℝ (d'.piece i) = 5 := by
    obtain ⟨j, hij⟩ := exists_distinct proper i
    have hb := d'.mixed_dim_bound round hij
    have him := le_max_left (Module.finrank ℝ (d'.piece i)) (Module.finrank ℝ (d'.piece j))
    have hi : ModelPieceDimension (Module.finrank ℝ (d'.piece i)) := dim i
    have hj : ModelPieceDimension (Module.finrank ℝ (d'.piece j)) := dim j
    unfold ModelPieceDimension at hi hj
    dsimp only at hb
    omega
  have hno (i : ι) : Module.finrank ℝ (d'.piece i) ≠ 5 := by
    intro h5
    have hh (j : ι) (hj : j ≠ i) : Module.finrank ℝ (d'.piece j) = 2 := by
      rcases hp j with h | h
      · exact h
      have hb := d'.mixed_dim_bound round hj.symm
      dsimp only at hb
      rw [h5, h, max_self, hV] at hb
      omega
    have hs := d'.finrank_eq_piece_add_twice_card_sub_one i hh
    omega
  have h₂ (i : ι) : Module.finrank ℝ (d'.piece i) = 2 :=
    (hp i).resolve_right (hno i)
  let P : PlaneDecomposition QuaternionicMUB.TracelessHilbert ι :=
    ⟨d'.piece, h₂, d'.orthogonal, d'.exhaustive⟩
  have hcount := planeCount_one_four_thirteen (planes := P) round d'.closed proper.le
  have hcard := d'.card_times_two h₂
  omega

end

end ThirteenPlanes.ClosedBlocks
