module

public import ThirteenPlanes.Quaternionic.Attainment
public import ThirteenPlanes.Quaternionic.FloorEquality

@[expose] public section

set_option backward.privateInPublic true

/-! The actual quaternionic bases and every witnessed Fourier normal form. -/

open scoped BigOperators Matrix

namespace QuaternionicMUB

noncomputable section

/-- The three unrestricted native overlap conditions of the paper. -/
def IsUnbiasedTriple (U V W : QBasis) : Prop :=
  U.MutuallyUnbiased V ∧ U.MutuallyUnbiased W ∧ V.MutuallyUnbiased W

/-- The paper's equivalence with the Fourier triple, using one common left
unitary and independent right unit phases of the columns. -/
def IsFourierNormalForm (U V W : QBasis) (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i) = 1) : Prop :=
  ∃ L : QBasis, ∃ u v w : Outcome → Q,
    ∃ hu : ∀ i, Quaternion.normSq (u i) = 1,
    ∃ hv : ∀ i, Quaternion.normSq (v i) = 1,
    ∃ hw : ∀ i, Quaternion.normSq (w i) = 1,
      (L.product U).rightPhases u hu = QBasis.coordinate ∧
      (L.product V).rightPhases v hv = fourierBasis ∧
      (L.product W).rightPhases w hw = phasedFourierBasis p hp

/-- The actual basis witness for the forward direction of the normal form. -/
theorem exists_fourierNormalForm (U V W : QBasis) (h : IsUnbiasedTriple U V W) :
    ∃ (p : Outcome → Q) (hp : ∀ i, Quaternion.normSq (p i) = 1),
      IsFourierNormalForm U V W p hp := by
  have huv : QBasis.coordinate.MutuallyUnbiased (U.transport V) := by
    simpa only [QBasis.transport_self] using (U.transport_mutuallyUnbiased U V).mpr h.1
  obtain ⟨a, b, ha, hb, hn⟩ := hadamard_normal_form (U.transport V) huv
  let D := diagonalBasis a ha
  let L := D.product U.adjoint
  have hL (T : QBasis) : L.product T = D.product (U.transport T) := by
    apply QBasis.eq_of_mat_eq
    simp only [L, QBasis.product_mat, QBasis.adjoint, QBasis.transport, mul_assoc]
  have ha' (i : Outcome) : Quaternion.normSq (star (a i)) = 1 := by
    rw [Quaternion.normSq_star, ha]
  have hU : (L.product U).rightPhases (fun i => star (a i)) ha' = QBasis.coordinate := by
    rw [hL, QBasis.transport_self, QBasis.product_coordinate]
    apply QBasis.eq_of_mat_eq
    apply Matrix.ext
    intro i j
    rw [rightPhases_mat_apply]
    change (Matrix.diagonal a) i j * star (a j) = (1 : QMat) i j
    by_cases hij : i = j
    · subst j
      simp [Quaternion.self_mul_star, ha]
    · simp [hij]
  have hV : (L.product V).rightPhases b hb = fourierBasis := by
    rw [hL]
    exact hn
  have hWcoord : QBasis.coordinate.MutuallyUnbiased (L.product W) := by
    have hW : (L.product U).MutuallyUnbiased (L.product W) :=
      (L.product_mutuallyUnbiased U W).mpr h.2.1
    exact (QBasis.mutuallyUnbiased_congr_points
      (fun i => by rw [← hU, QBasis.rightPhases_point]) (fun _ => rfl)).mp hW
  obtain ⟨r, s, hr, hs, hw⟩ := hadamard_normal_form (L.product W) hWcoord
  have hr' (i : Outcome) : Quaternion.normSq (star (r i)) = 1 := by
    rw [Quaternion.normSq_star, hr]
  have hW := congrArg ((diagonalBasis r hr).transport) hw
  rw [QBasis.transport_rightPhases, QBasis.transport_product, diagonal_transport_fourier] at hW
  exact ⟨fun i => star (r i), hr', L, fun i => star (a i), b, s, ha', hb, hs, hU, hV, hW⟩

/-- Any witnessed normal form preserves the full native centered-tensor share. -/
theorem basisS_eq_of_fourierNormalForm {U V W : QBasis} {p : Outcome → Q}
    {hp : ∀ i, Quaternion.normSq (p i) = 1} (hn : IsFourierNormalForm U V W p hp) :
    basisS U V W = basisS QBasis.coordinate fourierBasis (phasedFourierBasis p hp) := by
  obtain ⟨L, u, v, w, hu, hv, hw, hU, hV, hW⟩ := hn
  have h := basisS_rightPhases (L.product U) (L.product V) (L.product W) u v w hu hv hw
  rw [hU, hV, hW, basisS_product] at h
  exact h.symm

/-- The native pairwise-unbiased condition for the displayed Fourier triple. -/
theorem fourierNormalTriple_iff_correlations (p : Outcome → Q)
    (hp : ∀ i, Quaternion.normSq (p i) = 1) :
    IsUnbiasedTriple QBasis.coordinate fourierBasis (phasedFourierBasis p hp) ↔
      Heron.correlation (phaseA p) = 0 ∧ Heron.correlation (phaseB p) = 0 := by
  have hcoord : QBasis.coordinate.MutuallyUnbiased (phasedFourierBasis p hp) := by
    let D := diagonalBasis p hp
    have h := (D.product_mutuallyUnbiased QBasis.coordinate fourierBasis).mpr
      coordinate_fourier_mutuallyUnbiased
    rw [QBasis.product_coordinate] at h
    exact (QBasis.mutuallyUnbiased_congr_points (diagonalBasis_point p hp) (fun _ => rfl)).mp h
  exact ⟨fun h => fourier_unbiased_correlations p hp h.2.2,
    fun h => ⟨coordinate_fourier_mutuallyUnbiased, hcoord,
      fourier_unbiased_of_correlations p hp h.1 h.2⟩⟩

private theorem fourierNormalForm_pair_unbiased {U V W : QBasis} {p : Outcome → Q}
    {hp : ∀ i, Quaternion.normSq (p i) = 1} (h : V.MutuallyUnbiased W)
    (hn : IsFourierNormalForm U V W p hp) :
    fourierBasis.MutuallyUnbiased (phasedFourierBasis p hp) := by
  obtain ⟨L, u, v, w, hu, hv, hw, hU, hV, hW⟩ := hn
  have hleft := (L.product_mutuallyUnbiased V W).mpr h
  have hright := ((L.product V).rightPhases_mutuallyUnbiased
    (L.product W) v w hv hw).mpr hleft
  rwa [hV, hW] at hright

/-- The exact extremal balance condition for every actual normal form of any
unbiased triple. The witness `hn` ranges over every allowed choice of phases. -/
theorem native_floor_equality_every_normalForm {U V W : QBasis} (h : IsUnbiasedTriple U V W)
    {p : Outcome → Q} {hp : ∀ i, Quaternion.normSq (p i) = 1}
    (hn : IsFourierNormalForm U V W p hp) :
    basisS U V W = 1 - 1 / Real.sqrt 3 ↔
      Heron.FloorBalanceShape (phaseZ p 0) (phaseZ p 1) (phaseZ p 2) := by
  obtain ⟨ha, hb⟩ := fourier_unbiased_correlations p hp
    (fourierNormalForm_pair_unbiased h.2.2 hn)
  rw [basisS_eq_of_fourierNormalForm hn, basisS_phased_formula p hp ha hb]
  exact Heron.floor_equality_of_autocorrelations (phaseA p) (phaseB p) (fun i => by
    rw [phase_normSq_split, hp i]) ha hb

/-- The particular phases printed in the manuscript's attainment formula. -/
theorem attainmentPhases_formula :
    let r := Real.sqrt (Real.sqrt 3)
    let B₀ : ℝ := 1 / Real.sqrt 2
    let A : ℝ := (r + (r ^ 2 - 1) / Real.sqrt 2) / 2
    let C : ℝ := (r - (r ^ 2 - 1) / Real.sqrt 2) / 2
    attainmentPhases =
      ![(A : Q) + C • qj, omega ^ 2 * (B₀ • (1 - qj)), -(omega * ((C : Q) + A • qj))] := by
  dsimp only
  have hB : AttainmentScalars.B = 1 / Real.sqrt 2 := by
    unfold AttainmentScalars.B
    have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    field_simp [hs.ne']
    nlinarith only [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  have hd : AttainmentScalars.delta = (AttainmentScalars.r ^ 2 - 1) / Real.sqrt 2 := by
    rw [AttainmentScalars.delta, AttainmentScalars.r_square, hB]
    ring
  rw [attainmentPhases, AttainmentScalars.A, AttainmentScalars.C, hd, hB]
  rfl

/-- Lower bound, explicit attainment, and every-normal-form equality for the
literal native centered triple-trace weight `basisS`. -/
theorem nativeTripleFloor :
    (∀ U V W : QBasis, IsUnbiasedTriple U V W →
      1 - 1 / Real.sqrt 3 ≤ basisS U V W) ∧
    (IsUnbiasedTriple QBasis.coordinate fourierBasis attainingBasis ∧
      basisS QBasis.coordinate fourierBasis attainingBasis = 1 - 1 / Real.sqrt 3) ∧
    (∀ (U V W : QBasis), IsUnbiasedTriple U V W →
      ∀ (p : Outcome → Q) (hp : ∀ i, Quaternion.normSq (p i) = 1),
      IsFourierNormalForm U V W p hp →
      (basisS U V W = 1 - 1 / Real.sqrt 3 ↔
        Heron.FloorBalanceShape (phaseZ p 0) (phaseZ p 1) (phaseZ p 2))) :=
  ⟨fun U V W h => triple_lower_bound U V W h.1 h.2.1 h.2.2,
    ⟨⟨coordinate_fourier_mutuallyUnbiased, coordinate_attaining_mutuallyUnbiased,
      fourier_attaining_mutuallyUnbiased⟩, attaining_basisS⟩,
    fun _ _ _ h _ _ hn => native_floor_equality_every_normalForm h hn⟩

end

end QuaternionicMUB
