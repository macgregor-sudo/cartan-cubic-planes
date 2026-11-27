module

public import ThirteenPlanes.FieldDefect.Statements
public import ThirteenPlanes.Quaternionic.CapacityCorollaries
public import ThirteenPlanes.Quaternionic.SpectralTheorem
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Radial field defect (iii): six frames of `H₃(ℍ)` miss pairwise unbiasedness by an attained positive
minimum `ε₆` of `μ`, and `μ ≥ ε₆` on any `k ≥ 6` frames.

Route: as printed. The frame axioms are closed and force `‖p_{rc}‖ ≤ 1` (since
`tr(p • p) = tr p = 1` is the Frobenius square), so the frame tuples form a compact subset of
`(Fin 6 → Fin 3 → H₃(ℍ))`; `μ` is a maximum of finitely many continuous functions. A minimizer
with `μ = 0` would be six pairwise unbiased frames; quaternionic spectral theorem (iii) (`spectralTheorem`, last
clause) gives six bases with the same points, pairwise unbiased and distinct, contradicting
quaternionic five-basis bound (`quaternionicFiveBound`). -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading.Defect

open QuaternionicMUB
open scoped Matrix

/-- The frame axioms of `QuaternionicMUB.Frame` on a triple of matrices. -/
def IsFrameData (p : Fin 3 → QMat) : Prop :=
  (∀ a, (p a).IsHermitian) ∧ (∀ a, rtrace (p a) = 1) ∧ (∀ a, jordan (p a) (p a) = p a) ∧
    (∀ a b, a ≠ b → jordan (p a) (p b) = 0) ∧ ∑ a, p a = 1

lemma Frame.isFrameData (F : Frame) : IsFrameData F.point :=
  ⟨F.hermitian, F.trace_one, F.idempotent, F.orthogonal, F.sum_points⟩

/-- The frame with given data. -/
def frameOf (p : Fin 3 → QMat) (h : IsFrameData p) : Frame :=
  ⟨p, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- `μ` on raw tuples of matrix triples. -/
def muRaw {k : ℕ} (x : Fin k → Fin 3 → QMat) : ℝ :=
  sSup ((fun q : Fin k × Fin k × Fin 3 × Fin 3 =>
      |traceForm (x q.1 q.2.2.1) (x q.2.1 q.2.2.2) - 1 / 3|) '' {q | q.1 < q.2.1})

lemma mu_eq_muRaw {k : ℕ} (F : Fin k → Frame) : mu F = muRaw (fun i => (F i).point) := rfl

lemma continuous_rtrace : Continuous rtrace := by
  unfold rtrace
  exact continuous_finsetSum _ fun i _ =>
    Quaternion.continuous_re.comp ((continuous_id (X := QMat)).matrix_elem i i)

lemma continuous_jordan : Continuous fun p : QMat × QMat => jordan p.1 p.2 := by
  unfold jordan
  have h1 : Continuous fun p : QMat × QMat => p.1 := continuous_fst
  have h2 : Continuous fun p : QMat × QMat => p.2 := continuous_snd
  exact ((h1.matrix_mul h2).add (h2.matrix_mul h1)).const_smul (1 / 2 : ℝ)

lemma continuous_traceForm : Continuous fun p : QMat × QMat => traceForm p.1 p.2 :=
  continuous_rtrace.comp continuous_jordan

lemma continuous_muRaw (k : ℕ) : Continuous (muRaw (k := k)) := by
  let K : Set (Fin k × Fin k × Fin 3 × Fin 3) := {q | q.1 < q.2.1}
  have hK : IsCompact K := K.toFinite.isCompact
  have hf : Continuous fun p : (Fin k → Fin 3 → QMat) × (Fin k × Fin k × Fin 3 × Fin 3) =>
      |traceForm (p.1 p.2.1 p.2.2.2.1) (p.1 p.2.2.1 p.2.2.2.2) - 1 / 3| := by
    rw [continuous_prod_of_discrete_right]
    intro q
    have ha : Continuous fun x : Fin k → Fin 3 → QMat => x q.1 q.2.2.1 :=
      (continuous_apply q.2.2.1).comp (continuous_apply q.1)
    have hb : Continuous fun x : Fin k → Fin 3 → QMat => x q.2.1 q.2.2.2 :=
      (continuous_apply q.2.2.2).comp (continuous_apply q.2.1)
    exact continuous_abs.comp ((continuous_traceForm.comp (ha.prodMk hb)).sub continuous_const)
  exact hK.continuous_sSup
    (f := fun (x : Fin k → Fin 3 → QMat) (q : Fin k × Fin k × Fin 3 × Fin 3) =>
      |traceForm (x q.1 q.2.2.1) (x q.2.1 q.2.2.2) - 1 / 3|) hf

lemma muRaw_nonneg {k : ℕ} (x : Fin k → Fin 3 → QMat) : 0 ≤ muRaw x := by
  apply Real.sSup_nonneg
  rintro _ ⟨q, _, rfl⟩
  exact abs_nonneg _

lemma le_muRaw {k : ℕ} (x : Fin k → Fin 3 → QMat) (q : Fin k × Fin k × Fin 3 × Fin 3)
    (hq : q.1 < q.2.1) : |traceForm (x q.1 q.2.2.1) (x q.2.1 q.2.2.2) - 1 / 3| ≤ muRaw x :=
  le_csSup ((Set.toFinite _).image _).bddAbove ⟨q, hq, rfl⟩

/-- The tuples of six frames. -/
def frameSet : Set (Fin 6 → Fin 3 → QMat) := {x | ∀ i, IsFrameData (x i)}

lemma continuous_jordan' {X : Type*} [TopologicalSpace X] {f g : X → QMat} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => jordan (f x) (g x) := by
  unfold jordan
  exact ((hf.matrix_mul hg).add (hg.matrix_mul hf)).const_smul (1 / 2 : ℝ)

lemma isClosed_frameSet : IsClosed frameSet := by
  have hc : ∀ (i : Fin 6) (a : Fin 3), Continuous fun x : Fin 6 → Fin 3 → QMat => x i a :=
    fun i a => (continuous_apply a).comp (continuous_apply i)
  have heq : frameSet = ⋂ i : Fin 6, ({x : Fin 6 → Fin 3 → QMat | ∀ a, (x i a)ᴴ = x i a} ∩
      ({x | ∀ a, rtrace (x i a) = 1} ∩ ({x | ∀ a, jordan (x i a) (x i a) = x i a} ∩
      ({x | ∀ a b, a ≠ b → jordan (x i a) (x i b) = 0} ∩ {x | ∑ a, x i a = 1})))) := by
    ext x
    simp only [frameSet, IsFrameData, Matrix.IsHermitian, Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_inter_iff]
  rw [heq]
  refine isClosed_iInter fun i => ?_
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_eq (hc i a).matrix_conjTranspose (hc i a)
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_eq (continuous_rtrace.comp (hc i a)) continuous_const
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_eq (continuous_jordan' (hc i a) (hc i a)) (hc i a)
  · rw [Set.ofPred_forall]
    refine isClosed_iInter fun a => ?_
    rw [Set.ofPred_forall]
    refine isClosed_iInter fun b => ?_
    by_cases hab : a = b
    · simp only [hab, ne_eq, not_true_eq_false, IsEmpty.forall_iff, Set.ofPred_true]
      exact isClosed_univ
    · simp only [ne_eq, hab, not_false_eq_true, forall_const]
      exact isClosed_eq (continuous_jordan' (hc i a) (hc i b)) continuous_const
  · exact isClosed_eq (continuous_finsetSum _ fun a _ => hc i a) continuous_const

lemma entry_norm_le (p : Fin 3 → QMat) (h : IsFrameData p) (a r c : Fin 3) : ‖p a r c‖ ≤ 1 := by
  have hf : frobeniusSq (p a) = 1 := by
    rw [← traceForm_self_eq_frobeniusSq (h.1 a)]
    change rtrace (jordan (p a) (p a)) = 1
    rw [h.2.2.1 a, h.2.1 a]
  have hle : Quaternion.normSq (p a r c) ≤ frobeniusSq (p a) := by
    unfold frobeniusSq
    calc Quaternion.normSq (p a r c) ≤ ∑ j, Quaternion.normSq (p a r j) :=
          Finset.single_le_sum (f := fun j => Quaternion.normSq (p a r j))
            (fun j _ => Quaternion.normSq_nonneg) (Finset.mem_univ c)
      _ ≤ ∑ i, ∑ j, Quaternion.normSq (p a i j) :=
          Finset.single_le_sum (f := fun i => ∑ j, Quaternion.normSq (p a i j))
            (fun i _ => Finset.sum_nonneg fun j _ => Quaternion.normSq_nonneg) (Finset.mem_univ r)
  rw [hf, Quaternion.normSq_eq_norm_mul_self] at hle
  nlinarith [norm_nonneg (p a r c)]

lemma isCompact_frameSet : IsCompact frameSet := by
  have hB : IsCompact (Set.univ.pi fun _ : Fin 6 => Set.univ.pi fun _ : Fin 3 =>
      Set.univ.pi fun _ : Fin 3 => Set.univ.pi fun _ : Fin 3 =>
        Metric.closedBall (0 : Quaternion ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset isClosed_frameSet ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i a r c
  exact entry_norm_le (x i) (hx i) a r c

/-- No six pairwise unbiased frames, from the quaternionic spectral theorem (iii) and quaternionic five-basis bound. -/
lemma no_six_unbiased_frames (F : Fin 6 → Frame)
    (h : ∀ i j : Fin 6, i < j → ∀ a b, traceForm ((F i).point a) ((F j).point b) = 1 / 3) :
    False := by
  choose U hU using fun i => spectralTheorem.2.2.2 (F i)
  have hmub : ∀ i j, i ≠ j → (U i).MutuallyUnbiased (U j) := by
    intro i j hij
    rw [QBasis.mutuallyUnbiased_iff_trace]
    intro a b
    rw [hU i a, hU j b]
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact h i j hlt a b
    · rw [traceForm_comm]; exact h j i hlt b a
  have hinj : Function.Injective U := by
    intro i j hij
    by_contra hne
    have h1 := (QBasis.mutuallyUnbiased_iff_trace _ _).mp (hmub i j hne) 0 0
    rw [hij, hU j 0] at h1
    have h2 : traceForm ((F j).point 0) ((F j).point 0) = 1 := by
      change rtrace (jordan _ _) = 1
      rw [(F j).idempotent 0, (F j).trace_one 0]
    rw [h2] at h1
    norm_num at h1
  have hfive := quaternionicFiveBound (Set.range U) (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hmub i j fun hij => hne (by rw [hij]))
  have hcard := Set.ncard_range_of_injective hinj
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin] at hfive
  omega

/-- Radial field defect (iii). -/
theorem sixFramesGap : Statements.SixFramesGap := by
  have hne : frameSet.Nonempty :=
    ⟨fun _ => QBasis.coordinate.toFrame.point, fun _ => Frame.isFrameData _⟩
  obtain ⟨x, hx, hmin⟩ :=
    isCompact_frameSet.exists_isMinOn hne (continuous_muRaw 6).continuousOn
  have hmin' : ∀ y ∈ frameSet, muRaw x ≤ muRaw y := isMinOn_iff.mp hmin
  let Fs : Fin 6 → Frame := fun i => frameOf (x i) (hx i)
  have hFx : mu Fs = muRaw x := rfl
  have hlow : ∀ F : Fin 6 → Frame, muRaw x ≤ mu F := fun F =>
    hmin' (fun i => (F i).point) (fun i => Frame.isFrameData (F i))
  have hpos : 0 < muRaw x := by
    rcases (muRaw_nonneg x).lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      apply no_six_unbiased_frames Fs
      intro i j hij a b
      have hle := le_muRaw x (i, j, a, b) hij
      rw [← hzero] at hle
      have h0 : traceForm (x i a) (x j b) - 1 / 3 = 0 := abs_nonpos_iff.mp hle
      change traceForm (x i a) (x j b) = 1 / 3
      linarith
  have hk : ∀ k : ℕ, 6 ≤ k → ∀ F : Fin k → Frame, muRaw x ≤ mu F := by
    intro k hk F
    let e : Fin 6 → Fin k := Fin.castLE hk
    refine (hlow fun i => F (e i)).trans ?_
    rw [mu_eq_muRaw, mu_eq_muRaw, muRaw, muRaw]
    apply csSup_le_csSup ((Set.toFinite _).image _).bddAbove
    · exact ⟨_, ⟨((0 : Fin 6), (1 : Fin 6), (0 : Fin 3), (0 : Fin 3)), by decide, rfl⟩⟩
    · rintro _ ⟨q, hq, rfl⟩
      refine ⟨(e q.1, e q.2.1, q.2.2.1, q.2.2.2), ?_, rfl⟩
      show e q.1 < e q.2.1
      exact hq
  exact ⟨muRaw x, hpos, ⟨Fs, hFx⟩, hlow, hk⟩

end ThirteenPlanes.AlbertGrading.Defect

end
