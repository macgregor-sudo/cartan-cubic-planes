module

public import ThirteenPlanes.AlbertGrading.Recut.Statements
public import NativeIdempotentClassification

@[expose] public section

/-! # Re-cut frames are frames, and they are pairwise unbiased (rotation of four planes on a graded line (i))

Generic layer: thirteen graded frames `P p` (one per point of `PG(2,3)`), pairwise unbiased, a line
`l`, the subspace `Q = span ({e} ∪ ⋃_{p ∈ l} plane(P p))` of `J`, closed under the Jordan product,
and an automorphism `φ` of `Q`. No property of a grading group is used here. -/

namespace ThirteenPlanes.AlbertGrading.Recut

open ThirteenPlanes.RoundCubics

noncomputable section

/-! ## Planes of frames inside `J` -/

theorem mem_planeA {F : Fin 3 → Glennie.Albert} (hF : Glennie.Frame F) (x : Glennie.Albert) :
    x ∈ planeA F ↔ ∃ u : Fin 3 → ℝ, ∑ a, u a = 0 ∧ x = ∑ a, u a • F a := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
    refine ⟨nativeFrameEntries w, nativeFrameEntries_sum w, ?_⟩
    change ((nativeFrameChart F w : NativeTraceless) : Glennie.Albert) = _
    rw [nativeFrameChart_coe hF]
    rfl
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w, hw⟩ := nativeFrameEntries_surjective_of_zero_sum u hu
    refine ⟨nativeFrameChart F w, ⟨w, rfl⟩, ?_⟩
    change ((nativeFrameChart F w : NativeTraceless) : Glennie.Albert) = _
    rw [nativeFrameChart_coe hF, hw]
    rfl

theorem planeA_le_ker (F : Fin 3 → Glennie.Albert) : planeA F ≤ Glennie.traceLinear.ker := by
  rintro _ ⟨v, _, rfl⟩
  exact v.property

theorem trace_of_mem_planeA {F : Fin 3 → Glennie.Albert} {x : Glennie.Albert}
    (hx : x ∈ planeA F) : Glennie.trace x = 0 :=
  planeA_le_ker F hx

theorem centered_mem_planeA {F : Fin 3 → Glennie.Albert} (hF : Glennie.Frame F) (a : Fin 3) :
    F a - (1 / 3 : ℝ) • (1 : Glennie.Albert) ∈ planeA F := by
  rw [mem_planeA hF]
  refine ⟨fun b => (if b = a then 1 else 0) - 1 / 3, ?_, ?_⟩
  · simp [Finset.sum_sub_distrib]
  · rw [← hF.sum_unit]
    fin_cases a <;> simp [Fin.sum_univ_three, sub_smul, smul_add] <;> abel

theorem inner_planeA_of_unbiased {F G : Fin 3 → Glennie.Albert} (hF : Glennie.Frame F)
    (hG : Glennie.Frame G) (hFG : ∀ a b, Glennie.inner (F a) (G b) = 1 / 3)
    {x y : Glennie.Albert} (hx : x ∈ planeA F) (hy : y ∈ planeA G) : Glennie.inner x y = 0 := by
  obtain ⟨u, hu, rfl⟩ := (mem_planeA hF x).mp hx
  obtain ⟨v, hv, rfl⟩ := (mem_planeA hG y).mp hy
  change Glennie.inner (nativeFrameSynthesis F u) (nativeFrameSynthesis G v) = 0
  rw [nativeFrameSynthesis_inner]
  simp only [nativeFrame_inner_synthesis, hFG]
  rw [show (∑ c, v c * (1 / 3 : ℝ)) = 0 by rw [← Finset.sum_mul, hv, zero_mul]]
  simp

/-! ## A sum of three nonzero orthogonal idempotents equal to `e` is a frame -/

theorem one_le_trace_of_idempotent {q : Glennie.Albert} (hq : Glennie.jordan q q = q)
    (hne : q ≠ 0) : 1 ≤ Glennie.trace q := by
  open AlbertSequential AlbertSequential.NativeAnalysis in
  have hq' : jordanMul (recoveredCoordinateEquiv.symm q) (recoveredCoordinateEquiv.symm q) =
      recoveredCoordinateEquiv.symm q := by
    apply recoveredCoordinateEquiv.injective
    rw [recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply, hq]
  have ht : Glennie.trace q = albertTrace (recoveredCoordinateEquiv.symm q) := by
    rw [← recoveredCoordinateEquiv_trace, LinearEquiv.apply_symm_apply]
  have hpos : 0 < Glennie.trace q := by
    have h0 : Glennie.inner q q = Glennie.trace q := by rw [Glennie.inner, hq]
    rw [← h0]
    exact lt_of_le_of_ne (Glennie.inner_self_nonneg q)
      (fun h => hne ((Glennie.inner_self_eq_zero q).mp h.symm))
  rcases native_idempotent_trace_cases _ hq' with h | h | h | h <;> rw [← ht] at h <;> linarith

theorem trace_eq_one_of_split (x : Fin 3 → Glennie.Albert)
    (hid : ∀ a, Glennie.jordan (x a) (x a) = x a) (hne : ∀ a, x a ≠ 0)
    (hsum : x 0 + x 1 + x 2 = 1) (a : Fin 3) : Glennie.trace (x a) = 1 := by
  have h := congrArg Glennie.trace hsum
  simp only [Glennie.trace_add, Glennie.trace_unit] at h
  have h0 := one_le_trace_of_idempotent (hid 0) (hne 0)
  have h1 := one_le_trace_of_idempotent (hid 1) (hne 1)
  have h2 := one_le_trace_of_idempotent (hid 2) (hne 2)
  fin_cases a <;> simp <;> linarith

/-! ## The generic re-cut -/

/-- The generic re-cut of thirteen frames along the line `l` by a map `φ` of `Q`. -/
def recutG (Q : Submodule ℝ Glennie.Albert) (φ : Q ≃ₗ[ℝ] Q)
    (P : SignedPlaneIndex → Fin 3 → Glennie.Albert) (l : SignedPlaneIndex)
    (p : SignedPlaneIndex) (a : Fin 3) : Glennie.Albert :=
  if signedPointOnLine p l then extendOn Q φ (P p a) else P p a

theorem extendOn_of_mem {Q : Submodule ℝ Glennie.Albert} (φ : Q ≃ₗ[ℝ] Q) {x : Glennie.Albert}
    (h : x ∈ Q) : extendOn Q φ x = φ ⟨x, h⟩ := by
  unfold extendOn
  rw [dif_pos h]

/-- The span of `e` and the planes of the frames on `l`. -/
def lineQ (P : SignedPlaneIndex → Fin 3 → Glennie.Albert) (l : SignedPlaneIndex) :
    Submodule ℝ Glennie.Albert :=
  Submodule.span ℝ ({1} ∪ ⋃ (p : SignedPlaneIndex) (_ : signedPointOnLine p l),
    (planeA (P p) : Set Glennie.Albert))

section Generic

variable {P : SignedPlaneIndex → Fin 3 → Glennie.Albert} (hF : ∀ p, Glennie.Frame (P p))
  (hU : ∀ p q, p ≠ q → ∀ a b, Glennie.inner (P p a) (P q b) = 1 / 3)
  {l : SignedPlaneIndex}

include hF in
theorem one_mem_lineQ : (1 : Glennie.Albert) ∈ lineQ P l :=
  Submodule.subset_span (Or.inl rfl)

theorem planeA_le_lineQ {p : SignedPlaneIndex} (hp : signedPointOnLine p l) :
    planeA (P p) ≤ lineQ P l := fun x hx =>
  Submodule.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hx⟩⟩))

include hF in
theorem point_mem_lineQ {p : SignedPlaneIndex} (hp : signedPointOnLine p l) (a : Fin 3) :
    P p a ∈ lineQ P l := by
  have h := (lineQ P l).add_mem ((lineQ P l).smul_mem (1 / 3 : ℝ) (one_mem_lineQ hF))
    (planeA_le_lineQ hp (centered_mem_planeA (hF p) a))
  simpa using h

include hF hU in
/-- Every element of `Q_ℓ` is orthogonal to the plane of a point off `ℓ`. -/
theorem inner_lineQ_planeA {q : SignedPlaneIndex} (hq : ¬ signedPointOnLine q l)
    {x : Glennie.Albert} (hx : x ∈ lineQ P l) {d : Glennie.Albert} (hd : d ∈ planeA (P q)) :
    Glennie.inner x d = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · rw [Set.mem_singleton_iff.mp hx, nativeInner_one_left, trace_of_mem_planeA hd]
    · obtain ⟨p, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hp, hx⟩ := Set.mem_iUnion.mp hx
      have hpq : p ≠ q := by rintro rfl; exact hq hp
      exact inner_planeA_of_unbiased (hF p) (hF q) (hU p q hpq) hx hd
  | zero => simp [Glennie.inner]
  | add x y _ _ hx hy => rw [Glennie.inner_add_left, hx, hy, add_zero]
  | smul r x _ hx => rw [Glennie.inner_smul_left, hx, mul_zero]

variable (hclosed : ∀ x y, x ∈ lineQ P l → y ∈ lineQ P l → Glennie.jordan x y ∈ lineQ P l)
variable {φ : lineQ P l ≃ₗ[ℝ] lineQ P l} (hφ : IsSubalgebraAutomorphism (lineQ P l) φ)

include hφ in
theorem phi_one (h1 : (1 : Glennie.Albert) ∈ lineQ P l) :
    (φ ⟨1, h1⟩ : Glennie.Albert) = 1 := by
  let y := φ.symm ⟨1, h1⟩
  have hy : Glennie.jordan (((⟨1, h1⟩ : lineQ P l)) : Glennie.Albert) (y : Glennie.Albert) ∈
      lineQ P l := by
    simpa using y.property
  have key := hφ ⟨1, h1⟩ y hy
  have e1 : (⟨_, hy⟩ : lineQ P l) = y := Subtype.ext (by simp)
  have e2 : φ y = ⟨1, h1⟩ := LinearEquiv.apply_symm_apply _ _
  rw [e1, e2] at key
  simpa using key.symm

theorem phi_combination {F : Fin 3 → Glennie.Albert} (hFQ : ∀ a, F a ∈ lineQ P l)
    (u : Fin 3 → ℝ) (h : ∑ a, u a • F a ∈ lineQ P l) :
    (φ ⟨_, h⟩ : Glennie.Albert) = ∑ a, u a • (φ ⟨F a, hFQ a⟩ : Glennie.Albert) := by
  have e : (⟨_, h⟩ : lineQ P l) = ∑ a, u a • (⟨F a, hFQ a⟩ : lineQ P l) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    rfl
  rw [e, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Submodule.coe_smul]

include hF hφ in
/-- The image of a frame on `l` under `φ` is a frame of `J`. -/
theorem phi_frame {p : SignedPlaneIndex} (hp : signedPointOnLine p l) :
    Glennie.Frame (fun a => (φ ⟨P p a, point_mem_lineQ hF hp a⟩ : Glennie.Albert)) := by
  have hQ := point_mem_lineQ hF hp
  have hid (a : Fin 3) : Glennie.jordan (φ ⟨P p a, hQ a⟩ : Glennie.Albert) (φ ⟨P p a, hQ a⟩) =
      φ ⟨P p a, hQ a⟩ := by
    have hj : Glennie.jordan ((⟨P p a, hQ a⟩ : lineQ P l) : Glennie.Albert)
        ((⟨P p a, hQ a⟩ : lineQ P l) : Glennie.Albert) ∈ lineQ P l := by
      change Glennie.jordan (P p a) (P p a) ∈ lineQ P l
      rw [(hF p).idempotent a]
      exact hQ a
    have key := hφ _ _ hj
    have e : (⟨_, hj⟩ : lineQ P l) = ⟨P p a, hQ a⟩ := by
      apply Subtype.ext
      dsimp only
      exact (hF p).idempotent a
    rw [e] at key
    exact key.symm
  have horth (a b : Fin 3) (hab : a ≠ b) :
      Glennie.jordan (φ ⟨P p a, hQ a⟩ : Glennie.Albert) (φ ⟨P p b, hQ b⟩) = 0 := by
    have hj : Glennie.jordan ((⟨P p a, hQ a⟩ : lineQ P l) : Glennie.Albert)
        ((⟨P p b, hQ b⟩ : lineQ P l) : Glennie.Albert) ∈ lineQ P l := by
      change Glennie.jordan (P p a) (P p b) ∈ lineQ P l
      rw [(hF p).orthogonal a b hab]
      exact (lineQ P l).zero_mem
    have key := hφ _ _ hj
    have e : (⟨_, hj⟩ : lineQ P l) = 0 := by
      apply Subtype.ext
      dsimp only
      rw [Submodule.coe_zero]
      exact (hF p).orthogonal a b hab
    rw [e, map_zero, Submodule.coe_zero] at key
    exact key.symm
  have hsum : (φ ⟨P p 0, hQ 0⟩ : Glennie.Albert) + φ ⟨P p 1, hQ 1⟩ + φ ⟨P p 2, hQ 2⟩ = 1 := by
    have e : (⟨P p 0, hQ 0⟩ : lineQ P l) + ⟨P p 1, hQ 1⟩ + ⟨P p 2, hQ 2⟩ =
        ⟨1, one_mem_lineQ hF⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_add]
      exact (hF p).sum_unit
    have key := congrArg (fun z => ((φ z : lineQ P l) : Glennie.Albert)) e
    simp only [map_add, Submodule.coe_add] at key
    rw [key]
    exact phi_one hφ _
  have hne (a : Fin 3) : (φ ⟨P p a, hQ a⟩ : Glennie.Albert) ≠ 0 := by
    intro h
    have h' : φ ⟨P p a, hQ a⟩ = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_zero]
      exact h
    rw [LinearEquiv.map_eq_zero_iff] at h'
    have ht := (hF p).trace_one a
    have h0 : P p a = 0 := by
      have := congrArg Subtype.val h'
      rw [Submodule.coe_zero] at this
      exact this
    rw [h0] at ht
    simp at ht
  exact ⟨trace_eq_one_of_split _ hid hne hsum, hid, horth, hsum⟩

include hF hφ in
/-- `φ` preserves the trace of `J` on `Q`. -/
theorem phi_trace {x : Glennie.Albert} (hx : x ∈ lineQ P l) :
    Glennie.trace (φ ⟨x, hx⟩ : Glennie.Albert) = Glennie.trace x := by
  let f : lineQ P l →ₗ[ℝ] ℝ :=
    Glennie.traceLinear ∘ₗ (lineQ P l).subtype ∘ₗ φ.toLinearMap -
      Glennie.traceLinear ∘ₗ (lineQ P l).subtype
  have hf (y : lineQ P l) : f y = Glennie.trace (φ y : Glennie.Albert) - Glennie.trace y := rfl
  have hgen : ({1} ∪ ⋃ (p : SignedPlaneIndex) (_ : signedPointOnLine p l),
      (planeA (P p) : Set Glennie.Albert)) ⊆ (LinearMap.ker f).map (lineQ P l).subtype := by
    intro y hy
    have hyQ : y ∈ lineQ P l := Submodule.subset_span hy
    refine ⟨⟨y, hyQ⟩, ?_, rfl⟩
    change f ⟨y, hyQ⟩ = 0
    rw [hf, sub_eq_zero]
    rcases hy with hy | hy
    · have hy := Set.mem_singleton_iff.mp hy
      subst hy
      rw [phi_one hφ]
    · obtain ⟨p, hy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hp, hy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨u, hu, rfl⟩ := (mem_planeA (hF p) _).mp hy
      rw [phi_combination (point_mem_lineQ hF hp) u hyQ]
      have hfr := phi_frame hF hφ hp
      change Glennie.traceLinear _ = Glennie.traceLinear _
      simp only [map_sum, map_smul, Glennie.traceLinear_apply, hfr.trace_one, (hF p).trace_one]
  have hle : lineQ P l ≤ (LinearMap.ker f).map (lineQ P l).subtype := Submodule.span_le.mpr hgen
  obtain ⟨y, hy, hyx⟩ := hle hx
  have hyx' : y = ⟨x, hx⟩ := Subtype.ext hyx
  subst hyx'
  have := hf ⟨x, hx⟩
  rw [LinearMap.mem_ker.mp hy] at this
  linarith

include hF hU hclosed hφ in
/-- Rotation of four planes on a graded line (i): the re-cut frames are frames of `J` and pairwise unbiased. -/
theorem recutG_frames :
    (∀ p, Glennie.Frame (recutG (lineQ P l) φ P l p)) ∧
    ∀ p q, p ≠ q → ∀ a b, Glennie.inner (recutG (lineQ P l) φ P l p a)
      (recutG (lineQ P l) φ P l q b) = 1 / 3 := by
  have hQ := fun {p} (hp : signedPointOnLine p l) => point_mem_lineQ hF hp
  have on_eq {p} (hp : signedPointOnLine p l) :
      recutG (lineQ P l) φ P l p = fun a => (φ ⟨P p a, hQ hp a⟩ : Glennie.Albert) := by
    funext a
    simp only [recutG, if_pos hp, extendOn_of_mem φ (hQ hp a)]
  have off_eq {p} (hp : ¬ signedPointOnLine p l) : recutG (lineQ P l) φ P l p = P p := by
    funext a
    simp only [recutG, if_neg hp]
  -- an image point against an untouched point
  have mixed {p q} (hp : signedPointOnLine p l) (hq : ¬ signedPointOnLine q l) (a b : Fin 3) :
      Glennie.inner (φ ⟨P p a, hQ hp a⟩ : Glennie.Albert) (P q b) = 1 / 3 := by
    have hd := centered_mem_planeA (hF q) b
    have hsplit : P q b = (1 / 3 : ℝ) • (1 : Glennie.Albert) + (P q b - (1 / 3 : ℝ) • 1) := by
      abel
    rw [hsplit, Glennie.inner_add_right, Glennie.inner_smul_right, nativeInner_one_right,
      (phi_frame hF hφ hp).trace_one a,
      inner_lineQ_planeA hF hU hq (φ ⟨P p a, hQ hp a⟩).property hd]
    norm_num
  refine ⟨fun p => ?_, fun p q hpq a b => ?_⟩
  · by_cases hp : signedPointOnLine p l
    · rw [on_eq hp]; exact phi_frame hF hφ hp
    · rw [off_eq hp]; exact hF p
  · by_cases hp : signedPointOnLine p l <;> by_cases hq : signedPointOnLine q l
    · rw [on_eq hp, on_eq hq]
      have hj : Glennie.jordan ((⟨P p a, hQ hp a⟩ : lineQ P l) : Glennie.Albert)
          ((⟨P q b, hQ hq b⟩ : lineQ P l) : Glennie.Albert) ∈ lineQ P l := by
        exact hclosed _ _ (hQ hp a) (hQ hq b)
      change Glennie.trace (Glennie.jordan _ _) = _
      rw [← hφ _ _ hj, phi_trace hF hφ]
      exact hU p q hpq a b
    · rw [on_eq hp, off_eq hq]; exact mixed hp hq a b
    · rw [off_eq hp, on_eq hq, Glennie.inner_comm]; exact mixed hq hp b a
    · rw [off_eq hp, off_eq hq]; exact hU p q hpq a b

end Generic

end

end ThirteenPlanes.AlbertGrading.Recut
