module

public import ThirteenPlanes.AlbertGrading.Generation.Transport
public import ThirteenPlanes.Quaternionic.TripleLowerBound
public import ThirteenPlanes.Quaternionic.FrameDictionary

@[expose] public section

set_option backward.privateInPublic true

/-! Two inputs for generation by triples of closed planes.

* Two unbiased frames never lie in a line subalgebra of the dichotomy `lem_five_sub`.
* Three pairwise unbiased frames inside a quaternionic window (a trace-preserving unital Jordan
  embedding of `H₃(ℍ)`) satisfy the quaternionic lower bound
  `QuaternionicMUB.triple_lower_bound` (the sharp quaternionic triple-share bound), written with the literal 27 Albert
  triple traces. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading

open AlbertSequential

/-! ### Line subalgebras -/

/-- A line subalgebra of the dichotomy contains no two unbiased frames. -/
theorem not_le_lineSubalgebra {p q : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (hq : Glennie.Frame q) (hpq : ∀ a b, Glennie.inner (p a) (q b) = 1 / 3)
    (B : NativeJordanSubalgebra) (hpB : ∀ a, coordEquiv.symm (p a) ∈ B.carrier)
    (hqB : ∀ b, coordEquiv.symm (q b) ∈ B.carrier) (r : Albert) (hr : IsAtom r) :
    ¬ B.carrier ≤ (lineSubalgebra r hr).carrier := by
  intro hle
  set g := coordEquiv r with hg
  have hgg : Glennie.jordan g g = g := by rw [hg, ← coordEquiv_jordan, hr.1]
  have hgt : Glennie.trace g = 1 := by rw [hg, coordEquiv_trace, hr.2]
  have key : ∀ {s : Fin 3 → Glennie.Albert}, Glennie.Frame s →
      (∀ a, coordEquiv.symm (s a) ∈ B.carrier) → ∃ a, s a = g := by
    intro s hs hsB
    by_contra hnone
    push Not at hnone
    have hz : ∀ a, Glennie.jordan g (s a) = 0 := by
      intro a
      rcases atom_of_mem_lineSubalgebra hr
          (isAtom_coordEquiv_symm (hs.idempotent a) (hs.trace_one a)) (hle (hsB a)) with h | h
      · exfalso
        apply hnone a
        have h' := congrArg coordEquiv h
        rwa [LinearEquiv.apply_symm_apply] at h'
      · have h' := congrArg coordEquiv h
        rwa [coordEquiv_jordan, LinearEquiv.apply_symm_apply, map_zero] at h'
    have h1 : Glennie.jordan g 1 = 0 := by
      rw [← hs.sum_unit, Glennie.jordan_add_right, Glennie.jordan_add_right, hz 0, hz 1, hz 2]
      simp
    rw [Glennie.jordan_unit_right] at h1
    rw [h1] at hgt
    simp [Glennie.trace] at hgt
  obtain ⟨a, ha⟩ := key hp hpB
  obtain ⟨b, hb⟩ := key hq hqB
  have h := hpq a b
  rw [ha, hb] at h
  change Glennie.trace (Glennie.jordan g g) = 1 / 3 at h
  rw [hgg, hgt] at h
  norm_num at h

/-! ### Quaternionic embeddings -/

/-- A trace-preserving unital Jordan embedding of the quaternionic Hermitian matrices. -/
structure QEmb (ι : QuaternionHermitian3 →ₗ[ℝ] Glennie.Albert) : Prop where
  injective : Function.Injective ι
  unit : ι 1 = 1
  product : ∀ x y z : QuaternionHermitian3,
    (z : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) =
      (1 / 2 : ℝ) • ((x : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) * y + y * x) →
    ι z = Glennie.jordan (ι x) (ι y)
  trace : ∀ x : QuaternionHermitian3,
    Glennie.trace (ι x) = ∑ i, ((x : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) i i).re

/-- The half-anticommutator of two quaternionic Hermitian matrices. -/
def qjordan (x y : QuaternionHermitian3) : QuaternionHermitian3 :=
  ⟨(1 / 2 : ℝ) • ((x : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) * y + y * x), by
    obtain ⟨P, hP⟩ := quatHermitian_product_closed x y
    rw [← hP]
    exact P.2⟩

theorem QEmb.map_qjordan {ι : QuaternionHermitian3 →ₗ[ℝ] Glennie.Albert} (hι : QEmb ι)
    (x y : QuaternionHermitian3) : ι (qjordan x y) = Glennie.jordan (ι x) (ι y) :=
  hι.product x y _ rfl

/-- The coordinate image of a quaternionic window is a quaternionic embedding. -/
theorem window_qemb (W : QuaternionicWindow) :
    QEmb ((coordEquiv : Albert →ₗ[ℝ] Glennie.Albert) ∘ₗ W.embedding) where
  injective := coordEquiv.injective.comp W.injective
  unit := by
    change coordEquiv (W.embedding 1) = 1
    rw [W.unit, coordEquiv_unit]
  product x y z hz := by
    change coordEquiv (W.embedding z) =
      Glennie.jordan (coordEquiv (W.embedding x)) (coordEquiv (W.embedding y))
    rw [W.preserves_product x y z hz, coordEquiv_jordan]
  trace x := by
    change Glennie.trace (coordEquiv (W.embedding x)) = _
    rw [coordEquiv_trace, W.preserves_trace, Fin.sum_univ_three]

/-- The quaternionic frame of preimages of a Glennie frame in the range of an embedding. -/
def preFrame {ι : QuaternionHermitian3 →ₗ[ℝ] Glennie.Albert} (hι : QEmb ι)
    {s : Fin 3 → Glennie.Albert} (hs : Glennie.Frame s) (M : Fin 3 → QuaternionHermitian3)
    (hM : ∀ a, ι (M a) = s a) : QuaternionicMUB.Frame where
  point a := (M a : Matrix (Fin 3) (Fin 3) (Quaternion ℝ))
  hermitian a := (M a).2
  trace_one a := by
    have h := hι.trace (M a)
    rw [hM, hs.trace_one] at h
    exact h.symm
  idempotent a := by
    have h := hι.map_qjordan (M a) (M a)
    rw [hM, hs.idempotent, ← hM a] at h
    exact congrArg Subtype.val (hι.injective h)
  orthogonal a b hab := by
    have h := hι.map_qjordan (M a) (M b)
    rw [hM, hM, hs.orthogonal a b hab, ← map_zero ι] at h
    exact congrArg Subtype.val (hι.injective h)
  sum_points := by
    have h : ι (∑ a, M a) = ι 1 := by
      rw [map_sum, hι.unit]
      simp only [hM, Fin.sum_univ_three]
      exact hs.sum_unit
    have h' := congrArg Subtype.val (hι.injective h)
    simpa using h'

theorem preFrame_point {ι : QuaternionHermitian3 →ₗ[ℝ] Glennie.Albert} (hι : QEmb ι)
    {s : Fin 3 → Glennie.Albert} (hs : Glennie.Frame s) (M : Fin 3 → QuaternionHermitian3)
    (hM : ∀ a, ι (M a) = s a) (a : Fin 3) :
    (preFrame hι hs M hM).point a = (M a : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) := rfl

theorem rtrace_coe_eq {ι : QuaternionHermitian3 →ₗ[ℝ] Glennie.Albert} (hι : QEmb ι)
    (x : QuaternionHermitian3) :
    QuaternionicMUB.rtrace (x : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) = Glennie.trace (ι x) :=
  (hι.trace x).symm

theorem traceForm_coe_eq {ι : QuaternionHermitian3 →ₗ[ℝ] Glennie.Albert} (hι : QEmb ι)
    (x y : QuaternionHermitian3) :
    QuaternionicMUB.traceForm (x : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) y =
      Glennie.inner (ι x) (ι y) := by
  change QuaternionicMUB.rtrace ((qjordan x y : QuaternionHermitian3) :
    Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) = _
  rw [rtrace_coe_eq hι, hι.map_qjordan]
  rfl

theorem tripleTrace_coe_eq {ι : QuaternionHermitian3 →ₗ[ℝ] Glennie.Albert} (hι : QEmb ι)
    (x y z : QuaternionHermitian3) :
    QuaternionicMUB.traceForm (QuaternionicMUB.jordan (x : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) y)
        z = Glennie.trace (Glennie.jordan (Glennie.jordan (ι x) (ι y)) (ι z)) := by
  change QuaternionicMUB.traceForm ((qjordan x y : QuaternionHermitian3) :
    Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) z = _
  rw [traceForm_coe_eq hι, hι.map_qjordan]
  rfl

private theorem frame_unbiased {ι : QuaternionHermitian3 →ₗ[ℝ] Glennie.Albert} (hι : QEmb ι)
    {s t : Fin 3 → Glennie.Albert} (hs : Glennie.Frame s) (ht : Glennie.Frame t)
    (hst : ∀ a b, Glennie.inner (s a) (t b) = 1 / 3)
    (M N : Fin 3 → QuaternionHermitian3) (hM : ∀ a, ι (M a) = s a) (hN : ∀ a, ι (N a) = t a) :
    (preFrame hι hs M hM).MutuallyUnbiased (preFrame hι ht N hN) := by
  intro a b
  rw [preFrame_point, preFrame_point, traceForm_coe_eq hι, hM, hN, hst]

/-- The quaternionic lower bound for three pairwise unbiased frames inside a quaternionic
embedding, in Albert triple traces. -/
theorem floor_of_qemb {ι : QuaternionHermitian3 →ₗ[ℝ] Glennie.Albert} (hι : QEmb ι)
    {p q r : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (hq : Glennie.Frame q)
    (hr : Glennie.Frame r) (hpq : ∀ a b, Glennie.inner (p a) (q b) = 1 / 3)
    (hpr : ∀ a b, Glennie.inner (p a) (r b) = 1 / 3)
    (hqr : ∀ a b, Glennie.inner (q a) (r b) = 1 / 3)
    (hpι : ∀ a, p a ∈ LinearMap.range ι) (hqι : ∀ a, q a ∈ LinearMap.range ι)
    (hrι : ∀ a, r a ∈ LinearMap.range ι) :
    1 - 1 / Real.sqrt 3 ≤ 6 * ∑ a, ∑ b, ∑ c,
      (Glennie.trace (Glennie.jordan (Glennie.jordan (p a) (q b)) (r c)) - 1 / 9) ^ 2 := by
  choose M hM using hpι
  choose N hN using hqι
  choose R hR using hrι
  let F := preFrame hι hp M hM
  let G := preFrame hι hq N hN
  let H := preFrame hι hr R hR
  obtain ⟨U, hU⟩ := QuaternionicMUB.frame_has_basis F
  obtain ⟨V, hV⟩ := QuaternionicMUB.frame_has_basis G
  obtain ⟨X, hX⟩ := QuaternionicMUB.frame_has_basis H
  have hub {A B : QuaternionicMUB.QBasis} {F' G' : QuaternionicMUB.Frame}
      (hA : ∀ a, A.point a = F'.point a) (hB : ∀ a, B.point a = G'.point a)
      (h : F'.MutuallyUnbiased G') : A.MutuallyUnbiased B := by
    apply (A.mutuallyUnbiased_iff_toFrame B).mpr
    intro a b
    rw [QuaternionicMUB.QBasis.toFrame_point, QuaternionicMUB.QBasis.toFrame_point, hA, hB]
    exact h a b
  have hbound := QuaternionicMUB.triple_lower_bound U V X
    (hub hU hV (frame_unbiased hι hp hq hpq M N hM hN))
    (hub hU hX (frame_unbiased hι hp hr hpr M R hM hR))
    (hub hV hX (frame_unbiased hι hq hr hqr N R hN hR))
  have heq : QuaternionicMUB.basisS U V X = 6 * ∑ a, ∑ b, ∑ c,
      (Glennie.trace (Glennie.jordan (Glennie.jordan (p a) (q b)) (r c)) - 1 / 9) ^ 2 := by
    simp only [QuaternionicMUB.basisS, QuaternionicMUB.s, QuaternionicMUB.w,
      QuaternionicMUB.centeredTensor, hU, hV, hX]
    refine congrArg (fun t : ℝ => 6 * t) (Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_)
    have h := tripleTrace_coe_eq hι (M a) (N b) (R c)
    rw [hM, hN, hR] at h
    exact congrArg (fun t : ℝ => (t - 1 / 9) ^ 2) h
  rw [← heq]
  exact hbound

end ThirteenPlanes.AlbertGrading
