module

public import ThirteenPlanes.AlbertGrading.Recut.Frames
public import ThirteenPlanes.AlbertGrading.Recut.Combinatorics

@[expose] public section

/-! # Positive shares of a re-cut system (rotation of four planes on a graded line (ii), first sentence)

For points `q, q'` off `ℓ` whose line meets `ℓ` at `r`, the
product space `W_{qq'} = P_r ⊕ P_{q''}` is not changed by the re-cut. With binary shares one of
the four re-cut planes lies in `W_{qq'}`; being orthogonal to `P_{q''}`, it is `P_r`. Comparing the pair sums for `q, q'` in the graded and re-cut systems gives a
re-cut plane equal to `P_r` for every `r ∈ ℓ`. The nine untouched planes contribute the same
amounts to both sums. 
-/

namespace ThirteenPlanes.AlbertGrading.Recut

open ThirteenPlanes.RoundCubics

noncomputable section

theorem nativeRoundCubic : IsRound nativeEqualCubic (1 / 6) :=
  ⟨by norm_num, fun x => by rw [nativeEqualCubic_squareLaw]; ring⟩

theorem code_closed (c : TightNativeCode) : IsClosedPlaneSystem nativeEqualCubic c.decomposition := by
  intro f x y hx hy
  exact nativeFramePlane_closed (c.frame f) hx hy

theorem planeA_eq_iff (F G : Fin 3 → Glennie.Albert) :
    planeA F = planeA G ↔ nativeFramePlane F = nativeFramePlane G :=
  (Submodule.map_injective_of_injective Subtype.val_injective).eq_iff

theorem mem_planeA_coe {F : Fin 3 → Glennie.Albert} {v : NativeTraceless} :
    (v : Glennie.Albert) ∈ planeA F ↔ v ∈ nativeFramePlane F :=
  ⟨fun ⟨_, hu, huv⟩ => (Subtype.val_injective huv) ▸ hu, fun h => ⟨v, h, rfl⟩⟩

/-- If `S ≤ A ⊔ B` with `S ⊥ B` and `A ⊥ B`, then `S ≤ A`. -/
theorem le_of_le_sup_of_isOrtho {S A B : Submodule ℝ NativeTraceless} (h : S ≤ A ⊔ B)
    (hSB : S.IsOrtho B) (hAB : A.IsOrtho B) : S ≤ A := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (h hx)
  have h1 : inner ℝ (a + b) b = 0 := hSB.inner_eq hx hb
  have h2 : inner ℝ a b = 0 := hAB.inner_eq ha hb
  rw [inner_add_left, h2, zero_add, real_inner_self_eq_norm_sq] at h1
  have hb0 : b = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    exact norm_eq_zero.mp this
  rw [hb0, add_zero]
  exact ha

section Generic

variable {P : SignedPlaneIndex → Fin 3 → Glennie.Albert} (hF : ∀ p, Glennie.Frame (P p))
  (hU : ∀ p q, p ≠ q → ∀ a b, Glennie.inner (P p a) (P q b) = 1 / 3)
  {l : SignedPlaneIndex}
  (hclosed : ∀ x y, x ∈ lineQ P l → y ∈ lineQ P l → Glennie.jordan x y ∈ lineQ P l)
  {φ : lineQ P l ≃ₗ[ℝ] lineQ P l} (hφ : IsSubalgebraAutomorphism (lineQ P l) φ)

/-- The generic form of "φ permutes the four planes of `l`". -/
def PermutesG (P : SignedPlaneIndex → Fin 3 → Glennie.Albert) (l : SignedPlaneIndex)
    (φ : lineQ P l ≃ₗ[ℝ] lineQ P l) : Prop :=
  ∃ σ : {p : SignedPlaneIndex // signedPointOnLine p l} ≃
      {p : SignedPlaneIndex // signedPointOnLine p l},
    ∀ p x, x ∈ planeA (P (σ p).val) ↔
      ∃ y : lineQ P l, (y : Glennie.Albert) ∈ planeA (P p.val) ∧ (φ y : Glennie.Albert) = x

include hF hφ in
theorem recutG_on {p : SignedPlaneIndex} (hp : signedPointOnLine p l) :
    recutG (lineQ P l) φ P l p = fun a => (φ ⟨P p a, point_mem_lineQ hF hp a⟩ : Glennie.Albert) := by
  funext a
  simp only [recutG, if_pos hp, extendOn_of_mem φ (point_mem_lineQ hF hp a)]

theorem recutG_off {p : SignedPlaneIndex} (hp : ¬ signedPointOnLine p l) :
    recutG (lineQ P l) φ P l p = P p := by
  funext a
  simp only [recutG, if_neg hp]

include hF hφ in
/-- The plane of a re-cut frame on `l` is the image under `φ` of the graded plane. -/
theorem mem_planeA_recutG {p : SignedPlaneIndex} (hp : signedPointOnLine p l) (x : Glennie.Albert) :
    x ∈ planeA (recutG (lineQ P l) φ P l p) ↔
      ∃ y : lineQ P l, (y : Glennie.Albert) ∈ planeA (P p) ∧ (φ y : Glennie.Albert) = x := by
  rw [recutG_on hF hφ hp, mem_planeA (phi_frame hF hφ hp)]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hmem : ∑ a, u a • P p a ∈ lineQ P l :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (point_mem_lineQ hF hp a)
    exact ⟨⟨_, hmem⟩, (mem_planeA (hF p) _).mpr ⟨u, hu, rfl⟩,
      phi_combination (point_mem_lineQ hF hp) u hmem⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, hu, hyu⟩ := (mem_planeA (hF p) _).mp hy
    have hmem : ∑ a, u a • P p a ∈ lineQ P l := hyu ▸ y.property
    have hye : y = ⟨_, hmem⟩ := Subtype.ext hyu
    exact ⟨u, hu, by rw [hye, phi_combination (point_mem_lineQ hF hp) u hmem]⟩

include hF hU in
theorem graded_planes_orthogonal {p q : SignedPlaneIndex} (hpq : p ≠ q) :
    (nativeFramePlane (P p)).IsOrtho (nativeFramePlane (P q)) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro v hv w hw
  change Glennie.inner (v : Glennie.Albert) w = 0
  exact inner_planeA_of_unbiased (hF p) (hF q) (hU p q hpq) (mem_planeA_coe.mpr hv)
    (mem_planeA_coe.mpr hw)

include hF hU in
theorem graded_planes_injective {p q : SignedPlaneIndex}
    (h : nativeFramePlane (P p) = nativeFramePlane (P q)) : p = q := by
  by_contra hpq
  have ho := graded_planes_orthogonal hF hU hpq
  rw [h] at ho
  have hbot : nativeFramePlane (P q) = ⊥ :=
    Submodule.eq_bot_iff _ |>.mpr fun x hx => inner_self_eq_zero.mp (ho.inner_eq hx hx)
  have hd := nativeFramePlane_dimension (hF q)
  rw [hbot, finrank_bot] at hd
  exact absurd hd (by norm_num)

include hF hU hclosed hφ in
/-- A re-cut plane on `l` is orthogonal to every graded plane off `l`. -/
theorem recut_plane_orthogonal_off {k q : SignedPlaneIndex} (hk : signedPointOnLine k l)
    (hq : ¬ signedPointOnLine q l) :
    (nativeFramePlane (recutG (lineQ P l) φ P l k)).IsOrtho (nativeFramePlane (P q)) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro v hv w hw
  change Glennie.inner (v : Glennie.Albert) w = 0
  obtain ⟨y, _, hyv⟩ := (mem_planeA_recutG hF hφ hk _).mp (mem_planeA_coe.mpr hv)
  rw [← hyv]
  exact inner_lineQ_planeA hF hU hq (φ y).property (mem_planeA_coe.mpr hw)

/-- A thirteen-frame code realizing a labelled family of frames. -/
def codeOf (R : SignedPlaneIndex → Fin 3 → Glennie.Albert) (hR : ∀ p, Glennie.Frame (R p))
    (hRU : ∀ p q, p ≠ q → ∀ a b, Glennie.inner (R p a) (R q b) = 1 / 3)
    (e : Fin 13 ≃ SignedPlaneIndex) : TightNativeCode :=
  ⟨fun i => R (e i), fun i => hR (e i), fun hij a b => hRU _ _ (e.injective.ne hij) a b⟩

end Generic

end

end ThirteenPlanes.AlbertGrading.Recut
