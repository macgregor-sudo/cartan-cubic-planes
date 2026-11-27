module

public import ThirteenPlanes.MixedGram

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped RealInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {h : SymmetricCubic V} {c : ℝ} {U U' : Submodule ℝ V}

private theorem polarized_plane_slice (round : IsRound h c) (closed : IsClosedPiece h U)
    (dim : Module.finrank ℝ U = 2) (x y : U) (z : Uᗮ) :
    h.L (h.L (x : V) y) (z : V) + (2 : ℝ) • h.L (x : V) (h.L (y : V) z) =
      (c * ⟪(x : V), (y : V)⟫) • (z : V) := by
  have hc := congrArg (fun A : Module.End ℝ Uᗮ => (A z : V))
    (closedPlane_slices_commute round closed dim x y).eq
  change h.L (x : V) (h.L (y : V) z) = h.L (y : V) (h.L (x : V) z) at hc
  apply ext_inner_right ℝ
  intro w
  have ha : ⟪h.L (h.L (x : V) y) (z : V), w⟫ = ⟪h.L (x : V) y, h.L (z : V) w⟫ := by
    rw [h.L_comm (h.L (x : V) y) (z : V)]
    exact h.L_isSymmetric (z : V) _ _
  have hb : ⟪h.L (x : V) (h.L (y : V) z), w⟫ = ⟪h.L (x : V) z, h.L (y : V) w⟫ := by
    rw [hc]
    exact h.L_isSymmetric (y : V) _ _
  have hd : ⟪h.L (x : V) (h.L (y : V) z), w⟫ = ⟪h.L (x : V) w, h.L (y : V) z⟫ :=
    (h.L_isSymmetric (x : V) _ _).trans (real_inner_comm _ _)
  have hp := polarized round (x : V) y z w
  have hxz := Submodule.inner_right_of_mem_orthogonal x.property z.property
  have hyz := Submodule.inner_right_of_mem_orthogonal y.property z.property
  simp only [hxz, hyz, mul_zero, zero_mul, add_zero, ← ha, ← hb, ← hd] at hp
  simp only [inner_add_left, real_inner_smul_left]
  linear_combination hp

omit [FiniteDimensional ℝ V] in
private theorem product_space_swap (h : SymmetricCubic V) (U U' : Submodule ℝ V) :
    mixedProductSpace h U U' = mixedProductSpace h U' U := by
  rw [mixedProductSpace_eq_span, mixedProductSpace_eq_span]
  apply le_antisymm <;> apply Submodule.map₂_le.mpr
  · intro x hx y hy
    rw [h.L_comm]
    exact Submodule.apply_mem_map₂ _ hy hx
  · intro x hx y hy
    rw [h.L_comm]
    exact Submodule.apply_mem_map₂ _ hy hx

private theorem left_slice_preserves_pair_octet (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (dim : Module.finrank ℝ U = 2) (x : U) :
    ((U ⊔ U') ⊔ mixedProductSpace h U U') ≤
      ((U ⊔ U') ⊔ mixedProductSpace h U U').comap (h.L x) := by
  let W := mixedProductSpace h U U'
  let O := (U ⊔ U') ⊔ W
  have oU : U ≤ O := le_sup_left.trans le_sup_left
  have oV : U' ≤ O := le_sup_right.trans le_sup_left
  have oW : W ≤ O := le_sup_right
  have hp {x y : V} (hx : x ∈ U) (hy : y ∈ U') : h.L x y ∈ W := by
    rw [show W = mixedProductSpace h U U' from rfl, mixedProductSpace_eq_span]
    exact Submodule.apply_mem_map₂ _ hx hy
  have hv : U' ≤ Uᗮ := Submodule.isOrtho_iff_le.mp orth.symm
  refine sup_le (sup_le ?_ ?_) ?_
  · intro y hy
    exact oU (closed x.property hy)
  · intro y hy
    exact oW (hp x.property hy)
  · change W ≤ O.comap (h.L x)
    rw [show W = mixedProductSpace h U U' from rfl, mixedProductSpace_eq_span]
    apply Submodule.map₂_le.mpr
    intro y hy z hz
    change h.L (x : V) (h.L y z) ∈ O
    have hs := polarized_plane_slice round closed dim x ⟨y, hy⟩ ⟨z, hv hz⟩
    change h.L (h.L (x : V) y) z + (2 : ℝ) • h.L (x : V) (h.L y z) =
      (c * ⟪(x : V), y⟫) • z at hs
    have he : h.L (x : V) (h.L y z) =
        (1 / 2 : ℝ) • ((c * ⟪(x : V), y⟫) • z - h.L (h.L (x : V) y) z) := by
      rw [← hs, add_sub_cancel_left, smul_smul]
      norm_num
    rw [he]
    exact O.smul_mem _ (O.sub_mem (O.smul_mem _ (oV hz)) (oW (hp (closed x.property hy) hz)))

/-- The sum of two orthogonal closed round planes with their mixed product space is closed.
This is the closure assertion in the two-plane octet theorem. -/
theorem pairOctet_closed (round : IsRound h c) (orth : U.IsOrtho U')
    (closed : IsClosedPiece h U) (closed' : IsClosedPiece h U')
    (dim : Module.finrank ℝ U = 2) (dim' : Module.finrank ℝ U' = 2) :
    IsClosedPiece h ((U ⊔ U') ⊔ mixedProductSpace h U U') := by
  let W := mixedProductSpace h U U'
  let O := (U ⊔ U') ⊔ W
  have oU : U ≤ O := le_sup_left.trans le_sup_left
  have oV : U' ≤ O := le_sup_right.trans le_sup_left
  have left {x y : V} (hx : x ∈ U) (hy : y ∈ O) : h.L x y ∈ O :=
    left_slice_preserves_pair_octet round orth closed dim ⟨x, hx⟩ hy
  have right {x y : V} (hx : x ∈ U') (hy : y ∈ O) : h.L x y ∈ O := by
    have hs := left_slice_preserves_pair_octet round orth.symm closed' dim' ⟨x, hx⟩
    rw [sup_comm U' U, product_space_swap h U' U] at hs
    exact hs hy
  have outside (x : V) (hx : O ≤ O.comap (h.L x)) {z : V} (hz : z ∈ Oᗮ) :
      h.L x z ∈ Oᗮ := by
    apply (O.mem_orthogonal _).mpr
    intro w hw
    rw [← h.L_isSymmetric x w z]
    have hw' : h.L x w ∈ O := hx hw
    exact Submodule.inner_right_of_mem_orthogonal hw' hz
  intro w v hw hv
  have hU : U ≤ O.comap (h.L w) := fun x hx => by
    change h.L w x ∈ O
    rw [h.L_comm]
    exact left hx hw
  have hV : U' ≤ O.comap (h.L w) := fun x hx => by
    change h.L w x ∈ O
    rw [h.L_comm]
    exact right hx hw
  have hW : W ≤ O.comap (h.L w) := by
    rw [show W = mixedProductSpace h U U' from rfl, mixedProductSpace_eq_span]
    apply Submodule.map₂_le.mpr
    intro x hx y hy
    change h.L w (h.L x y) ∈ O
    rw [← Submodule.orthogonal_orthogonal O]
    apply (Oᗮ.mem_orthogonal _).mpr
    intro z hz
    have hxy := orth.inner_eq hx hy
    have hxz := Submodule.inner_right_of_mem_orthogonal (oU hx) hz
    have hyz := Submodule.inner_right_of_mem_orthogonal (oV hy) hz
    have hp := polarized round x y w z
    have hb : ⟪h.L x w, h.L y z⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (left hx hw) (outside y (fun _ hy' => right hy hy') hz)
    have hc : ⟪h.L x z, h.L y w⟫ = 0 :=
      (real_inner_comm _ _).trans
        (Submodule.inner_right_of_mem_orthogonal (right hy hw) (outside x (fun _ hx' => left hx hx') hz))
    simp only [hxy, hxz, hyz, hb, hc, mul_zero, zero_mul, add_zero] at hp
    rw [← h.L_isSymmetric w z (h.L x y)]
    exact (real_inner_comm _ _).trans hp
  exact (sup_le (sup_le hU hV) hW : O ≤ O.comap (h.L w)) hv

end
end ThirteenPlanes.RoundCubics
