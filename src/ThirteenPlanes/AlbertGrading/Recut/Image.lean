module

public import ThirteenPlanes.AlbertGrading.Recut.Count
public import ThirteenPlanes.Shares.ThirteenIncidence

@[expose] public section

/-! Automorphisms preserve the quartet cover of a graded system.

An automorphism taking the graded planes to the rotated planes carries every line algebra
to the unital subalgebra spanned by the corresponding four planes. Thus each pair of rotated
planes lies in a closed quartet. The quartet criterion gives exactly 52 positive shares,
which is equivalent to the line automorphism permuting its four planes. -/

namespace ThirteenPlanes.AlbertGrading.Recut

open ThirteenPlanes.RoundCubics

noncomputable section

theorem jordanAut_one {ψ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert} (hψ : IsJordanAutomorphism ψ) :
    ψ 1 = 1 := by
  have h := hψ 1 (ψ.symm 1)
  rw [Glennie.jordan_unit_left, LinearEquiv.apply_symm_apply, Glennie.jordan_unit_right] at h
  exact h.symm

/-- The generic form of "`ψ` carries the graded system onto the re-cut system". -/
def CarriesG (P : SignedPlaneIndex → Fin 3 → Glennie.Albert)
    (ψ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert) (R : SignedPlaneIndex → Fin 3 → Glennie.Albert) :
    Prop :=
  ∀ p : SignedPlaneIndex, ∃ q : SignedPlaneIndex,
    ∀ x, x ∈ planeA (R q) ↔ ∃ y ∈ planeA (P p), ψ y = x

section Generic

variable {P : SignedPlaneIndex → Fin 3 → Glennie.Albert} (hF : ∀ p, Glennie.Frame (P p))
  (hU : ∀ p q, p ≠ q → ∀ a b, Glennie.inner (P p a) (P q b) = 1 / 3)
  (hclosedAll : ∀ m : SignedPlaneIndex, ∀ x y, x ∈ lineQ P m → y ∈ lineQ P m →
    Glennie.jordan x y ∈ lineQ P m)
  {l : SignedPlaneIndex}
  {φ : lineQ P l ≃ₗ[ℝ] lineQ P l} (hφ : IsSubalgebraAutomorphism (lineQ P l) φ)
  (hmix : ∀ p q r r' : SignedPlaneIndex, p ≠ q → r ≠ r' → r ≠ p → r ≠ q → r' ≠ p → r' ≠ q →
    signedCollinear p q r → signedCollinear p q r' →
    mixedProductSpace nativeEqualCubic (nativeFramePlane (P p)) (nativeFramePlane (P q)) =
      nativeFramePlane (P r) ⊔ nativeFramePlane (P r'))
  (hshare : ∀ p q r : SignedPlaneIndex, p ≠ q → p ≠ r → q ≠ r →
    shareOfThreePlanes nativeEqualCubic (nativeFramePlane (P p)) (nativeFramePlane (P q))
      (nativeFramePlane (P r)) = if signedCollinear p q r then 1 else 0)

include hF hU hclosedAll hφ hmix hshare in
/-- Rotation of four planes on a graded line (ii), second sentence, for the generic re-cut. -/
theorem recutG_not_image (hnot : ¬ PermutesG P l φ) :
    ¬ ∃ ψ : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert, IsJordanAutomorphism ψ ∧
      CarriesG P ψ (recutG (lineQ P l) φ P l) := by
  rintro ⟨ψ, hψ, hcar⟩
  set R := recutG (lineQ P l) φ P l with hRdef
  obtain ⟨hRF, hRU⟩ := recutG_frames hF hU (hclosedAll l) hφ
  choose τ hτ using hcar
  have hτ' (p : SignedPlaneIndex) :
      planeA (R (τ p)) = (planeA (P p)).map (ψ : Glennie.Albert →ₗ[ℝ] Glennie.Albert) := by
    ext x
    rw [hτ p x, Submodule.mem_map]
    rfl
  have τinj : Function.Injective τ := by
    intro p p' hpp
    apply graded_planes_injective hF hU
    rw [← planeA_eq_iff]
    apply Submodule.map_injective_of_injective (f := (ψ : Glennie.Albert →ₗ[ℝ] Glennie.Albert))
      ψ.injective
    rw [← hτ', ← hτ', hpp]
  have τsurj : Function.Surjective τ := Finite.injective_iff_surjective.mp τinj
  have hψ1 := jordanAut_one hψ
  let e : Fin 13 ≃ SignedPlaneIndex := (Fintype.equivFinOfCardEq signedPlaneIndex_card).symm
  let c := codeOf R hRF hRU e
  have hc : ∀ i, c.point i = R (e i) := fun _ => rfl
  have hcP (i : Fin 13) : c.decomposition.plane i = nativeFramePlane (R (e i)) := rfl
  -- every pair of re-cut planes lies in a quartet
  have cover : ∀ i j : Fin 13, i ≠ j →
      ∃ B, IsPlaneQuartet nativeEqualCubic c.decomposition B ∧ i ∈ B ∧ j ∈ B := by
    intro i j _
    obtain ⟨p1, hp1⟩ := τsurj (e i)
    obtain ⟨p2, hp2⟩ := τsurj (e j)
    obtain ⟨m, hm1, hm2⟩ := exists_common_line p1 p2
    let B := (signedLinePoints m).image (fun p => e.symm (τ p))
    have hBinj : Function.Injective (fun p => e.symm (τ p)) := e.symm.injective.comp τinj
    have hon (p : SignedPlaneIndex) (hp : p ∈ signedLinePoints m) : signedPointOnLine p m := by
      simpa [signedLinePoints] using hp
    refine ⟨B, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hBinj, signedLinePoints_card]
    · -- closedness of the sum of the four planes
      let O := ⨆ t ∈ B, c.decomposition.plane t
      let ψQ := (lineQ P m).map (ψ : Glennie.Albert →ₗ[ℝ] Glennie.Albert)
      have hplane (p : SignedPlaneIndex) :
          c.decomposition.plane (e.symm (τ p)) = nativeFramePlane (R (τ p)) := by
        rw [hcP, e.apply_symm_apply]
      have hle (v : NativeTraceless) (hv : v ∈ O) : (v : Glennie.Albert) ∈ ψQ := by
        have hO : O ≤ ψQ.comap (Glennie.traceLinear.ker.subtype) := by
          refine iSup₂_le fun t ht => ?_
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
          intro w hw
          rw [hplane] at hw
          have hw' : (w : Glennie.Albert) ∈ planeA (R (τ p)) := mem_planeA_coe.mpr hw
          rw [hτ'] at hw'
          obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.mp hw'
          exact Submodule.mem_map.mpr ⟨y, planeA_le_lineQ (hon p hp) hy, hyw⟩
        exact hO hv
      have hge (v : NativeTraceless) (hv : (v : Glennie.Albert) ∈ ψQ) : v ∈ O := by
        obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.mp hv
        have hz' := hz
        unfold lineQ at hz'
        rw [Submodule.span_union] at hz'
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz'
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp ha
        let O' := O.map Glennie.traceLinear.ker.subtype
        have hbO : (ψ : Glennie.Albert →ₗ[ℝ] Glennie.Albert) b ∈ O' := by
          have hspan : Submodule.span ℝ (⋃ (p : SignedPlaneIndex) (_ : signedPointOnLine p m),
              (planeA (P p) : Set Glennie.Albert)) ≤
              O'.comap (ψ : Glennie.Albert →ₗ[ℝ] Glennie.Albert) := by
            rw [Submodule.span_le]
            intro y hy
            obtain ⟨p, hy⟩ := Set.mem_iUnion.mp hy
            obtain ⟨hp, hy⟩ := Set.mem_iUnion.mp hy
            have hψy : ψ y ∈ planeA (R (τ p)) := (hτ p (ψ y)).mpr ⟨y, hy, rfl⟩
            obtain ⟨w, hw, hwy⟩ := hψy
            have hpm : p ∈ signedLinePoints m := by simp [signedLinePoints, hp]
            have hwO : w ∈ O := by
              have : c.decomposition.plane (e.symm (τ p)) ≤ O :=
                le_iSup₂_of_le (e.symm (τ p)) (Finset.mem_image_of_mem _ hpm) le_rfl
              exact this (by rw [hplane]; exact hw)
            exact ⟨w, hwO, hwy⟩
          exact hspan hb
        obtain ⟨w, hwO, hwb⟩ := hbO
        have hwb' : ψ b = (w : Glennie.Albert) := hwb.symm
        have htr := congrArg Glennie.trace hzv
        rw [map_add, map_smul] at htr
        change Glennie.trace (t • ψ 1 + ψ b) = Glennie.trace (v : Glennie.Albert) at htr
        rw [hψ1, Glennie.trace_add, Glennie.trace_smul, Glennie.trace_unit, nativeTraceless_trace,
          hwb', nativeTraceless_trace] at htr
        have ht0 : t = 0 := by linarith
        have hvw : v = w := by
          apply Subtype.ext
          rw [← hzv, map_add, map_smul, ht0, zero_smul, zero_add]
          exact hwb.symm
        rw [hvw]
        exact hwO
      intro x y hx hy
      apply hge
      obtain ⟨x', hx'Q, hx'⟩ := Submodule.mem_map.mp (hle x hx)
      obtain ⟨y', hy'Q, hy'⟩ := Submodule.mem_map.mp (hle y hy)
      have hj : Glennie.jordan (x : Glennie.Albert) y ∈ ψQ := by
        rw [← hx', ← hy']
        change Glennie.jordan (ψ x') (ψ y') ∈ ψQ
        rw [← hψ]
        exact Submodule.mem_map_of_mem (hclosedAll m _ _ hx'Q hy'Q)
      have h1 : (1 : Glennie.Albert) ∈ ψQ := by
        rw [← hψ1]
        exact Submodule.mem_map_of_mem (one_mem_lineQ hF)
      change Glennie.traceless (Glennie.jordan (x : Glennie.Albert) y) ∈ ψQ
      exact ψQ.sub_mem hj (ψQ.smul_mem _ h1)
    · exact Finset.mem_image.mpr ⟨p1, by simp [signedLinePoints, hm1], by rw [hp1]; simp⟩
    · exact Finset.mem_image.mpr ⟨p2, by simp [signedLinePoints, hm2], by rw [hp2]; simp⟩
  have binary := (planeShare_binary_iff_quartet_cover nativeRoundCubic (code_closed c)).mpr cover
  have sparse := (thirteenPlane_positive_eq_fifty_two_iff nativeRoundCubic (code_closed c)).mpr binary
  exact hnot ((recutG_card_iff hF hU (hclosedAll l) hφ hmix hshare c e hc).mp sparse)

end Generic

end

end ThirteenPlanes.AlbertGrading.Recut
