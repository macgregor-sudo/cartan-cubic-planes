module

public import ThirteenPlanes.AlbertGrading.Generation.Windows
public import ThirteenPlanes.AlbertGrading.Generation.ComplexTrace

@[expose] public section

/-! Classification of a proper subalgebra of dimension at least nine containing two unbiased
frames: it is a copy of `H₃(ℂ)` (dimension 9) or of `H₃(ℍ)` (dimension 15).

Route: the dichotomy `lem_five_sub .O` puts the subalgebra in a quaternionic window (line
subalgebras are excluded by the two unbiased frames); transported to the standard quaternionic
window, `lem_five_sub .H` either gives the whole window, or a line (excluded again), or a copy of
`H₃(ℂ)`, which the dimension bound fills. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading

open AlbertSequential

/-- A frame transported between two quaternionic embeddings is a frame. -/
theorem transport_frame {ι₁ ι₂ : QuaternionHermitian3 →ₗ[ℝ] Glennie.Albert} (h₁ : QEmb ι₁)
    (h₂ : QEmb ι₂) {s : Fin 3 → Glennie.Albert} (hs : Glennie.Frame s)
    (M : Fin 3 → QuaternionHermitian3) (hM : ∀ a, ι₁ (M a) = s a) :
    Glennie.Frame (fun a => ι₂ (M a)) where
  trace_one a := by
    change Glennie.trace (ι₂ (M a)) = 1
    rw [h₂.trace, ← h₁.trace, hM, hs.trace_one]
  idempotent a := by
    change Glennie.jordan (ι₂ (M a)) (ι₂ (M a)) = ι₂ (M a)
    have h : qjordan (M a) (M a) = M a :=
      h₁.injective (by rw [h₁.map_qjordan, hM, hs.idempotent])
    rw [← h₂.map_qjordan, h]
  orthogonal a b hab := by
    change Glennie.jordan (ι₂ (M a)) (ι₂ (M b)) = 0
    have h : qjordan (M a) (M b) = 0 :=
      h₁.injective (by rw [h₁.map_qjordan, hM, hM, hs.orthogonal a b hab, map_zero])
    rw [← h₂.map_qjordan, h, map_zero]
  sum_unit := by
    change ι₂ (M 0) + ι₂ (M 1) + ι₂ (M 2) = 1
    have h : M 0 + M 1 + M 2 = 1 :=
      h₁.injective (by rw [map_add, map_add, hM, hM, hM, hs.sum_unit, h₁.unit])
    rw [← map_add, ← map_add, h, h₂.unit]

theorem transport_inner {ι₁ ι₂ : QuaternionHermitian3 →ₗ[ℝ] Glennie.Albert} (h₁ : QEmb ι₁)
    (h₂ : QEmb ι₂) (M N : QuaternionHermitian3) :
    Glennie.inner (ι₂ M) (ι₂ N) = Glennie.inner (ι₁ M) (ι₁ N) := by
  rw [← traceForm_coe_eq h₂, traceForm_coe_eq h₁]

/-- A copy of `H₃(ℂ)` inside the standard quaternionic window, filling the transport of `B`,
makes `B` a copy of `H₃(ℂ)`. -/
theorem complexCopy_of_window (W : QuaternionicWindow) (B : NativeJordanSubalgebra)
    (hBW : B.carrier ≤ LinearMap.range W.embedding) (Q : NativeJordanSubalgebra)
    (ψ : JordanSubalgebraIso (H3Subalgebra .C) Q)
    (hQ : Q.carrier =
      (B.carrier.comap W.embedding).map standardQuaternionicWindow.embedding) :
    IsComplexCopy (B.carrier.map (coordEquiv : Albert →ₗ[ℝ] Glennie.Albert)) := by
  set Sw := standardQuaternionicWindow
  set C := B.carrier.comap W.embedding
  have hQS : Q.carrier ≤ LinearMap.range Sw.embedding := hQ ▸ LinearMap.map_le_range
  set c0 := standardComplexWindow.embedding
  have hc0 (x : ComplexHermitian3) : c0 x ∈ (H3Subalgebra .C).carrier := by
    rw [H3Subalgebra_C_eq_standardComplexWindow]
    exact ⟨x, rfl⟩
  let h0 : ComplexHermitian3 →ₗ[ℝ] (H3Subalgebra .C).carrier := LinearMap.codRestrict _ c0 hc0
  let eS := LinearEquiv.ofInjective Sw.embedding Sw.injective
  let χ : ComplexHermitian3 →ₗ[ℝ] QuaternionHermitian3 :=
    eS.symm.toLinearMap ∘ₗ Submodule.inclusion hQS ∘ₗ ψ.toLinearEquiv.toLinearMap ∘ₗ h0
  have hχ (x : ComplexHermitian3) :
      Sw.embedding (χ x) = ((ψ.toLinearEquiv (h0 x) : Q.carrier) : Albert) := by
    have h := eS.apply_symm_apply (Submodule.inclusion hQS (ψ.toLinearEquiv (h0 x)))
    exact congrArg Subtype.val h
  have hχC (x : ComplexHermitian3) : χ x ∈ C := by
    have hmem : Sw.embedding (χ x) ∈ C.map Sw.embedding := by
      rw [hχ, ← hQ]
      exact (ψ.toLinearEquiv (h0 x)).2
    obtain ⟨M, hM, hMeq⟩ := hmem
    rw [← Sw.injective hMeq]
    exact hM
  have hW := window_qemb W
  let φ : ComplexHermitian3 →ₗ[ℝ] Glennie.Albert :=
    ((coordEquiv : Albert →ₗ[ℝ] Glennie.Albert) ∘ₗ W.embedding) ∘ₗ χ
  have hφ (x : ComplexHermitian3) :
      φ x = ((coordEquiv : Albert →ₗ[ℝ] Glennie.Albert) ∘ₗ W.embedding) (χ x) := rfl
  have χinj : Function.Injective χ := by
    intro x y hxy
    have h1 := congrArg Sw.embedding hxy
    rw [hχ, hχ] at h1
    have h2 : ψ.toLinearEquiv (h0 x) = ψ.toLinearEquiv (h0 y) := Subtype.ext h1
    have h3 := congrArg Subtype.val (ψ.toLinearEquiv.injective h2)
    exact standardComplexWindow.injective h3
  have χunit : χ 1 = 1 := by
    apply Sw.injective
    rw [hχ, Sw.unit]
    have hh : h0 1 = ⟨albertUnit, (H3Subalgebra .C).unit_mem⟩ :=
      Subtype.ext standardComplexWindow.unit
    rw [hh, ψ.map_unit]
  have χprod (x y z : ComplexHermitian3)
      (hz : (z : Matrix (Fin 3) (Fin 3) ℂ) =
        (1 / 2 : ℝ) • ((x : Matrix (Fin 3) (Fin 3) ℂ) * y + y * x)) :
      χ z = qjordan (χ x) (χ y) := by
    apply Sw.injective
    rw [Sw.preserves_product (χ x) (χ y) (qjordan (χ x) (χ y)) rfl, hχ, hχ, hχ]
    have hh : h0 z = ⟨jordanMul (h0 x).1 (h0 y).1,
        (H3Subalgebra .C).product_mem _ (h0 x).2 _ (h0 y).2⟩ :=
      Subtype.ext (standardComplexWindow.preserves_product x y z hz)
    rw [hh, ψ.map_jordan]
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact hW.injective.comp χinj
  · ext b
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨W.embedding (χ x), hχC x, rfl⟩
    · rintro ⟨b', hb', rfl⟩
      obtain ⟨M, rfl⟩ := hBW hb'
      have hMQ : Sw.embedding M ∈ Q.carrier := by
        rw [hQ]
        exact ⟨M, hb', rfl⟩
      set z := ψ.toLinearEquiv.symm ⟨Sw.embedding M, hMQ⟩
      have hrange (y : Albert) (hy : y ∈ (H3Subalgebra .C).carrier) : y ∈ LinearMap.range c0 := by
        rw [H3Subalgebra_C_eq_standardComplexWindow] at hy
        exact hy
      have hz : (z : Albert) ∈ LinearMap.range c0 := hrange _ z.2
      obtain ⟨x, hx⟩ := hz
      have hh0 : h0 x = z := Subtype.ext hx
      have hχx : χ x = M := by
        apply Sw.injective
        rw [hχ, hh0]
        simp [z]
      refine ⟨x, ?_⟩
      rw [hφ, hχx]
      rfl
  · rw [hφ, χunit]
    exact hW.unit
  · intro x y z hz
    rw [hφ, χprod x y z hz, hW.map_qjordan]
    rfl
  · exact trace_of_complex_jordan_hom φ (by rw [hφ, χunit]; exact hW.unit)
      (fun x y z hz => by rw [hφ, χprod x y z hz, hW.map_qjordan]; rfl)

/-- Classification of a proper subalgebra of dimension at least nine containing two unbiased
frames. -/
theorem classify {p q : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (hq : Glennie.Frame q)
    (hpq : ∀ a b, Glennie.inner (p a) (q b) = 1 / 3) (B : NativeJordanSubalgebra)
    (hpB : ∀ a, coordEquiv.symm (p a) ∈ B.carrier) (hqB : ∀ b, coordEquiv.symm (q b) ∈ B.carrier)
    (hB : B.carrier ≠ ⊤) (h9 : 9 ≤ Module.finrank ℝ B.carrier) :
    (Module.finrank ℝ B.carrier = 9 ∧
        IsComplexCopy (B.carrier.map (coordEquiv : Albert →ₗ[ℝ] Glennie.Albert))) ∨
      (Module.finrank ℝ B.carrier = 15 ∧
        IsQuaternionicCopy (B.carrier.map (coordEquiv : Albert →ₗ[ℝ] Glennie.Albert))) := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  have hlt : B.carrier < (H3Subalgebra .O).carrier := by
    rw [H3Subalgebra_O_eq_top]
    exact lt_top_iff_ne_top.mpr hB
  rcases lem_five_sub .O B hlt with ⟨s, hs, _, hline⟩ | ⟨W, hW⟩
  · exact absurd hline (not_le_lineSubalgebra hp hq hpq B hpB hqB s hs)
  have hBW : B.carrier ≤ LinearMap.range W.embedding := by
    rw [W.range_eq]
    exact hW
  set Sw := standardQuaternionicWindow
  set C := B.carrier.comap W.embedding
  let Bs : NativeJordanSubalgebra :=
    { carrier := C.map Sw.embedding
      unit_mem := ⟨1, by
        change W.embedding 1 ∈ B.carrier
        rw [W.unit]
        exact B.unit_mem, Sw.unit⟩
      product_mem := by
        rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
        refine ⟨qjordan M N, ?_, Sw.preserves_product M N _ rfl⟩
        change W.embedding (qjordan M N) ∈ B.carrier
        rw [W.preserves_product M N _ rfl]
        exact B.product_mem _ hM _ hN }
  have hBsH : Bs.carrier ≤ (H3Subalgebra .H).carrier := by
    rw [H3Subalgebra_H_eq_standardQuaternionicWindow, ← Sw.range_eq]
    exact LinearMap.map_le_range
  have hCfin : Module.finrank ℝ C = Module.finrank ℝ B.carrier := by
    have h := (Submodule.equivMapOfInjective W.embedding W.injective C).finrank_eq
    rw [Submodule.map_comap_eq, inf_eq_right.mpr hBW] at h
    exact h
  have hBsfin : Module.finrank ℝ Bs.carrier = Module.finrank ℝ B.carrier := by
    rw [← hCfin]
    exact (Submodule.equivMapOfInjective Sw.embedding Sw.injective C).finrank_eq.symm
  have hH15 : Module.finrank ℝ (H3Subalgebra .H).carrier = 15 := finrank_H3Subalgebra .H
  have hC9 : Module.finrank ℝ (H3Subalgebra .C).carrier = 9 := finrank_H3Subalgebra .C
  have hqW := window_qemb W
  have hqS := window_qemb Sw
  have pre (x : Glennie.Albert) (hx : coordEquiv.symm x ∈ B.carrier) :
      ∃ M : QuaternionHermitian3, M ∈ C ∧
        ((coordEquiv : Albert →ₗ[ℝ] Glennie.Albert) ∘ₗ W.embedding) M = x := by
    obtain ⟨M, hM⟩ := hBW hx
    refine ⟨M, ?_, ?_⟩
    · change W.embedding M ∈ B.carrier
      rw [hM]
      exact hx
    · change coordEquiv (W.embedding M) = x
      rw [hM, LinearEquiv.apply_symm_apply]
  choose Mp hMpC hMp using fun a => pre (p a) (hpB a)
  choose Mq hMqC hMq using fun a => pre (q a) (hqB a)
  by_cases hfull : Bs.carrier = (H3Subalgebra .H).carrier
  · right
    have h15 : Module.finrank ℝ B.carrier = 15 := by rw [← hBsfin, hfull, hH15]
    refine ⟨h15, ?_⟩
    have hQH15 : Module.finrank ℝ QuaternionHermitian3 = 15 := by
      rw [← LinearMap.finrank_range_of_inj Sw.injective, Sw.range_eq,
        ← H3Subalgebra_H_eq_standardQuaternionicWindow, hH15]
    have hBeq : B.carrier = LinearMap.range W.embedding := by
      apply Submodule.eq_of_le_of_finrank_eq hBW
      rw [h15, LinearMap.finrank_range_of_inj W.injective, hQH15]
    refine ⟨(coordEquiv : Albert →ₗ[ℝ] Glennie.Albert) ∘ₗ W.embedding, hqW.injective, ?_,
      hqW.unit, hqW.product, hqW.trace⟩
    rw [LinearMap.range_comp, hBeq]
  · left
    have hlt' : Bs.carrier < (H3Subalgebra .H).carrier := lt_of_le_of_ne hBsH hfull
    rcases lem_five_sub .H Bs hlt' with ⟨s, hs, _, hline⟩ | ⟨Q, _, ⟨ψ⟩, hBsQ⟩
    · have hp' := transport_frame hqW hqS hp Mp hMp
      have hq' := transport_frame hqW hqS hq Mq hMq
      refine absurd hline (not_le_lineSubalgebra hp' hq' ?_ Bs ?_ ?_ s hs)
      · intro a b
        change Glennie.inner (((coordEquiv : Albert →ₗ[ℝ] Glennie.Albert) ∘ₗ Sw.embedding) (Mp a))
          (((coordEquiv : Albert →ₗ[ℝ] Glennie.Albert) ∘ₗ Sw.embedding) (Mq b)) = 1 / 3
        rw [transport_inner hqW hqS, hMp, hMq, hpq]
      · intro a
        change coordEquiv.symm (coordEquiv (Sw.embedding (Mp a))) ∈ C.map Sw.embedding
        rw [LinearEquiv.symm_apply_apply]
        exact ⟨Mp a, hMpC a, rfl⟩
      · intro a
        change coordEquiv.symm (coordEquiv (Sw.embedding (Mq a))) ∈ C.map Sw.embedding
        rw [LinearEquiv.symm_apply_apply]
        exact ⟨Mq a, hMqC a, rfl⟩
    · have hQ9 : Module.finrank ℝ Q.carrier = 9 := by
        rw [← ψ.toLinearEquiv.finrank_eq, hC9]
      have hBsQeq : Bs.carrier = Q.carrier :=
        Submodule.eq_of_le_of_finrank_le hBsQ (by rw [hQ9, hBsfin]; exact h9)
      refine ⟨by rw [← hBsfin, hBsQeq, hQ9], ?_⟩
      exact complexCopy_of_window W B hBW Q ψ hBsQeq.symm

end ThirteenPlanes.AlbertGrading
