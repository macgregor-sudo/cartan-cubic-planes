module

public import ThirteenPlanes.AlbertGrading.Generation.Statements

@[expose] public section

/-! Transport between the compact Albert carrier `Glennie.Albert` and the native carrier
`AlbertSequential.Albert` through the literal coordinate equivalence
`AlbertSequential.NativeAnalysis.recoveredCoordinateEquiv`, plus elementary facts about generated
subalgebras, traceless parts and unbiased frames. -/

noncomputable section

namespace ThirteenPlanes.AlbertGrading

open AlbertSequential

/-- The coordinate equivalence of the two Albert carriers. -/
abbrev coordEquiv : Albert ≃ₗ[ℝ] Glennie.Albert := NativeAnalysis.recoveredCoordinateEquiv

theorem coordEquiv_jordan (x y : Albert) :
    coordEquiv (jordanMul x y) = Glennie.jordan (coordEquiv x) (coordEquiv y) :=
  NativeAnalysis.recoveredCoordinateEquiv_jordanMul x y

theorem coordEquiv_symm_jordan (a b : Glennie.Albert) :
    coordEquiv.symm (Glennie.jordan a b) = jordanMul (coordEquiv.symm a) (coordEquiv.symm b) := by
  apply coordEquiv.injective
  rw [coordEquiv_jordan, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

theorem coordEquiv_trace (x : Albert) : Glennie.trace (coordEquiv x) = albertTrace x :=
  NativeAnalysis.recoveredCoordinateEquiv_trace x

theorem coordEquiv_unit : coordEquiv albertUnit = 1 :=
  NativeAnalysis.recoveredCoordinateEquiv_unit

theorem coordEquiv_symm_one : coordEquiv.symm 1 = albertUnit := by
  rw [← coordEquiv_unit, LinearEquiv.symm_apply_apply]

theorem albertTrace_coordEquiv_symm (a : Glennie.Albert) :
    albertTrace (coordEquiv.symm a) = Glennie.trace a := by
  rw [← coordEquiv_trace, LinearEquiv.apply_symm_apply]

theorem tracePairing_coordEquiv_symm (a b : Glennie.Albert) :
    tracePairing (coordEquiv.symm a) (coordEquiv.symm b) = Glennie.inner a b := by
  rw [tracePairing, ← coordEquiv_symm_jordan, albertTrace_coordEquiv_symm]
  rfl

theorem isAtom_coordEquiv_symm {a : Glennie.Albert} (hidem : Glennie.jordan a a = a)
    (htr : Glennie.trace a = 1) : IsAtom (coordEquiv.symm a) :=
  ⟨by rw [← coordEquiv_symm_jordan, hidem], by rw [albertTrace_coordEquiv_symm, htr]⟩

/-! ### Generated subalgebras -/

theorem subset_generated (X : Set Glennie.Albert) : X ⊆ generated X :=
  fun _ hx => Submodule.mem_sInf.mpr fun _ hC => hC.1 hx

theorem one_mem_generated (X : Set Glennie.Albert) : (1 : Glennie.Albert) ∈ generated X :=
  Submodule.mem_sInf.mpr fun _ hC => hC.2.1

theorem jordan_mem_generated (X : Set Glennie.Albert) {x y : Glennie.Albert}
    (hx : x ∈ generated X) (hy : y ∈ generated X) : Glennie.jordan x y ∈ generated X :=
  Submodule.mem_sInf.mpr fun C hC =>
    hC.2.2 x (Submodule.mem_sInf.mp hx C hC) y (Submodule.mem_sInf.mp hy C hC)

theorem generated_le {X : Set Glennie.Albert} {C : Submodule ℝ Glennie.Albert} (hX : X ⊆ C)
    (h1 : (1 : Glennie.Albert) ∈ C) (hj : ∀ x ∈ C, ∀ y ∈ C, Glennie.jordan x y ∈ C) :
    generated X ≤ C :=
  sInf_le ⟨hX, h1, hj⟩

theorem generated_mono {X Y : Set Glennie.Albert} (h : X ⊆ Y) : generated X ≤ generated Y :=
  generated_le (h.trans (subset_generated Y)) (one_mem_generated Y)
    (fun _ hx _ hy => jordan_mem_generated Y hx hy)

/-- The Glennie generated subalgebra is the coordinate image of the generated subalgebra in the native matrix coordinates. -/
theorem generated_eq_map (X : Set Glennie.Albert) :
    generated X =
      (generatedSubalgebra (coordEquiv.symm '' X)).carrier.map (coordEquiv : Albert →ₗ[ℝ] _) := by
  apply le_antisymm
  · apply generated_le
    · intro x hx
      refine ⟨coordEquiv.symm x, subset_generatedSubalgebra _ ⟨x, hx, rfl⟩, ?_⟩
      exact LinearEquiv.apply_symm_apply _ x
    · exact ⟨albertUnit, (generatedSubalgebra _).unit_mem, coordEquiv_unit⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      refine ⟨jordanMul a b, (generatedSubalgebra _).product_mem a ha b hb, ?_⟩
      exact coordEquiv_jordan a b
  · rw [Submodule.map_le_iff_le_comap]
    let B : NativeJordanSubalgebra :=
      { carrier := (generated X).comap (coordEquiv : Albert →ₗ[ℝ] _)
        unit_mem := by
          change coordEquiv albertUnit ∈ generated X
          rw [coordEquiv_unit]; exact one_mem_generated X
        product_mem := by
          intro x hx y hy
          change coordEquiv (jordanMul x y) ∈ generated X
          rw [coordEquiv_jordan]
          exact jordan_mem_generated X hx hy }
    have hle : generatedSubalgebra (coordEquiv.symm '' X) ≤ B := by
      apply generatedSubalgebra_le
      rintro _ ⟨x, hx, rfl⟩
      change coordEquiv (coordEquiv.symm x) ∈ generated X
      rw [LinearEquiv.apply_symm_apply]
      exact subset_generated X hx
    exact hle

theorem finrank_map_coordEquiv (C : Submodule ℝ Albert) :
    Module.finrank ℝ (C.map (coordEquiv : Albert →ₗ[ℝ] Glennie.Albert)) = Module.finrank ℝ C :=
  LinearEquiv.finrank_map_eq coordEquiv C

theorem map_coordEquiv_eq_top_iff (C : Submodule ℝ Albert) :
    C.map (coordEquiv : Albert →ₗ[ℝ] Glennie.Albert) = ⊤ ↔ C = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    have hx : coordEquiv x ∈ C.map (coordEquiv : Albert →ₗ[ℝ] Glennie.Albert) := by
      rw [h]; trivial
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [coordEquiv.injective hyx] at hy
  · intro h
    rw [h, Submodule.map_top, LinearEquiv.range]

/-! ### Traceless parts -/

theorem finrank_tracelessPart (C : Submodule ℝ Glennie.Albert) (h1 : (1 : Glennie.Albert) ∈ C) :
    Module.finrank ℝ (tracelessPart C) + 1 = Module.finrank ℝ C := by
  let f : C →ₗ[ℝ] ℝ := Glennie.traceLinear.domRestrict C
  have hsurj : Function.Surjective f := by
    intro r
    refine ⟨⟨(r / 3) • (1 : Glennie.Albert), C.smul_mem _ h1⟩, ?_⟩
    change Glennie.trace ((r / 3) • (1 : Glennie.Albert)) = r
    rw [Glennie.trace_smul, Glennie.trace_unit]
    ring
  have hrk := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hrk
  have hker : Module.finrank ℝ (LinearMap.ker f) = Module.finrank ℝ (tracelessPart C) := by
    let g : LinearMap.ker f ≃ₗ[ℝ] tracelessPart C :=
      { toFun := fun x => ⟨(x : C), (x : C).2, by
          have hx := x.2
          rw [LinearMap.mem_ker] at hx
          exact hx⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, by
          rw [LinearMap.mem_ker]
          exact y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact g.finrank_eq
  omega

/-! ### Unbiased frames -/

/-- The centered idempotent of a frame lies in the frame plane. -/
theorem center_mem_framePlane {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (a : Fin 3) :
    nativeCenter (p a) ∈ nativeFramePlane p := by
  let u : Fin 3 → ℝ := Pi.single a 1
  have hu : ∑ b, u b = 1 := by simp [u]
  have hpoint : nativeFrameSynthesis p u = p a := by
    simp [nativeFrameSynthesis, u, Pi.single_apply]
  have hsum : (∑ b, (u b - (∑ k, u k) / 3)) = 0 := by
    rw [Finset.sum_sub_distrib, hu]
    norm_num
  obtain ⟨v, hv⟩ := nativeFrameEntries_surjective_of_zero_sum _ hsum
  refine ⟨v, Subtype.ext ?_⟩
  rw [nativeFrameChart_coe hp, nativeCenter_coe, hv, ← hpoint, nativeFrameSynthesis_centered hp]

theorem inner_traceless_traceless (x y : Glennie.Albert) :
    Glennie.inner (Glennie.traceless x) (Glennie.traceless y) =
      Glennie.inner x y - Glennie.trace x * Glennie.trace y / 3 := by
  simp only [Glennie.traceless, Glennie.inner_sub_left, Glennie.inner_sub_right,
    Glennie.inner_smul_left, Glennie.inner_smul_right, nativeInner_one_left,
    nativeInner_one_right, Glennie.trace_sub, Glennie.trace_smul, Glennie.trace_unit]
  ring

/-- Orthogonal frame planes have unbiased frames. -/
theorem unbiased_of_ortho {p q : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (hq : Glennie.Frame q) (h : (nativeFramePlane p).IsOrtho (nativeFramePlane q)) (a b : Fin 3) :
    Glennie.inner (p a) (q b) = 1 / 3 := by
  have h0 := (Submodule.isOrtho_iff_inner_eq.mp h) _ (center_mem_framePlane hp a) _
    (center_mem_framePlane hq b)
  change Glennie.inner (Glennie.traceless (p a)) (Glennie.traceless (q b)) = 0 at h0
  rw [inner_traceless_traceless, hp.trace_one, hq.trace_one] at h0
  linarith

/-- Unbiased frames have orthogonal frame planes. -/
theorem ortho_of_unbiased {p q : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p)
    (hq : Glennie.Frame q) (h : ∀ a b, Glennie.inner (p a) (q b) = 1 / 3) :
    (nativeFramePlane p).IsOrtho (nativeFramePlane q) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
  change Glennie.inner (nativeFrameChart p u) (nativeFrameChart q v) = 0
  rw [nativeFrameChart_coe hp, nativeFrameChart_coe hq, nativeFrameSynthesis_inner]
  apply Finset.sum_eq_zero
  intro a _
  rw [nativeFrame_inner_synthesis]
  simp only [h]
  rw [← Finset.sum_mul, nativeFrameEntries_sum, zero_mul, mul_zero]

end ThirteenPlanes.AlbertGrading
