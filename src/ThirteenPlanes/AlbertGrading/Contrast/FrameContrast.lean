module

public import ThirteenPlanes.AlbertGrading.Contrast.Statements
public import ThirteenPlanes.NativeFrames

@[expose] public section

/-!
# the complex Fourier contrast of a Jordan frame

The frame relations collapse every product of two Fourier sums
to a diagonal sum, and the order-three character sums invert the transform.
-/

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Contrast Contrast.AlbertC

namespace Contrast

/-! ## Order-three phases -/

theorem chargePhase_mul_neg (a : ZMod 3) : chargePhase a * chargePhase (-a) = 1 := by
  rw [← chargePhase_add, add_neg_cancel, chargePhase_zero]

theorem chargePhase_mul_star (a : ZMod 3) : chargePhase a * star (chargePhase a) = 1 := by
  rw [← chargePhase_neg, chargePhase_mul_neg]

theorem chargePhase_mul_self (a : ZMod 3) : chargePhase a * chargePhase a = star (chargePhase a) := by
  rw [← chargePhase_add, ← chargePhase_neg]
  congr 1
  linear_combination a * (by decide : (3 : ZMod 3) = 0)

theorem sum_chargePhase : (∑ a : Fin 3, chargePhase (outcome a)) = 0 := by
  rw [Fin.sum_univ_three]
  change chargeRoot ^ 0 + chargeRoot ^ 1 + chargeRoot ^ 2 = 0
  linear_combination chargeRoot_quadratic

theorem sum_star_chargePhase : (∑ a : Fin 3, star (chargePhase (outcome a))) = 0 := by
  rw [← star_sum, sum_chargePhase, star_zero]

/-- The character sum `1 + ω^c + ω^{-c}` is `3` at `c = 0` and `0` otherwise. -/
theorem character_sum (c : ZMod 3) :
    1 + chargePhase c + chargePhase (-c) = if c = 0 then 3 else 0 := by
  fin_cases c
  · change (1 : ℂ) + chargeRoot ^ 0 + chargeRoot ^ 0 = 3
    norm_num
  · change (1 : ℂ) + chargeRoot ^ 1 + chargeRoot ^ 2 = 0
    linear_combination chargeRoot_quadratic
  · change (1 : ℂ) + chargeRoot ^ 2 + chargeRoot ^ 1 = 0
    linear_combination chargeRoot_quadratic

theorem chargePhase_mem_mu3 (a : ZMod 3) : chargePhase a ∈ mu3 := by
  fin_cases a
  · exact Or.inl (by change chargeRoot ^ 0 = 1; simp)
  · exact Or.inr (Or.inl (by change chargeRoot ^ 1 = chargeRoot; simp))
  · exact Or.inr (Or.inr rfl)

theorem mem_mu3_iff (ζ : ℂ) : ζ ∈ mu3 ↔ ∃ a : ZMod 3, chargePhase a = ζ := by
  constructor
  · rintro (h | h | h)
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, by rw [h]; change chargeRoot ^ 1 = chargeRoot; simp⟩
    · exact ⟨2, by rw [h]; rfl⟩
  · rintro ⟨a, rfl⟩
    exact chargePhase_mem_mu3 a

/-! ## Products of Fourier sums over one frame -/

theorem jordan_frame_sums {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (α β : Fin 3 → ℂ) :
    jordan (∑ a, α a • ofReal (p a)) (∑ b, β b • ofReal (p b)) =
      ∑ a, (α a * β a) • ofReal (p a) := by
  simp only [jordan_sum_left, jordan_sum_right, jordan_smul_left, jordan_smul_right,
    jordan_ofReal, nativeFrame_jordan hp, smul_smul]
  simp only [Fin.sum_univ_three]
  simp
  module

theorem conj_contrast (p : Fin 3 → Glennie.Albert) :
    conj (contrast p) = ∑ a : Fin 3, star (chargePhase (outcome a)) • ofReal (p a) := by
  simp [contrast, conj_sum]

theorem conj_contrast' (p : Fin 3 → Glennie.Albert) :
    conj (contrast p) = ∑ a : Fin 3, chargePhase (-outcome a) • ofReal (p a) := by
  rw [conj_contrast]
  simp only [chargePhase_neg]

theorem trace_frame_sum {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (α : Fin 3 → ℂ) :
    trace (∑ a, α a • ofReal (p a)) = ∑ a, α a := by
  simp [trace_sum, trace_smul, hp.trace_one]

theorem sum_frame_ofReal {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    (∑ a : Fin 3, ofReal (p a)) = ofReal 1 := by
  rw [← ofReal_sum, Fin.sum_univ_three, hp.sum_unit]

theorem contrast_sq {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    jordan (contrast p) (contrast p) = conj (contrast p) := by
  rw [conj_contrast, contrast, jordan_frame_sums hp]
  simp only [chargePhase_mul_self]

theorem contrast_mul_conj {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    jordan (contrast p) (conj (contrast p)) = ofReal 1 := by
  rw [conj_contrast, contrast, jordan_frame_sums hp]
  simp only [chargePhase_mul_star, one_smul]
  exact sum_frame_ofReal hp

theorem trace_contrast {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    trace (contrast p) = 0 := by
  rw [contrast, trace_frame_sum hp, sum_chargePhase]

theorem trace_conj_contrast {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    trace (conj (contrast p)) = 0 := by
  rw [trace_conj, trace_contrast hp, star_zero]

theorem pair_contrast_self {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    pair (contrast p) (contrast p) = 0 := by
  rw [pair, contrast_sq hp, trace_conj_contrast hp]

theorem pair_contrast_conj {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) :
    pair (contrast p) (conj (contrast p)) = 3 := by
  rw [pair, contrast_mul_conj hp, trace_ofReal, Glennie.trace_unit]
  norm_num

/-- Fourier inversion: `p_a = (e + ω^{-a} u + ω^a ū)/3`. -/
theorem fourier_inversion {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (a : Fin 3) :
    ofReal (p a) = (1 / 3 : ℂ) • (ofReal 1 + chargePhase (-outcome a) • contrast p +
      chargePhase (outcome a) • conj (contrast p)) := by
  have hcoef : ∀ b : Fin 3, (1 / 3 : ℂ) * (1 + chargePhase (-outcome a) * chargePhase (outcome b)
      + chargePhase (outcome a) * chargePhase (-outcome b)) = if a = b then 1 else 0 := by
    intro b
    rw [← chargePhase_add, ← chargePhase_add, show -(outcome a) + outcome b = outcome b - outcome a by ring,
      show outcome a + -outcome b = -(outcome b - outcome a) by ring, character_sum]
    by_cases h : a = b
    · subst h; simp
    · have h' : outcome b - outcome a ≠ 0 := sub_ne_zero.mpr (fun e => h e.symm)
      simp [h, h']
  have hexp : (1 / 3 : ℂ) • (ofReal 1 + chargePhase (-outcome a) • contrast p +
      chargePhase (outcome a) • conj (contrast p)) =
      ∑ b : Fin 3, ((1 / 3 : ℂ) * (1 + chargePhase (-outcome a) * chargePhase (outcome b)
        + chargePhase (outcome a) * chargePhase (-outcome b))) • ofReal (p b) := by
    rw [← sum_frame_ofReal hp, conj_contrast', contrast]
    simp only [Fin.sum_univ_three]
    module
  rw [hexp]
  simp only [hcoef, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-! ## The complexified plane -/

theorem sum_mem_framePlane (p : Fin 3 → Glennie.Albert) (c : Fin 3 → ℝ) (hc : ∑ a, c a = 0) :
    (∑ a, c a • p a) ∈ framePlane p := by
  have h : (∑ a, c a • p a) = ∑ a, c a • (p a - (1 / 3 : ℝ) • (1 : Glennie.Albert)) := by
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
    rw [← Finset.sum_smul, ← Finset.sum_mul, hc, zero_mul, zero_smul, sub_zero]
  rw [h]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem frame_sum_re (p : Fin 3 → Glennie.Albert) (α : Fin 3 → ℂ) :
    (∑ a, α a • ofReal (p a)).re = ∑ a, (α a).re • p a := by
  simp [sum_re]

theorem frame_sum_im (p : Fin 3 → Glennie.Albert) (α : Fin 3 → ℂ) :
    (∑ a, α a • ofReal (p a)).im = ∑ a, (α a).im • p a := by
  simp [sum_im]

theorem contrast_re_mem (p : Fin 3 → Glennie.Albert) : (contrast p).re ∈ framePlane p := by
  rw [contrast, frame_sum_re]
  apply sum_mem_framePlane
  rw [← Complex.re_sum, sum_chargePhase, Complex.zero_re]

theorem contrast_im_mem (p : Fin 3 → Glennie.Albert) : (contrast p).im ∈ framePlane p := by
  rw [contrast, frame_sum_im]
  apply sum_mem_framePlane
  rw [← Complex.im_sum, sum_chargePhase, Complex.zero_im]

theorem complexPlane_iff {p : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (z : AlbertC) :
    (z.re ∈ framePlane p ∧ z.im ∈ framePlane p) ↔
      z ∈ Submodule.span ℂ {contrast p, conj (contrast p)} := by
  set S := Submodule.span ℂ {contrast p, conj (contrast p)}
  have hu : contrast p ∈ S := Submodule.subset_span (by simp)
  have hv : conj (contrast p) ∈ S := Submodule.subset_span (by simp)
  constructor
  · rintro ⟨hre, him⟩
    have hreal : ∀ y ∈ framePlane p, ofReal y ∈ S := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        have h := fourier_inversion hp a
        have : ofReal (p a - (1 / 3 : ℝ) • (1 : Glennie.Albert)) =
            (1 / 3 : ℂ) • (chargePhase (-outcome a) • contrast p +
              chargePhase (outcome a) • conj (contrast p)) := by
          rw [ofReal_sub, ofReal_smul, h]
          push_cast
          module
        rw [this]
        exact S.smul_mem _ (S.add_mem (S.smul_mem _ hu) (S.smul_mem _ hv))
      | zero => simpa using S.zero_mem
      | add x y _ _ hx hy => simpa using S.add_mem hx hy
      | smul r x _ hx => simpa using S.smul_mem (r : ℂ) hx
    rw [eq_ofReal_add_I_smul z]
    exact S.add_mem (hreal _ hre) (S.smul_mem _ (hreal _ him))
  · intro hz
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
    have h1 := contrast_re_mem p
    have h2 := contrast_im_mem p
    refine ⟨?_, ?_⟩
    · simp only [add_re, smul_re, conj_re, conj_im, smul_neg]
      exact (framePlane p).add_mem ((framePlane p).sub_mem ((framePlane p).smul_mem _ h1)
        ((framePlane p).smul_mem _ h2)) ((framePlane p).sub_mem ((framePlane p).smul_mem _ h1)
        ((framePlane p).neg_mem ((framePlane p).smul_mem _ h2)))
    · simp only [add_im, smul_im, conj_re, conj_im, smul_neg]
      exact (framePlane p).add_mem ((framePlane p).add_mem ((framePlane p).smul_mem _ h2)
        ((framePlane p).smul_mem _ h1)) ((framePlane p).add_mem
        ((framePlane p).neg_mem ((framePlane p).smul_mem _ h2)) ((framePlane p).smul_mem _ h1))

/-! ## Relabelling the outcomes -/

/-- Every permutation of `𝔽₃` is `c ↦ s c + b` with `s = ±1`. -/
theorem perm_affine : ∀ τ : Equiv.Perm (Fin 3), ∃ s b : ZMod 3, (s = 1 ∨ s = -1) ∧
    ∀ c : Fin 3, outcome (τ c) = s * (outcome c) + b := by
  decide

/-- Relabelling the outcomes of a Fourier sum multiplies it by a phase, after possibly
conjugating the characters. -/
theorem fourier_perm {M : Type*} [AddCommGroup M] [Module ℂ M] (w : Fin 3 → M)
    (σ : Equiv.Perm (Fin 3)) : ∃ b s : ZMod 3, (s = 1 ∨ s = -1) ∧
      ∑ a : Fin 3, chargePhase (outcome a) • w (σ a) =
        chargePhase b • ∑ c : Fin 3, chargePhase (s * (outcome c)) • w c := by
  obtain ⟨s, b, hs, hτ⟩ := perm_affine σ.symm
  refine ⟨b, s, hs, ?_⟩
  rw [← Equiv.sum_comp σ.symm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Equiv.apply_symm_apply, hτ c, smul_smul, add_comm, chargePhase_add]

theorem contrast_perm (p : Fin 3 → Glennie.Albert) (σ : Equiv.Perm (Fin 3)) :
    ∃ ζ ∈ mu3, contrast (p ∘ σ) = ζ • contrast p ∨ contrast (p ∘ σ) = ζ • conj (contrast p) := by
  obtain ⟨b, s, hs, h⟩ := fourier_perm (fun a => ofReal (p a)) σ
  refine ⟨chargePhase b, chargePhase_mem_mu3 b, ?_⟩
  have hc : contrast (p ∘ σ) = ∑ a : Fin 3, chargePhase (outcome a) • ofReal (p (σ a)) := rfl
  rcases hs with rfl | rfl
  · left
    rw [hc, h]
    simp [contrast]
  · right
    rw [hc, h, conj_contrast']
    simp

/-! ## Unbiasedness -/

theorem pair_frame_sums (p q : Fin 3 → Glennie.Albert) (α β : Fin 3 → ℂ) :
    pair (∑ a, α a • ofReal (p a)) (∑ b, β b • ofReal (q b)) =
      ∑ a, ∑ b, α a * β b * (Glennie.inner (p a) (q b) : ℂ) := by
  rw [← pairL_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp only [pairL_apply, pair_ofReal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem unbiased_iff {p q : Fin 3 → Glennie.Albert} (hp : Glennie.Frame p) (hq : Glennie.Frame q) :
    Unbiased p q ↔ pair (contrast p) (contrast q) = 0 ∧ pair (contrast p) (conj (contrast q)) = 0 := by
  constructor
  · intro h
    have hin : ∀ a b, (Glennie.inner (p a) (q b) : ℂ) = 1 / 3 := by
      intro a b
      rw [Glennie.inner, h a b]
      push_cast; ring
    constructor
    · simp only [contrast]
      rw [pair_frame_sums]
      simp only [hin]
      rw [show (∑ a : Fin 3, ∑ b : Fin 3, chargePhase (outcome a) * chargePhase (outcome b) *
          (1 / 3 : ℂ)) = (∑ a : Fin 3, chargePhase (outcome a)) *
            (∑ b : Fin 3, chargePhase (outcome b)) * (1 / 3) by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        simp only [Finset.sum_mul]]
      rw [sum_chargePhase]; ring
    · rw [conj_contrast]
      simp only [contrast]
      rw [pair_frame_sums]
      simp only [hin]
      rw [show (∑ a : Fin 3, ∑ b : Fin 3, chargePhase (outcome a) * star (chargePhase (outcome b)) *
          (1 / 3 : ℂ)) = (∑ a : Fin 3, chargePhase (outcome a)) *
            (∑ b : Fin 3, star (chargePhase (outcome b))) * (1 / 3) by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        simp only [Finset.sum_mul]]
      rw [sum_chargePhase]; ring
  · rintro ⟨h1, h2⟩ a b
    have h3 : pair (conj (contrast p)) (contrast q) = 0 := by
      rw [← conj_conj (contrast q), pair_conj, h2, star_zero]
    have h4 : pair (conj (contrast p)) (conj (contrast q)) = 0 := by
      rw [pair_conj, h1, star_zero]
    have he : ∀ x, pair (ofReal 1) x = trace x := fun x => by rw [pair, jordan_one_left]
    have he' : ∀ x, pair x (ofReal 1) = trace x := fun x => by rw [pair, jordan_one_right]
    have key : (Glennie.trace (Glennie.jordan (p a) (q b)) : ℂ) = 1 / 3 := by
      rw [← trace_ofReal, ← jordan_ofReal, ← pair, fourier_inversion hp a, fourier_inversion hq b]
      rw [← pairL_apply]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      simp only [pairL_apply]
      rw [he, he, he, he', he', h1, h2, h3, h4, trace_contrast hp, trace_contrast hq,
        trace_conj_contrast hp, trace_conj_contrast hq, trace_ofReal, Glennie.trace_unit]
      push_cast; ring
    have := congrArg Complex.re key
    simpa using this

end Contrast

/-- Fourier contrast identities. -/
theorem frameContrast : Statements.FrameContrast :=
  ⟨fun _ hp => ⟨contrast_sq hp, contrast_mul_conj hp, pair_contrast_self hp, pair_contrast_conj hp,
      fourier_inversion hp, complexPlane_iff hp, contrast_perm _⟩,
    fun _ _ hp hq => unbiased_iff hp hq⟩

end

end ThirteenPlanes.AlbertGrading
