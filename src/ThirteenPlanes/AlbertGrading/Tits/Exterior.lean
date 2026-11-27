module

public import ThirteenPlanes.AlbertGrading.Tits.Automorphisms
public import ThirteenPlanes.AlbertGrading.Tits.CentralTriples

@[expose] public section

set_option backward.privateInPublic true

/-!
# a frame orthogonal to `Q₀⁰`

The determinant and adjugate argument in `specialUnitary_triple_sum_zero` identifies an
ordered special-unitary triple with zero sum as the three central multiples of its first member.


-/

open scoped Matrix RealInnerProductSpace BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

theorem sum_zmod3 {M : Type*} [AddCommMonoid M] (f : ZMod 3 → M) :
    ∑ a, f a = f 0 + f 1 + f 2 := Fin.sum_univ_three f

theorem exteriorPoint_coordinates (a : ZMod 3) :
    CompactTits.coordinates (exteriorPoint a) =
      ((1 / 3 : ℂ) • (1 : Mat3 ℂ), ((1 / 3 : ℂ) * chargePhase a) • (1 : Mat3 ℂ),
        ((1 / 3 : ℂ) * chargePhase (-a)) • (1 : Mat3 ℂ)) := by
  rw [exteriorPoint, CompactTits.coordinates_ofMatrices, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, chargePhase_neg, star_mul']
  congr 3
  simp

/-- The visible part of an atom of a frame orthogonal to `Q₀⁰` is `1/3`. -/
theorem visible_third (p : ZMod 3 → CompactTits) (hp : IsTitsFrame p)
    (horth : (titsFramePlane p).IsOrtho visibleTraceless) (a : ZMod 3) :
    (CompactTits.coordinates (p a)).1 = (1 / 3 : ℂ) • (1 : Mat3 ℂ) := by
  set x := p a - (1 / 3 : ℝ) • CompactTits.one with hx
  have hxmem : x ∈ titsFramePlane p := Submodule.subset_span ⟨a, rfl⟩
  have htr : CompactTits.trace x = 0 := by
    rw [hx, map_sub, map_smul, hp.2.1 a, CompactTits.trace_one]; norm_num
  have htr3 : trace3 (CompactTits.coordinates x).1 = 0 := by
    rw [← CompactTits.complex_trace_eq, htr, Complex.ofReal_zero]
  set A := (CompactTits.coordinates x).1 with hA
  let y := CompactTits.ofMatrices A 0 (CompactTits.hermitian x)
  have hymem : y ∈ visibleTraceless := by
    refine ⟨rfl, ?_⟩
    rw [CompactTits.trace_apply]
    change (trace3 A).re = 0
    rw [htr3, Complex.zero_re]
  have h0 : ⟪x, y⟫ = 0 := horth.inner_eq hxmem hymem
  have hyy : ⟪y, y⟫ = ⟪x, y⟫ := by
    simp only [CompactTits.inner_eq_tracePairing, CompactTits.tracePairing, y,
      CompactTits.coordinates_ofMatrices, Matrix.conjTranspose_zero, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, mul_zero, add_zero, A]
  have hy0 : y = 0 := inner_self_eq_zero (𝕜 := ℝ) |>.mp (hyy.trans h0)
  have hA0 : A = 0 := by
    have := congrArg (fun z => (CompactTits.coordinates z).1) hy0
    simpa [y] using this
  have hcx : (CompactTits.coordinates x).1 =
      (CompactTits.coordinates (p a)).1 - (1 / 3 : ℝ) • (1 : Mat3 ℂ) := by
    rw [hx, map_sub, map_smul, CompactTits.coordinates_one]
    rfl
  rw [← hA, hA0] at hcx
  have := (sub_eq_zero.mp hcx.symm)
  rw [this]
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

/-- `Vᴴ * adj(Vᴴ) = det(Vᴴ) • 1` with `adj(Vᴴ) = V` and `V Vᴴ = 1` forces `det V = 1`. -/
private theorem det_eq_one_of_adjugate {V : Mat3 ℂ} (hV : V * Vᴴ = 1)
    (hadj : adjugate3 Vᴴ = V) : V.det = 1 := by
  have hV' : Vᴴ * V = 1 := unitary_conjTranspose_mul
    (Matrix.mem_unitaryGroup_iff.mpr (by simpa [Matrix.star_eq_conjTranspose] using hV))
  have h := Matrix.mul_adjugate Vᴴ
  rw [← AlbertLean.Generic.TitsLinear.adjugate3_eq_matrixAdjugate, hadj, hV'] at h
  have h00 := congrFun (congrFun h 0) 0
  simp only [Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_one] at h00
  rw [Matrix.det_conjTranspose] at h00
  have := congrArg star h00
  simpa using this.symm

/-- Each atom has hidden block `V/3` with `V ∈ SU(3)`. -/
theorem hidden_specialUnitary (p : ZMod 3 → CompactTits) (hp : IsTitsFrame p)
    (horth : (titsFramePlane p).IsOrtho visibleTraceless) (a : ZMod 3) :
    (3 : ℂ) • (CompactTits.coordinates (p a)).2.1 ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  set B := (CompactTits.coordinates (p a)).2.1 with hB
  have hvis := visible_third p hp horth a
  have hthird : (CompactTits.coordinates (p a)).2.2 = Bᴴ := CompactTits.third_eq_adjoint _
  have hidem : firstTitsSquare (CompactTits.coordinates (p a)) = CompactTits.coordinates (p a) := by
    have := congrArg CompactTits.coordinates (hp.1 a a)
    rw [if_pos rfl, coordinates_product, firstTitsJordanProduct_self] at this
    exact this
  have hc : CompactTits.coordinates (p a) = ((1 / 3 : ℂ) • (1 : Mat3 ℂ), B, Bᴴ) := by
    rw [← hvis, ← hthird]
  rw [hc] at hidem
  simp only [firstTitsSquare] at hidem
  have h1 := congrArg Prod.fst hidem
  have h2 := congrArg (fun z => z.2.1) hidem
  simp only at h1 h2
  -- position 0: `B Bᴴ = (1/9) 1`
  set t := trace3 (B * Bᴴ) with ht
  have hP : B * Bᴴ = (t - 2 / 9 : ℂ) • (1 : Mat3 ℂ) := by
    have : (1 / 3 : ℂ) • (1 : Mat3 ℂ) * ((1 / 3 : ℂ) • (1 : Mat3 ℂ)) = (1 / 9 : ℂ) • 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]; norm_num
    rw [this] at h1
    have h1' : B * Bᴴ = (1 / 9 : ℂ) • 1 + t • 1 - (1 / 3 : ℂ) • 1 := by
      rw [← h1]; abel
    rw [h1', ← add_smul, ← sub_smul]; congr 1; ring
  have htval : t = 1 / 3 := by
    have := congrArg trace3 hP
    rw [← ht] at this
    simp only [trace3, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    linear_combination -this / 2
  have hBB : B * Bᴴ = (1 / 9 : ℂ) • (1 : Mat3 ℂ) := by
    rw [hP, htval]; norm_num
  -- position 1: `adj(Bᴴ) = B/3`
  have hadjB : adjugate3 Bᴴ = (1 / 3 : ℂ) • B := by
    have htr : trace3 ((1 / 3 : ℂ) • (1 : Mat3 ℂ)) = 1 := by
      simp [trace3, Matrix.one_apply]; norm_num
    rw [htr, one_smul, Matrix.smul_mul, Matrix.one_mul] at h2
    calc adjugate3 Bᴴ = (adjugate3 Bᴴ - (1 / 3 : ℂ) • B + B) - B + (1 / 3 : ℂ) • B := by abel
      _ = (1 / 3 : ℂ) • B := by rw [h2]; abel
  -- `V = 3B`
  have hunit : (3 : ℂ) • B * ((3 : ℂ) • B)ᴴ = 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hBB, smul_smul, smul_smul]
    norm_num
  have hadj : adjugate3 ((3 : ℂ) • B)ᴴ = (3 : ℂ) • B := by
    rw [Matrix.conjTranspose_smul, AlbertLean.Generic.TitsLinear.adjugate3_eq_matrixAdjugate,
      Matrix.adjugate_smul, ← AlbertLean.Generic.TitsLinear.adjugate3_eq_matrixAdjugate, hadjB,
      smul_smul, Fintype.card_fin]
    norm_num
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, det_eq_one_of_adjugate hunit hadj⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact hunit

end

end ThirteenPlanes.AlbertGrading
