module

public import ThirteenPlanes.AlbertGrading.Recognition.Sparsest

@[expose] public section

/-! Native diagonal and Fourier frames in first Tits coordinates.

The diagonal frame is the eigenframe of `ι₀(Z)`. The Fourier frame over `ℂ_i` is the
eigenframe of `ι₀(X)`, as an unordered set. -/

open scoped Matrix BigOperators
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes.AlbertGrading

noncomputable section

open Tits

theorem zmod3_cases (t : ZMod 3) : t = 0 ∨ t = 1 ∨ t = 2 := by
  revert t; decide

theorem val2 : (2 : ZMod 3).val = 2 := rfl
theorem val1 : (1 : ZMod 3).val = 1 := rfl

/-- Native coordinates in the compact first Tits model. -/
def octHead' (q : Glennie.Octonion) : ℂ := ⟨q.1.re, q.1.imI⟩
def octTail' (q : Glennie.Octonion) : Fin 3 → ℂ :=
  ![⟨-q.1.imJ, q.1.imK⟩, ⟨-q.2.re, q.2.imI⟩, ⟨-q.2.imJ, -q.2.imK⟩]
def nativeA (x : Glennie.Albert) : Mat3 ℂ :=
  ![![x.d0, octHead' x.o01, octHead' x.o02],
    ![star (octHead' x.o01), x.d1, octHead' x.o12],
    ![star (octHead' x.o02), star (octHead' x.o12), x.d2]]
def nativeB (x : Glennie.Albert) : Mat3 ℂ :=
  ![octTail' x.o12, -octTail' x.o02, octTail' x.o01]

def asMat3 (M : Matrix (ZMod 3) (ZMod 3) ℂ) : Mat3 ℂ := M

theorem cpn1 : chargePhase (-1) = chargeRoot ^ 2 := rfl
theorem cpn2 : chargePhase (-2) = chargeRoot := pow_one _
theorem cp1 : chargePhase 1 = chargeRoot := pow_one _
theorem cp2 : chargePhase 2 = chargeRoot ^ 2 := rfl
theorem cmk0 : ({ re := 0, im := 0 } : ℂ) = 0 := rfl

theorem coords_native (x : Glennie.Albert) :
    CompactTits.coordinates (nativeCompactTitsEquiv x) = (nativeA x, nativeB x, (nativeB x)ᴴ) :=
  nativeToCompactTits_coordinates x

theorem standard_decomp (b : ZMod 3) : nativeA (Glennie.standardFrame b) =
    asMat3 ((1 / 3 : ℂ) • (1 : Matrix (ZMod 3) (ZMod 3) ℂ) + (chargePhase (-b) / 3) • weylD (0, 1) +
      (chargePhase b / 3) • weylD (0, -1)) := by
  have hq := chargeRoot_quadratic
  have hc := chargeRoot_cube
  simp only [weylD_eq_weylMatrix]
  suffices h : ∀ i j : ZMod 3, nativeA (Glennie.standardFrame b) i j =
      ((1 / 3 : ℂ) • (1 : Matrix (ZMod 3) (ZMod 3) ℂ) + (chargePhase (-b) / 3) • weylMatrix (0, 1) +
      (chargePhase b / 3) • weylMatrix (0, -1)) i j from funext fun i => funext fun j => h i j
  intro i j
  rcases zmod3_cases b with rfl | rfl | rfl <;> rcases zmod3_cases i with rfl | rfl | rfl <;>
    rcases zmod3_cases j with rfl | rfl | rfl <;>
    simp (config := {decide := true}) [nativeA, octHead', Glennie.standardFrame, weylMatrix,
      Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, cpn1, cpn2, cp1, cp2, cmk0] <;>
    first
    | ring1
    | linear_combination (1 / 3 : ℂ) * hq
    | linear_combination (-1 / 3 : ℂ) * hq
    | linear_combination (1 / 3 : ℂ) * hq + (1 / 3 : ℂ) * chargeRoot * hc
    | linear_combination (-1 / 3 : ℂ) * hq - (1 / 3 : ℂ) * chargeRoot * hc
    | linear_combination (2 / 3 : ℂ) * hc
    | linear_combination (-2 / 3 : ℂ) * hc


/-- The imaginary unit `i` of the first quaternion factor. -/
def octI' : Glennie.Octonion := (⟨0, 1, 0, 0⟩, 0)

theorem octHead'_fourier (m : ZMod 3) :
    octHead' ((1 / 3 : ℝ) • omegaU octI' m) = ((1 / 3 : ℝ) : ℂ) * chargePhase m := by
  apply Complex.ext <;> simp [octHead', omegaU, octI']

theorem octHead'_fourier' (m : ZMod 3) :
    octHead' ((3 : ℝ)⁻¹ • omegaU octI' m) = (3 : ℂ)⁻¹ * chargePhase m := by
  apply Complex.ext <;> simp [octHead', omegaU, octI']

theorem octTail'_fourier (r : ℝ) (m : ZMod 3) : octTail' (r • omegaU octI' m) = 0 := by
  funext i
  fin_cases i <;> simp [octTail', omegaU, octI'] <;> rfl

theorem star_root : (starRingEnd ℂ) chargeRoot = chargeRoot ^ 2 := chargeRoot_sq_eq_star.symm

theorem star_root_sq : (starRingEnd ℂ) (chargeRoot ^ 2) = chargeRoot := by
  rw [map_pow, star_root, ← pow_mul]
  have hc := chargeRoot_cube
  calc chargeRoot ^ (2 * 2) = chargeRoot ^ 3 * chargeRoot := by ring
    _ = chargeRoot := by rw [hc, one_mul]

theorem fourier_decomp (k : ZMod 3) : nativeA (fourierFrameU octI' k) =
    asMat3 ((1 / 3 : ℂ) • (1 : Matrix (ZMod 3) (ZMod 3) ℂ) + (chargePhase k / 3) • weylD (1, 0) +
      (chargePhase (-k) / 3) • weylD (-1, 0)) := by
  have hq := chargeRoot_quadratic
  have hc := chargeRoot_cube
  simp only [weylD_eq_weylMatrix]
  suffices h : ∀ i j : ZMod 3, nativeA (fourierFrameU octI' k) i j =
      ((1 / 3 : ℂ) • (1 : Matrix (ZMod 3) (ZMod 3) ℂ) + (chargePhase k / 3) • weylMatrix (1, 0) +
      (chargePhase (-k) / 3) • weylMatrix (-1, 0)) i j from funext fun i => funext fun j => h i j
  intro i j
  rcases zmod3_cases k with rfl | rfl | rfl <;> rcases zmod3_cases i with rfl | rfl | rfl <;>
    rcases zmod3_cases j with rfl | rfl | rfl <;>
    simp (config := {decide := true}) [nativeA, fourierFrameU, octHead'_fourier', weylMatrix,
      Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, cmk0] <;>
    reduce_mod_char <;>
    simp only [chargePhase_zero, cpn1, cpn2, cp1, cp2, star_root, star_root_sq, map_mul,
      map_inv₀, map_ofNat, map_one] <;>
    first
    | ring1
    | linear_combination (1 / 3 : ℂ) * hq
    | linear_combination (-1 / 3 : ℂ) * hq
    | linear_combination (1 / 3 : ℂ) * hc
    | linear_combination (-1 / 3 : ℂ) * hc

theorem nativeB_standard (b : ZMod 3) : nativeB (Glennie.standardFrame b) = 0 := by
  funext i j
  rcases zmod3_cases b with rfl | rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp [nativeB, octTail', Glennie.standardFrame] <;> rfl

theorem nativeB_fourier (k : ZMod 3) : nativeB (fourierFrameU octI' k) = 0 := by
  funext i j
  fin_cases i <;> simp [nativeB, fourierFrameU, octTail'_fourier]

theorem titsBasis_visible (v : WeylLabel) : titsBasis (chargeFrom v 0) = (weylD v, 0, 0) := by
  simp only [titsBasis, iota, chargeFrom_first, chargeFrom_second, chargeFrom_third]
  exact Prod.ext rfl (Prod.ext rfl rfl)

theorem coords_mem_of_decomp {x : Glennie.Albert} {v : WeylLabel} {c0 c1 c2 : ℂ}
    (hA : nativeA x = asMat3 (c0 • (1 : Matrix (ZMod 3) (ZMod 3) ℂ) + c1 • weylD v + c2 • weylD (-v)))
    (hB : nativeB x = 0) :
    CompactTits.coordinates (nativeCompactTitsEquiv x) ∈
      Submodule.span ℂ {firstTitsOne, titsBasis (chargeFrom v 0), titsBasis (-chargeFrom v 0)} := by
  have e : CompactTits.coordinates (nativeCompactTitsEquiv x) =
      c0 • firstTitsOne + c1 • titsBasis (chargeFrom v 0) + c2 • titsBasis (-chargeFrom v 0) := by
    rw [coords_native, hA, hB, ← chargeFrom_neg, neg_zero, titsBasis_visible, titsBasis_visible]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · show (0 : Mat3 ℂ) = c0 • (0 : Mat3 ℂ) + c1 • (0 : Mat3 ℂ) + c2 • (0 : Mat3 ℂ)
      simp
    · show (0 : Mat3 ℂ)ᴴ = c0 • (0 : Mat3 ℂ) + c1 • (0 : Mat3 ℂ) + c2 • (0 : Mat3 ℂ)
      simp
  rw [e]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem standard_mem (b : ZMod 3) :
    CompactTits.coordinates (nativeCompactTitsEquiv (Glennie.standardFrame b)) ∈
      Submodule.span ℂ {firstTitsOne, titsBasis (chargeFrom (0, 1) 0),
        titsBasis (-chargeFrom (0, 1) 0)} := by
  refine coords_mem_of_decomp (v := (0, 1)) (c0 := 1 / 3) (c1 := chargePhase (-b) / 3)
    (c2 := chargePhase b / 3) ?_ (nativeB_standard b)
  rw [standard_decomp]
  congr 3

theorem fourier_mem (k : ZMod 3) :
    CompactTits.coordinates (nativeCompactTitsEquiv (fourierFrameU octI' k)) ∈
      Submodule.span ℂ {firstTitsOne, titsBasis (chargeFrom (1, 0) 0),
        titsBasis (-chargeFrom (1, 0) 0)} := by
  refine coords_mem_of_decomp (v := (1, 0)) (c0 := 1 / 3) (c1 := chargePhase k / 3)
    (c2 := chargePhase (-k) / 3) ?_ (nativeB_fourier k)
  rw [fourier_decomp]
  congr 3

theorem range_of_span {R : ZMod 3 → CompactTits} (hR : IsTitsFrame R) {g : Charge} (hg : g ≠ 0)
    (h : ∀ a, CompactTits.coordinates (R a) ∈
      Submodule.span ℂ {firstTitsOne, titsBasis g, titsBasis (-g)}) :
    Set.range R = Set.range (gradedFrame g) := by
  obtain ⟨l, hl | hl⟩ := contrast_two hR hg (contrast_mem_of_coordinates h)
  · exact range_eq_of_line hR hl
  · rw [range_eq_of_line hR hl, range_gradedFrame_neg]

end

end ThirteenPlanes.AlbertGrading
