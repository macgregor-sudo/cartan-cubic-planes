module

public import ThirteenPlanes.AlbertGrading.Grading.Coefficients

@[expose] public section

/-! # statement and the parts proved here

The target `Targets.ThirteenPlaneCubic` is the full display `(thirteen-field polynomial)` for every ternary grading
group, every choice of representatives `g_p`, every normalized `u_{g_p}` and all coordinates. It is
NOT proved in this file. Proved here: the diagonal (one-plane) terms `W = Re ζ³`, the vanishing of
`d(u_g,u_h,u_k)` off `g+h+k=0`, and `|⟨u_g ∘ u_h, u_k⟩| = 3/2` for distinct collinear points. Open:
the phase `⟨u_g ∘ u_h, u_k⟩ ∈ -(3/2)μ₃` and the regrouping of the expansion into the 52 triples. -/

namespace ThirteenPlanes.AlbertGrading

open Grading Grading.JC

noncomputable section

namespace Grading

/-- The point of a nonzero grade (as a `NonzeroCharge`). -/
def pointOfNZ (k : NonzeroCharge) : SignedPlaneIndex := (signedPlaneGradeEquiv.symm k).1

/-- `u_g` for every nonzero grade: `u_{g_p}` itself, or `ū_{g_p}` at `-g_p`. -/
def gradeUnit (sgn : SignedPlaneIndex → Bool) (u : SignedPlaneIndex → JC) (k : NonzeroCharge) : JC :=
  if (signedPlaneGradeEquiv.symm k).2 = sgn (pointOfNZ k) then u (pointOfNZ k) else conj (u (pointOfNZ k))

/-- `ζ_g` for every nonzero grade: `ζ_p` at `g_p` and `ζ̄_p` at `-g_p`. -/
def gradeCoord (sgn : SignedPlaneIndex → Bool) (ζ : SignedPlaneIndex → ℂ) (k : NonzeroCharge) : ℂ :=
  if (signedPlaneGradeEquiv.symm k).2 = sgn (pointOfNZ k) then ζ (pointOfNZ k) else star (ζ (pointOfNZ k))

/-- Ordered zero-sum representatives of an unordered triple of points. -/
def tripleReps (t : Finset SignedPlaneIndex) : Set (NonzeroCharge × NonzeroCharge × NonzeroCharge) :=
  {x | x.1.val + x.2.1.val + x.2.2.val = 0 ∧
    ({pointOfNZ x.1, pointOfNZ x.2.1, pointOfNZ x.2.2} : Finset SignedPlaneIndex) = t}

/-- `Re(ω^φ ζ_g ζ_h ζ_k)` with `ω^φ = -(2/3)⟨u_g ∘ u_h, u_k⟩`. -/
def tripleTerm (sgn : SignedPlaneIndex → Bool) (u : SignedPlaneIndex → JC) (ζ : SignedPlaneIndex → ℂ)
    (x : NonzeroCharge × NonzeroCharge × NonzeroCharge) : ℝ :=
  ((-(2 / 3 : ℂ)) * ip (mul (gradeUnit sgn u x.1) (gradeUnit sgn u x.2.1)) (gradeUnit sgn u x.2.2) *
    gradeCoord sgn ζ x.1 * gradeCoord sgn ζ x.2.1 * gradeCoord sgn ζ x.2.2).re

open Classical in
/-- The summand of a collinear triple, at a chosen representative (any choice gives the same value
by the second clause of the target). -/
def tripleValue (sgn : SignedPlaneIndex → Bool) (u : SignedPlaneIndex → JC) (ζ : SignedPlaneIndex → ℂ)
    (t : Finset SignedPlaneIndex) : ℝ :=
  if h : (tripleReps t).Nonempty then tripleTerm sgn u ζ h.some else 0

end Grading

/-- Graded cubic expansion (display thirteen-field polynomial), for every ternary grading group: in the coordinates `ζ_p`
(with `X = (1/√6) Σ_p (ζ_p u_{g_p} + ζ̄_p u_{-g_p})`, `u_{-g_p} = ū_{g_p}`), for every collinear triple
and every zero-sum representative `(g,h,k)` one has `⟨u_g ∘ u_h, u_k⟩ = -(3/2) ω^φ` for some
`φ ∈ 𝔽₃`, the summand does not depend on the representative, and
`√6 d(X,X,X) = Σ_p Re ζ_p³ - 3 Σ_{52 collinear triples} Re(ω^φ ζ_g ζ_h ζ_k)`. -/
def Statements.ThirteenPlaneCubic : Prop :=
  ∀ ρ : TernaryAction, IsTernaryGrading ρ →
    ∀ (sgn : SignedPlaneIndex → Bool) (u : SignedPlaneIndex → JC),
      (∀ p, u p ∈ charSpace ρ (signedGrade p (sgn p)).val ∧ IsNormalized (u p)) →
      (∀ t ∈ signedCollinearTriples, ∀ x ∈ tripleReps t, ∃ φ : ZMod 3,
        ip (mul (gradeUnit sgn u x.1) (gradeUnit sgn u x.2.1)) (gradeUnit sgn u x.2.2) =
          -(3 / 2 : ℂ) * chargePhase φ) ∧
      ∀ (ζ : SignedPlaneIndex → ℂ) (X : NativeTraceless),
        of (X : Glennie.Albert) = ((Real.sqrt 6)⁻¹ : ℂ) •
          ∑ p, (ζ p • u p + star (ζ p) • conj (u p)) →
        (∀ t ∈ signedCollinearTriples, ∀ x ∈ tripleReps t,
          tripleTerm sgn u ζ x = tripleValue sgn u ζ t) ∧
        Real.sqrt 6 * nativeEqualCubic.apply X X X =
          ∑ p, (ζ p ^ 3).re - 3 * ∑ t ∈ signedCollinearTriples, tripleValue sgn u ζ t

namespace Grading

variable {ρ : TernaryAction}

theorem apply_eq_ip' (x y z : NativeTraceless) :
    nativeEqualCubic.apply x y z = (ip (mul (of x) (of y)) (of z)).re := by
  change Glennie.inner (Glennie.traceless (Glennie.jordan x y)) z = _
  rw [nativeInner_center_left, of_mul, inner_eq_ip_re]

/-- `d(u_g,u_h,u_k) = 0` unless `g + h + k = 0`. -/
theorem cubic_grade (hρ : IsTernaryGrading ρ) {g h k : Charge} {a b c : JC} (ha : a ∈ charSpace ρ g)
    (hb : b ∈ charSpace ρ h) (hc : c ∈ charSpace ρ k) (hs : g + h + k ≠ 0) : ip (mul a b) c = 0 :=
  ip_eq_zero_of_charSpace hρ (mul_mem_charSpace hρ ha hb) hc hs

/-- The one-plane terms of `(thirteen-field polynomial)`: `√6 d(X,X,X) = Re ζ³` on the plane of `u`. -/
theorem cubic_one_plane (hρ : IsTernaryGrading ρ) {g : Charge} (hg : g ≠ 0) {u : JC}
    (hu : u ∈ charSpace ρ g) (hun : IsNormalized u) (ζ : ℂ) (X : NativeTraceless)
    (hX : of (X : Glennie.Albert) = ((Real.sqrt 6)⁻¹ : ℂ) • (ζ • u + star ζ • conj u)) :
    Real.sqrt 6 * nativeEqualCubic.apply X X X = (ζ ^ 3).re := by
  have hub := conj_mem_charSpace hu
  have g2 : g + g ≠ 0 := charge_add_self_ne_zero hg
  have z1 : ip (mul u u) (conj u) = 0 := cubic_grade hρ hu hu hub (by
    rw [show g + g + -g = g by abel]; exact hg)
  have z2 : ip (mul u (conj u)) u = 0 := cubic_grade hρ hu hub hu (by
    rw [show g + -g + g = g by abel]; exact hg)
  have z3 : ip (mul u (conj u)) (conj u) = 0 := cubic_grade hρ hu hub hub (by
    rw [show g + -g + -g = -g by abel]; exact neg_ne_zero.mpr hg)
  have z4 : ip (mul (conj u) u) u = 0 := cubic_grade hρ hub hu hu (by
    rw [show -g + g + g = g by abel]; exact hg)
  have z5 : ip (mul (conj u) u) (conj u) = 0 := cubic_grade hρ hub hu hub (by
    rw [show -g + g + -g = -g by abel]; exact neg_ne_zero.mpr hg)
  have z6 : ip (mul (conj u) (conj u)) u = 0 := cubic_grade hρ hub hub hu (by
    rw [show -g + -g + g = -g by abel]; exact neg_ne_zero.mpr hg)
  have n1 : ip (mul u u) u = 3 := by rw [hun.1, ip_comm, ip_conj_normalized hun]
  have n2 : ip (mul (conj u) (conj u)) (conj u) = 3 := by
    rw [conj_mul_conj_of_normalized hun, ip_conj_normalized hun]
  rw [apply_eq_ip', hX]
  set s : ℂ := ((Real.sqrt 6)⁻¹ : ℂ)
  have key : ip (mul (s • (ζ • u + star ζ • conj u)) (s • (ζ • u + star ζ • conj u)))
      (s • (ζ • u + star ζ • conj u)) = s ^ 3 * (3 * ζ ^ 3 + 3 * star ζ ^ 3) := by
    simp only [mul_add_left, mul_add_right, mul_smul_left, mul_smul_right, ip_add_left,
      ip_add_right, ip_smul_left, ip_smul_right, z1, z2, z3, z4, z5, z6, n1, n2]
    ring
  rw [key]
  have hs : s ^ 3 = (((Real.sqrt 6)⁻¹ ^ 3 : ℝ) : ℂ) := by simp [s]
  rw [hs]
  have h6 : Real.sqrt 6 * (Real.sqrt 6)⁻¹ ^ 3 * 6 = 1 := by
    have h0 : Real.sqrt 6 ≠ 0 := by positivity
    have hsq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    field_simp
    linarith
  have hst : (star ζ ^ 3).re = (ζ ^ 3).re := by rw [← star_pow]; rfl
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re, Complex.re_ofNat, Complex.im_ofNat]
  have hst' : ((starRingEnd ℂ) ζ ^ 3).re = (ζ ^ 3).re := hst
  simp [Complex.mul_im, hst']
  have h0 : Real.sqrt 6 ≠ 0 := by positivity
  have hsq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  rw [show Real.sqrt 6 ^ 3 = Real.sqrt 6 ^ 2 * Real.sqrt 6 by ring, hsq]
  field_simp
  ring

/-- `|⟨u_g ∘ u_h, u_k⟩| = 3/2` for normalized elements of three pairwise independent grades with
zero sum. -/
theorem cubic_three_modulus (hρ : IsTernaryGrading ρ) {g h : Charge} (hg : g ≠ 0) (hh : h ≠ 0)
    (h₁ : g + h ≠ 0) (h₂ : g - h ≠ 0) {a b c : JC} (ha : a ∈ charSpace ρ g)
    (han : IsNormalized a) (hb : b ∈ charSpace ρ h) (hbn : IsNormalized b)
    (hc : c ∈ charSpace ρ (-(g + h))) (hcn : IsNormalized c) :
    ip (mul a b) c * star (ip (mul a b) c) = 9 / 4 := by
  have hcb : conj c ∈ charSpace ρ (g + h) := by
    have := conj_mem_charSpace hc; rwa [neg_neg] at this
  obtain ⟨κ, hκ, hκκ⟩ := structure_constant hρ hg hh h₁ h₂ ha han hb hbn hcb (conj_normalized hcn)
  rw [hκ, ip_smul_left, ip_comm, ip_conj_normalized hcn, star_mul', mul_comm κ 3]
  rw [show (3 : ℂ) * κ * (star κ * star 3) = 9 * (κ * star κ) by
    rw [show (star (3 : ℂ)) = 3 by simp]; ring, hκκ]
  norm_num

end Grading

end

end ThirteenPlanes.AlbertGrading
