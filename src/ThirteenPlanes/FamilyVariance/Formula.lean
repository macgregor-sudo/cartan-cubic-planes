module

public import ThirteenPlanes.FamilyVariance.Rational
public import ThirteenPlanes.SphereFloor
public import ThirteenPlanes.Contracts

@[expose] public section

set_option backward.privateInPublic true

/-! The relative variance of the field energy on the coupling plane.

For a cubic `h` let `U_h(x) = ‖Q_h(x)‖²/8` and `D(h) = Var(U_h)/(E U_h)²`, with mean and variance
over the unit sphere for the normalized surface measure. On the pencil `h = a D + b C` of a
`CubicPair` obeying the contraction laws with parameter `lam`, with both cubics trace-free,
`D(a D + b C)` is the rational function `anisotropyRational n lam (a, b)`, `n = dim V`.

The Gram data `⟨D,D⟩ = n/3`, `⟨C,C⟩ = n lam`, `⟨D,C⟩ = 0` follow from the double-contraction law by
taking traces. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The scalar energy `U_h(x) = ‖Q_h(x)‖²/8` of a uniform field `x`. -/
def fieldEnergy (h : SymmetricCubic V) (x : V) : ℝ := ‖h.squareMap x‖ ^ 2 / 8

/-- The relative variance `Var(U_h)/(E U_h)²` of the field energy over the unit sphere. -/
def relativeVariance (h : SymmetricCubic V) : ℝ :=
  sphereVariance (fieldEnergy h) / sphereAverage (fieldEnergy h) ^ 2

/-- The relative variance of the field energy of the coupling `a D + b C`. -/
def familyAnisotropy (P : CubicPair V) (u : ℝ × ℝ) : ℝ := relativeVariance (coupling P u)

namespace SymmetricCubic

private theorem tp_add_left (k g h : SymmetricCubic V) :
    (g + h).tensorPairing k = g.tensorPairing k + h.tensorPairing k := by
  rw [tensorPairing_comm, tensorPairing_add_right, tensorPairing_comm k, tensorPairing_comm k]

private theorem tp_smul_left (k g : SymmetricCubic V) (a : ℝ) :
    (a • g).tensorPairing k = a * g.tensorPairing k := by
  rw [tensorPairing_comm, tensorPairing_smul_right, tensorPairing_comm k]

theorem tensorPairing_zero_self : (0 : SymmetricCubic V).tensorPairing 0 = 0 := by
  simpa using tensorPairing_smul_right (0 : SymmetricCubic V) 0 0

end SymmetricCubic

open SymmetricCubic

/-- Bilinear expansion of the coefficient pairing on the pencil. -/
theorem tensorPairing_coupling (P : CubicPair V) (u v : ℝ × ℝ) :
    (coupling P u).tensorPairing (coupling P v) =
      u.1 * v.1 * P.diagonalCubic.tensorPairing P.diagonalCubic +
        (u.1 * v.2 + u.2 * v.1) * P.diagonalCubic.tensorPairing P.mixingCubic +
        u.2 * v.2 * P.mixingCubic.tensorPairing P.mixingCubic := by
  simp only [coupling_apply, tensorPairing_add_right, tensorPairing_smul_right, tp_add_left,
    tp_smul_left, tensorPairing_comm P.mixingCubic P.diagonalCubic]
  ring

variable {P : CubicPair V} {lam : ℝ}

/-- Under the double-contraction law, `⟨h, h⟩ = n · m(u)` on the pencil. -/
theorem tensorPairing_coupling_self (hlaws : HasContractionLaws P lam) (u : ℝ × ℝ) :
    (coupling P u).tensorPairing (coupling P u) = familyM lam u * Module.finrank ℝ V := by
  rw [tensorPairing_self, hlaws.double, map_smul, LinearMap.trace_id, smul_eq_mul]

/-- **Gram data.** The contraction laws force `⟨D,D⟩ = n/3`, `⟨C,C⟩ = n lam`, `⟨D,C⟩ = 0`. -/
theorem gram_of_contractionLaws (hlaws : HasContractionLaws P lam) :
    P.diagonalCubic.tensorPairing P.diagonalCubic = Module.finrank ℝ V / 3 ∧
      P.mixingCubic.tensorPairing P.mixingCubic = Module.finrank ℝ V * lam ∧
      P.diagonalCubic.tensorPairing P.mixingCubic = 0 := by
  have h1 := tensorPairing_coupling_self hlaws (1, 0)
  have h2 := tensorPairing_coupling_self hlaws (0, 1)
  have h3 := tensorPairing_coupling_self hlaws (1, 1)
  rw [tensorPairing_coupling] at h1 h2 h3
  simp only [familyM] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩ <;> linarith

omit [FiniteDimensional ℝ V] in
/-- The pencil of two trace-free cubics consists of trace-free cubics. -/
theorem traceFree_coupling (hD : P.diagonalCubic.TraceFree) (hC : P.mixingCubic.TraceFree)
    (u : ℝ × ℝ) : (coupling P u).TraceFree := by
  intro x
  simp only [coupling_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hD x, hC x, smul_zero, add_zero]

/-- The tetrahedron contraction on the pencil. -/
theorem tetrahedron_coupling (hlaws : HasContractionLaws P lam) (u : ℝ × ℝ) :
    (coupling P u).tetrahedron =
      Module.finrank ℝ V * lam * ((1 - lam) * u.2 ^ 4 / 2 - 2 * u.1 * u.2 ^ 3 / 3) := by
  obtain ⟨gD, gC, gDC⟩ := gram_of_contractionLaws hlaws
  rw [tetrahedron, hlaws.triangle, tensorPairing_coupling, gD, gC, gDC]
  simp only [familyP, familyQ]
  ring

/-- `tr M² = n m²` when `M = m · 1`. -/
theorem doubleTraceSq_of_scalar (h : SymmetricCubic V) {m : ℝ}
    (hM : h.doubleContraction = m • (LinearMap.id : V →ₗ[ℝ] V)) :
    h.doubleTraceSq = m ^ 2 * Module.finrank ℝ V := by
  simp only [doubleTraceSq, hM, smul_mul_smul_comm, map_smul, smul_eq_mul]
  rw [show (LinearMap.id : V →ₗ[ℝ] V) * LinearMap.id = LinearMap.id from rfl, LinearMap.trace_id]
  ring

variable [Nontrivial V]

/-- The sphere mean of the field energy of a trace-free cubic is `⟨h,h⟩/(4n(n+2))`. -/
theorem sphereAverage_fieldEnergy (h : SymmetricCubic V) (hv : h.TraceFree) :
    sphereAverage (fieldEnergy h) =
      h.tensorPairing h / (4 * Module.finrank ℝ V * (Module.finrank ℝ V + 2)) := by
  have hf : fieldEnergy h = fun x => (1 / 8 : ℝ) * ‖h.squareMap x‖ ^ 2 := by
    funext x; simp only [fieldEnergy]; ring
  have h0 : h.traceNormSq (stdOrthonormalBasis ℝ V) = 0 := by
    simp [traceNormSq, hv _]
  rw [hf, sphereAverage_const_mul, sphereAverage_norm_squareMap_sq (stdOrthonormalBasis ℝ V), h0]
  have hn : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos
  field_simp
  ring

private theorem variance_algebra (n m t Vr : ℝ) (hn : 0 < n)
    (h : -(1 / 4) * (m * n) + 3 / 8 * (m ^ 2 * n) + 1 / 2 * t - -(n * (n + 2) / (n + 10)) / 8 =
      (n + 10) / (8 * n * (n + 2)) * (m * n - n * (n + 2) / (n + 10)) ^ 2 +
        2 * n * (n + 2) * (n + 4) * (n + 6) * Vr) :
    Vr = (t / 2 + (n - 2) * n * m ^ 2 / (4 * (n + 2))) /
      (2 * n * (n + 2) * (n + 4) * (n + 6)) := by
  have hK : 2 * n * (n + 2) * (n + 4) * (n + 6) * Vr =
      -(1 / 4) * (m * n) + 3 / 8 * (m ^ 2 * n) + 1 / 2 * t - -(n * (n + 2) / (n + 10)) / 8 -
        (n + 10) / (8 * n * (n + 2)) * (m * n - n * (n + 2) / (n + 10)) ^ 2 := by linarith
  have hK0 : 2 * n * (n + 2) * (n + 4) * (n + 6) ≠ 0 := by positivity
  rw [eq_div_iff hK0, mul_comm, hK]
  field_simp
  ring

/-- The sphere variance of the field energy of a trace-free cubic with `M = m · 1`:
`2n(n+2)(n+4)(n+6) Var(U_h) = P(h)/2 + (n-2) n m² / (4(n+2))`. -/
theorem sphereVariance_fieldEnergy (h : SymmetricCubic V) (hv : h.TraceFree) {m : ℝ}
    (hM : h.doubleContraction = m • (LinearMap.id : V →ₗ[ℝ] V)) :
    sphereVariance (fieldEnergy h) =
      (h.tetrahedron / 2 + (Module.finrank ℝ V - 2) * Module.finrank ℝ V * m ^ 2 /
          (4 * (Module.finrank ℝ V + 2))) /
        (2 * Module.finrank ℝ V * (Module.finrank ℝ V + 2) * (Module.finrank ℝ V + 4) *
          (Module.finrank ℝ V + 6)) := by
  have key := aFunction_floor_identity h hv ⟨m, hM⟩
  simp only at key
  have hx : h.tensorPairing h = m * Module.finrank ℝ V := by
    rw [tensorPairing_self, hM, map_smul, LinearMap.trace_id, smul_eq_mul]
  unfold aFunction at key
  rw [doubleTraceSq_of_scalar h hM, hx] at key
  have hn : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos
  exact variance_algebra _ m _ _ hn key

/-- The sphere mean of the field energy on the pencil: `E U = m(u)/(4(n+2)) = W(u)/(12(n+2))`. -/
theorem sphereAverage_fieldEnergy_coupling (hlaws : HasContractionLaws P lam)
    (hD : P.diagonalCubic.TraceFree) (hC : P.mixingCubic.TraceFree) (u : ℝ × ℝ) :
    sphereAverage (fieldEnergy (coupling P u)) =
      weightedStrength lam u.1 u.2 / (12 * (Module.finrank ℝ V + 2)) := by
  rw [sphereAverage_fieldEnergy _ (traceFree_coupling hD hC u), tensorPairing_coupling_self hlaws]
  have hn : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos
  simp only [familyM, weightedStrength]
  field_simp
  ring

/-- The mean field energy is positive exactly when the coupling is nonzero. -/
theorem sphereAverage_fieldEnergy_pos_iff (hlaws : HasContractionLaws P lam) (hlam : 0 < lam)
    (hD : P.diagonalCubic.TraceFree) (hC : P.mixingCubic.TraceFree) (u : ℝ × ℝ) :
    (0 < sphereAverage (fieldEnergy (coupling P u)) ↔ coupling P u ≠ 0) ∧
      (coupling P u ≠ 0 ↔ u ≠ 0) := by
  have hn : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos
  have hE := sphereAverage_fieldEnergy_coupling hlaws hD hC u
  have hpos : u ≠ 0 → 0 < sphereAverage (fieldEnergy (coupling P u)) := fun hu => by
    rw [hE]
    have := weightedStrength_pos hlam (a := u.1) (b := u.2) (by simpa using hu)
    positivity
  have hcu : coupling P u ≠ 0 → u ≠ 0 := fun h hu => h (by rw [hu, map_zero])
  have huc : u ≠ 0 → coupling P u ≠ 0 := fun hu h => by
    have hx := tensorPairing_coupling_self hlaws u
    rw [h, tensorPairing_zero_self] at hx
    have hW := weightedStrength_pos hlam (a := u.1) (b := u.2) (by simpa using hu)
    simp only [weightedStrength] at hW
    simp only [familyM] at hx
    nlinarith
  refine ⟨⟨fun h hc => ?_, fun h => hpos (hcu h)⟩, ⟨hcu, huc⟩⟩
  have hx := tensorPairing_coupling_self hlaws u
  rw [hc, tensorPairing_zero_self] at hx
  rw [hE] at h
  have hm : familyM lam u = 0 := by
    rcases mul_eq_zero.mp hx.symm with h' | h'
    · exact h'
    · exact absurd h' hn.ne'
  simp only [familyM] at hm
  simp only [weightedStrength] at h
  have h0 : u.1 ^ 2 + 3 * lam * u.2 ^ 2 = 0 := by linarith
  rw [h0, zero_div] at h
  exact lt_irrefl _ h

/-- **Closed formula.** On the pencil of two trace-free cubics obeying the contraction laws, the
relative variance of the field energy over the unit sphere is the rational function
`(2(n-2) W² + 6(n+2) lam b³ (3(1-lam) b - 4a)) / ((n+4)(n+6) W²)`, `W = a² + 3 lam b²`
(both sides are `0` at `u = 0`). -/
theorem familyAnisotropy_eq (hlaws : HasContractionLaws P lam)
    (hD : P.diagonalCubic.TraceFree) (hC : P.mixingCubic.TraceFree) (u : ℝ × ℝ) :
    familyAnisotropy P u = anisotropyRational (Module.finrank ℝ V) lam u := by
  have hn : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos
  unfold familyAnisotropy relativeVariance
  rw [sphereAverage_fieldEnergy_coupling hlaws hD hC u,
    sphereVariance_fieldEnergy _ (traceFree_coupling hD hC u) (hlaws.double u),
    tetrahedron_coupling hlaws u]
  unfold anisotropyRational anisotropyNum anisotropyDen
  set n : ℝ := (Module.finrank ℝ V : ℝ)
  obtain ⟨a, b⟩ := u
  simp only [familyM, weightedStrength] at *
  by_cases hW : a ^ 2 + 3 * lam * b ^ 2 = 0
  · rw [hW]; simp
  · field_simp
    ring

end

end ThirteenPlanes
