module

public import ThirteenPlanes.Quartic.Square
public import ThirteenPlanes.Potential
public import ThirteenPlanes.SphereMoments.Energy

@[expose] public section

/-! The quartic toolkit for a real symmetric cubic, in an orthonormal basis.

For `h : SymmetricCubic V` with coefficient array `c = h.coefficient e`:
`⟨h,h⟩ = x`, `tr M_h² = ⟨M, M⟩`, `P(h) = tetSum`, `|S|² = 3 tr M² + 6P`, and hence
`A(h) = -x/4 + tr M²/8 + |S|²/12`. The field energy `‖Q_h(x)‖²` is one third of the quartic form of `S`.
The coordinate arrays agree with those of `ThirteenPlanes.SphereMoments.Energy`:
`h.symmetrizedArray e = sq4 c` and `pairingArray = Π`. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open Quartic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

namespace SymmetricCubic

omit [FiniteDimensional ℝ V] [DecidableEq ι] in
/-- The symmetrized array of `SphereMoments` is the toolkit's `S`. -/
theorem symmetrizedArray_eq_sq4 (h : SymmetricCubic V) :
    h.symmetrizedArray e = sq4 (h.coefficient e) := by
  funext a b c d
  rw [sq4_eq_pairT]; rfl

omit [DecidableEq ι] in
theorem tensorPairing_self_eq_strength (h : SymmetricCubic V) :
    h.tensorPairing h = strength (h.coefficient e) := by
  rw [tensorPairing_eq_sum e]; rfl

theorem doubleTraceSq_eq_minner (h : SymmetricCubic V) :
    h.doubleTraceSq = minner (mMat (h.coefficient e)) (mMat (h.coefficient e)) := by
  rw [doubleTraceSq_eq e, quadSum_eq_minner (coefficient_symm e h)]

/-- `|S|² = 3 tr M² + 6 P`. -/
theorem qinner_sq4_coefficient (h : SymmetricCubic V) :
    qinner (sq4 (h.coefficient e)) (sq4 (h.coefficient e)) =
      3 * h.doubleTraceSq + 6 * h.tetrahedron := by
  rw [qinner_sq4 (coefficient_symm e h), doubleTraceSq_eq e, tetrahedron_eq e]

/-- `|S|² = 3 tr M² + 6 P` for the symmetrized array of `SphereMoments`. -/
theorem sum_sq_symmetrizedArray' (h : SymmetricCubic V) :
    ∑ a, ∑ b, ∑ c, ∑ d, h.symmetrizedArray e a b c d ^ 2 =
      3 * h.doubleTraceSq + 6 * h.tetrahedron := by
  rw [← qinner_sq4_coefficient e, ← symmetrizedArray_eq_sq4]
  simp only [qinner, sq]

/-- `A(h) = -x/4 + tr M²/8 + |S|²/12`. -/
theorem aFunction_eq_quartic (h : SymmetricCubic V) :
    aFunction h = -(1 / 4) * h.tensorPairing h + 1 / 8 * h.doubleTraceSq +
      1 / 12 * qinner (sq4 (h.coefficient e)) (sq4 (h.coefficient e)) := by
  rw [qinner_sq4_coefficient, aFunction]
  ring

/-- The field energy is one third of the quartic form of `S`, in the coordinates `⟪e i, x⟫`. -/
theorem norm_squareMap_sq_eq_form4 (h : SymmetricCubic V) (x : V) :
    ‖h.squareMap x‖ ^ 2 = 1 / 3 * form4 (sq4 (h.coefficient e)) (fun i => ⟪e i, x⟫) := by
  have := quarticForm_symmetrizedArray e h x
  rw [symmetrizedArray_eq_sq4] at this
  change form4 _ _ = _ at this
  rw [this]; ring

end SymmetricCubic

omit [FiniteDimensional ℝ V] in
/-- The pairing array of `SphereMoments` is the toolkit's `Π`. -/
theorem pairingArray_eq_piT : (pairingArray : ι → ι → ι → ι → ℝ) = piT := rfl

omit [FiniteDimensional ℝ V] [DecidableEq ι] in
theorem qsymm_iff_isSymmetric4 (T : ι → ι → ι → ι → ℝ) : QSymm T ↔ IsSymmetric4 T :=
  ⟨fun h => ⟨h.s12, h.s23, h.s34⟩, fun h => ⟨h.swap₁₂, h.swap₂₃, h.swap₃₄⟩⟩

omit [FiniteDimensional ℝ V] in
/-- For a symmetric array, trace-freeness in the sense of `SphereMoments` is `contr T = 0`. -/
theorem isTraceFree4_iff_contr {T : ι → ι → ι → ι → ℝ} (hT : QSymm T) :
    IsTraceFree4 T ↔ contr T = 0 := by
  constructor
  · intro h; funext i j
    change ∑ k, T i j k k = 0
    rw [← h i j]
    exact Finset.sum_congr rfl fun t _ => hT.pair i j t t
  · intro h c d
    have := congrFun (congrFun h c) d
    change ∑ k, T c d k k = 0 at this
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => hT.pair t t c d

end

end ThirteenPlanes
