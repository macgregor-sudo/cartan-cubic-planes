module

public import ThirteenPlanes.SignedPair
public import ThirteenPlanes.MinimumHessian.Invariance

@[expose] public section

open scoped RealInnerProductSpace

namespace ThirteenPlanes.SignedSkew

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The trace-free product with a unit of trace three adjoined. -/
def splitUnitalProduct (C : SymmetricCubic V) (x y : V × ℝ) : V × ℝ :=
  (C.L x.1 y.1 + x.2 • y.1 + y.2 • x.1, ⟪x.1,y.1⟫ / 3 + x.2 * y.2)

abbrev SignedWithUnit := SignedField × ℝ
abbrev signedSplitProduct := splitUnitalProduct signedEqualCubic

/-- The derivation identity for the metric-raised centered product. -/
def CenterDerivation (C : SymmetricCubic V) (A : V →ₗ[ℝ] V) : Prop :=
  ∀ x y, A (C.L x y) = C.L (A x) y + C.L x (A y)

theorem insert_zero_iff_centerDerivation (C : SymmetricCubic V) (A : V →ₗ[ℝ] V) (hA : IsSkew A) :
    C.insert A = 0 ↔ CenterDerivation C A := by
  constructor
  · intro hh x y
    apply ext_inner_right ℝ
    intro z
    have he : (C.insert A).apply x y z = (0 : SymmetricCubic V).apply x y z :=
      congrArg (fun T : SymmetricCubic V => T.apply x y z) hh
    rw [SymmetricCubic.apply_insert, SymmetricCubic.apply_zero] at he
    simp only [SymmetricCubic.apply] at he
    rw [inner_add_left, hA]
    linarith
  · intro hh
    apply SymmetricCubic.ext
    intro x y z
    rw [SymmetricCubic.apply_insert, SymmetricCubic.apply_zero]
    simp only [SymmetricCubic.apply]
    have he := hA (C.L x y) z
    rw [hh x y, inner_add_left] at he
    linarith

/-- Extend an endomorphism by zero on the unit direction. -/
def liftSignedEnd : (V →ₗ[ℝ] V) →ₗ[ℝ] (V × ℝ →ₗ[ℝ] V × ℝ) where
  toFun A := ((LinearMap.inl ℝ V ℝ).comp A).comp (LinearMap.fst ℝ V ℝ)
  map_add' A B := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · change (0 : ℝ) = 0 + 0
      exact (zero_add _).symm
  map_smul' r A := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · change (0 : ℝ) = r • (0 : ℝ)
      exact (smul_zero _).symm

omit [FiniteDimensional ℝ V] in
@[simp] theorem liftSignedEnd_apply (A : V →ₗ[ℝ] V) (x : V × ℝ) :
    liftSignedEnd A x = (A x.1, 0) := rfl

omit [FiniteDimensional ℝ V] in
theorem liftSignedEnd_derivation_iff (C : SymmetricCubic V) (A : V →ₗ[ℝ] V) :
    (∀ x y, liftSignedEnd A (splitUnitalProduct C x y) =
      splitUnitalProduct C (liftSignedEnd A x) y + splitUnitalProduct C x (liftSignedEnd A y)) ↔
      IsSkew A ∧ CenterDerivation C A := by
  constructor
  · intro h
    constructor
    · intro x y
      have ht := congrArg (fun z : V × ℝ => z.2) (h (x,0) (y,0))
      change (0 : ℝ) = ⟪A x,y⟫ / 3 + 0*0 + (⟪x,A y⟫ / 3 + 0*0) at ht
      linarith
    · intro x y
      have ht := congrArg (fun z : V × ℝ => z.1) (h (x,0) (y,0))
      change A (C.L x y + (0 : ℝ) • y + (0 : ℝ) • x) =
        C.L (A x) y + (0 : ℝ) • y + (0 : ℝ) • A x +
        (C.L x (A y) + (0 : ℝ) • A y + (0 : ℝ) • x) at ht
      simpa only [zero_smul, add_zero] using ht
  · rintro ⟨hsk,hc⟩ x y
    apply Prod.ext
    · simp only [splitUnitalProduct, liftSignedEnd_apply, Prod.fst_add, map_add, map_smul,
        hc x.1 y.1, zero_smul, add_zero]
      abel
    · change (0 : ℝ) = ⟪A x.1,y.1⟫ / 3 + 0*y.2 + (⟪x.1,A y.1⟫ / 3 + x.2*0)
      rw [hsk x.1 y.1]
      ring

end

end ThirteenPlanes.SignedSkew
