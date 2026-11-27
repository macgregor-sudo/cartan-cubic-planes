module

public import ThirteenPlanes.Graded.Characters
public import ThirteenPlanes.Graded.Frames

@[expose] public section

/-! The native frame planes are the compact real loci of their opposite character spaces. -/

namespace ThirteenPlanes.Graded

open scoped BigOperators

noncomputable section

/-- A native traceless field lies in the real character plane exactly when
its complex charge coordinates vanish off the two opposite grades. -/
theorem plane_iff_character_support (p : SignedPlaneIndex) (x : NativeTraceless) :
    x ∈ plane p ↔ ∀ q : Charge, q ≠ p.val.val → q ≠ -p.val.val →
      (nativeSignedCoordinates (x : Glennie.Albert)).val q = 0 := by
  obtain ⟨y, rfl⟩ := signedNativeEquiv.surjective x
  rw [nativeSignedCoordinates_signedNative]
  have hmem : signedNativeEquiv y ∈ plane p ↔ y ∈ signedPlane p := by
    constructor
    · rintro ⟨v, hv, h⟩
      exact signedNativeEquiv.injective h ▸ hv
    · intro hy
      exact ⟨y, hy, rfl⟩
  rw [hmem, mem_signedPlane_iff]
  change (∀ t ≠ p, signedPlaneCoordinates y t = 0) ↔
    ∀ q : Charge, q ≠ p.val.val → q ≠ -p.val.val → signedExtend y q = 0
  constructor
  · intro h q hpos hneg
    by_cases hq : q = 0
    · rw [hq, signedExtend_zero]
    · obtain ⟨⟨t, s⟩, ht⟩ := signedPlaneGradeEquiv.surjective ⟨q, hq⟩
      have ht' : (signedPlaneGradeEquiv (t, s)).val = q := congrArg Subtype.val ht
      rw [← ht']
      cases s
      · rw [signedPlaneGradeEquiv_false, signedExtend_nonzero, ← signedPlaneCoordinates_apply]
        apply h
        intro he
        subst t
        exact hpos ht'.symm
      · rw [signedPlaneGradeEquiv_true, signedExtend_nonzero, signedCoordinates_opposite,
          ← signedPlaneCoordinates_apply, h, star_zero]
        intro he
        subst t
        exact hneg ht'.symm
  · intro h t ht
    have hpos : t.val.val ≠ p.val.val := fun he => ht (Subtype.ext (Subtype.ext he))
    have hneg : t.val.val ≠ -p.val.val := by
      intro he
      have hp : t.val = oppositeCharge p.val := Subtype.ext he
      have ha : signedPlaneGradeEquiv (t, false) = signedPlaneGradeEquiv (p, true) := hp
      exact Bool.noConfusion (congrArg Prod.snd (signedPlaneGradeEquiv.injective ha))
    rw [signedPlaneCoordinates_apply, ← signedExtend_nonzero]
    exact h _ hpos hneg

/-- The frame plane of the explicit Fourier frame is the real opposite-character plane. -/
theorem nativeFramePlane_iff_character_support (p : SignedPlaneIndex) (x : NativeTraceless) :
    x ∈ nativeFramePlane (point p) ↔ ∀ q : Charge, q ≠ p.val.val → q ≠ -p.val.val →
      (nativeSignedCoordinates (x : Glennie.Albert)).val q = 0 := by
  rw [nativeFramePlane_point, plane_iff_character_support]

/-- In the actual signed coordinates of the full native algebra, the projectors are the
unit plus the two conjugate Fourier coefficients, all divided by three. -/
theorem nativePoint_fourier (p : SignedPlaneIndex) (a : Fin 3) :
    nativeSignedCoordinates (point p a) =
      (1 / 3 : ℝ) • (signedUnitalOne +
        signedUnitalExtend (signedPlaneInclusion p (chargePhase (-(show ZMod 3 from a))))) := by
  have h : point p a =
      (1 / 3 : ℝ) • ((1 : Glennie.Albert) +
        (signedNativeEquiv (signedPlaneInclusion p (chargePhase (-(show ZMod 3 from a)))) :
          Glennie.Albert)) := rfl
  rw [h, map_smul, map_add, nativeSignedCoordinates_one, nativeSignedCoordinates_signedNative]

end

end ThirteenPlanes.Graded
