module

public import ThirteenPlanes.Cartan.SecondRowLieRealization
public import ThirteenPlanes.Cartan.CartanOfInvariantPositive
public import ThirteenPlanes.Cartan.SecondRow.Involution

@[expose] public section

set_option backward.privateInPublic true

/-! The fixed real Lie algebra and the actual Lie subalgebras of the second row. -/

namespace ThirteenPlanes.Cartan.SecondRowCompactRealization

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  {M : TraceJordanData J} {K : Submodule ℝ (SkewOperator J)} (H : SecondRowCompactRealization M K)

/-- The fixed points of the actual conjugation, with their inherited operator bracket. -/
def realLie : LieSubalgebra ℝ H.operators where
  carrier := {X | H.theta X = X}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    change H.theta X = X at hX
    change H.theta Y = Y at hY
    change H.theta (X + Y) = X + Y
    rw [map_add, hX, hY]
  smul_mem' := by
    intro r X hX
    change H.theta X = X at hX
    change H.theta (r • X) = r • X
    rw [map_smul, hX]
  lie_mem' := by
    intro X Y hX hY
    change H.theta X = X at hX
    change H.theta Y = Y at hY
    have hb : (H.theta ⁅X,Y⁆).val = operatorBracket (H.theta X).val (H.theta Y).val :=
      secondRowTheta_preserves_operatorBracket M K
        (H.coordinates.symm X) (H.coordinates.symm Y) (H.coordinates.symm ⁅X,Y⁆) rfl
    rw [hX,hY] at hb
    exact Subtype.ext hb

private def realInclusion : K →ₗ[ℝ] H.realLie where
  toFun D := ⟨H.coordinates (secondRowRealInclusion M K D), by
    change H.theta (H.coordinates (secondRowCoordinates M K (D, 0))) = _
    rw [H.theta_coordinates, secondRowTheta_coordinates, neg_zero]
    rfl⟩
  map_add' D E := Subtype.ext (map_add (H.coordinates.toLinearMap.comp (secondRowRealInclusion M K)) D E)
  map_smul' r D := Subtype.ext (map_smul (H.coordinates.toLinearMap.comp (secondRowRealInclusion M K)) r D)

/-- The fixed Lie algebra is exactly the original real derivations under scalar extension. -/
def realCoordinates : K ≃ₗ[ℝ] H.realLie := LinearEquiv.ofBijective H.realInclusion (by
  constructor
  · intro D E h
    have he := H.coordinates.injective (congrArg Subtype.val h)
    exact congrArg Prod.fst ((secondRowCoordinates M K).injective he)
  · intro X
    have hX : H.theta X.val = X.val := X.property
    rw [← H.coordinates.apply_symm_apply X.val, H.theta_coordinates] at hX
    obtain ⟨D, hD⟩ := (secondRowTheta_fixed_iff_real M K _).mp (H.coordinates.injective hX)
    refine ⟨D, Subtype.ext ?_⟩
    change H.coordinates (secondRowCoordinates M K (D, 0)) = X.val
    rw [← hD, H.coordinates.apply_symm_apply])

@[simp] theorem realCoordinates_val (D : K) :
    (H.realCoordinates D).val = H.coordinates (secondRowRealInclusion M K D) := rfl

@[simp] theorem realCoordinates_operator (D : K) :
    (H.realCoordinates D).val.val = D.val.val.baseChange ℂ :=
  secondRowRealInclusion_operator M K D

/-- The fixed Lie bracket is the scalar extension of the original real operator commutator. -/
theorem realCoordinates_bracket (D E : K) :
    (⁅H.realCoordinates D, H.realCoordinates E⁆ : H.realLie).val.val =
      (operatorBracket D.val.val E.val.val).baseChange ℂ := by
  change operatorBracket (H.realCoordinates D).val.val (H.realCoordinates E).val.val = _
  rw [realCoordinates_operator, realCoordinates_operator]
  simp only [operatorBracket, LinearMap.baseChange_sub, LinearMap.baseChange_mul]

private theorem realCoordinates_lie_eq_zero (D E : K) :
    Commute D.val.val E.val.val ↔ ⁅H.realCoordinates D, H.realCoordinates E⁆ = 0 := by
  constructor
  · intro hc
    apply Subtype.ext
    apply Subtype.ext
    rw [H.realCoordinates_bracket]
    change (operatorBracket D.val.val E.val.val).baseChange ℂ = 0
    rw [show operatorBracket D.val.val E.val.val = 0 from sub_eq_zero.mpr hc.eq,
      LinearMap.baseChange_zero]
  · intro h
    have h0 := congrArg (fun X : H.realLie => X.val.val) h
    rw [H.realCoordinates_bracket] at h0
    change (operatorBracket D.val.val E.val.val).baseChange ℂ = 0 at h0
    have he : realImagOperator (operatorBracket D.val.val E.val.val) 0 = 0 := by
      simpa only [realImagOperator, LinearMap.baseChange_zero, smul_zero, add_zero] using h0
    exact sub_eq_zero.mp ((realImagOperator_eq_zero _ _).mp he).1

private def negativeAmbientKilling : LinearMap.BilinForm ℝ H.realLie :=
  -(killingForm ℝ H.operators).compl₁₂
    H.realLie.toSubmodule.subtype H.realLie.toSubmodule.subtype

/-- The ordinary Cartans of the fixed algebra are exactly its maximal commuting
subspaces in the native real operator coordinates. -/
theorem realOperatorCartan_iff (C : LieSubalgebra ℝ H.realLie) :
    IsRepresentedOperatorCartan (C.toSubmodule.comap H.realCoordinates.toLinearMap) ↔
      C.IsCartanSubalgebra := by
  have hpositive (X : H.realLie) (hX : X ≠ 0) : 0 < H.negativeAmbientKilling X X :=
    neg_pos.mpr (H.compact X.val fun he => hX (Subtype.ext he))
  have hinvariant (X Y Z : H.realLie) :
      H.negativeAmbientKilling ⁅X,Y⁆ Z = H.negativeAmbientKilling X ⁅Y,Z⁆ :=
    congrArg Neg.neg (LieModule.traceForm_apply_lie_apply ℝ H.operators H.operators
      X.val Y.val Z.val)
  rw [← compactCartan_iff_cartan_of_invariant_positive H.negativeAmbientKilling hpositive hinvariant C]
  constructor
  · intro h X
    obtain ⟨D, rfl⟩ := H.realCoordinates.surjective X
    constructor
    · intro hD
      apply (h D).mp
      rintro ⟨E, hE⟩
      exact (H.realCoordinates_lie_eq_zero D E).mpr (hD _ hE)
    · intro hD Y hY
      obtain ⟨E, rfl⟩ := H.realCoordinates.surjective Y
      exact (H.realCoordinates_lie_eq_zero D E).mp ((h D).mpr hD ⟨E, hY⟩)
  · intro h D
    constructor
    · intro hD
      apply (h (H.realCoordinates D)).mp
      intro Y hY
      obtain ⟨E, rfl⟩ := H.realCoordinates.surjective Y
      exact (H.realCoordinates_lie_eq_zero D E).mp (hD ⟨E, hY⟩)
    · intro hD E
      exact (H.realCoordinates_lie_eq_zero D E).mpr ((h (H.realCoordinates D)).mpr hD _ E.property)

/-- An arbitrary maximal commuting subspace of the native derivations as a Lie Cartan. -/
def realOperatorCartanSubalgebra (T : Submodule ℝ K)
    (hT : IsRepresentedOperatorCartan T) : LieSubalgebra ℝ H.realLie where
  toSubmodule := T.map H.realCoordinates.toLinearMap
  lie_mem' := by
    rintro _ _ ⟨D, hD, rfl⟩ ⟨E, hE, rfl⟩
    have he := (H.realCoordinates_lie_eq_zero D E).mp (hT.commutes ⟨D,hD⟩ ⟨E,hE⟩)
    change ⁅H.realCoordinates D,H.realCoordinates E⁆ ∈ T.map H.realCoordinates.toLinearMap
    rw [he]
    exact Submodule.zero_mem _

theorem realOperatorCartanSubalgebra_toSubmodule (T : Submodule ℝ K)
    (hT : IsRepresentedOperatorCartan T) :
    (H.realOperatorCartanSubalgebra T hT).toSubmodule = T.map H.realCoordinates.toLinearMap := rfl

theorem realOperatorCartanSubalgebra_spec (T : Submodule ℝ K)
    (hT : IsRepresentedOperatorCartan T) :
    (H.realOperatorCartanSubalgebra T hT).IsCartanSubalgebra ∧
      Module.finrank ℝ (H.realOperatorCartanSubalgebra T hT) = Module.finrank ℝ T := by
  constructor
  · apply (H.realOperatorCartan_iff _).mp
    rwa [H.realOperatorCartanSubalgebra_toSubmodule,
      Submodule.comap_map_eq_of_injective H.realCoordinates.injective]
  · exact (H.realCoordinates.submoduleMap T).finrank_eq.symm

/-- View any maximal commuting second-row subspace as a Lie subalgebra of actual operators. -/
def operatorCartanSubalgebra (C : Submodule ℝ (secondRowSpace M K))
    (hC : IsSecondRowOperatorCartan M K C) : LieSubalgebra ℝ H.operators where
  toSubmodule := C.map H.coordinates.toLinearMap
  lie_mem' := by
    rintro _ _ ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
    have hc := ((hC X).mpr hX) ⟨Y, hY⟩
    have hz : ⁅H.coordinates X, H.coordinates Y⁆ = 0 :=
      Subtype.ext (sub_eq_zero.mpr hc.eq)
    change ⁅H.coordinates X, H.coordinates Y⁆ ∈ C.map H.coordinates.toLinearMap
    rw [hz]
    exact Submodule.zero_mem _

theorem operatorCartanSubalgebra_toSubmodule (C : Submodule ℝ (secondRowSpace M K))
    (hC : IsSecondRowOperatorCartan M K C) :
    (H.operatorCartanSubalgebra C hC).toSubmodule = C.map H.coordinates.toLinearMap := rfl

theorem operatorCartanSubalgebra_spec [FiniteDimensional ℝ J] (C : Submodule ℝ (secondRowSpace M K))
    (hC : IsSecondRowOperatorCartan M K C) :
    (H.operatorCartanSubalgebra C hC).IsCartanSubalgebra ∧
      Module.finrank ℝ (H.operatorCartanSubalgebra C hC) = Module.finrank ℝ C := by
  constructor
  · apply (H.operatorCartan_iff _).mp
    rwa [H.operatorCartanSubalgebra_toSubmodule, Submodule.comap_map_eq_of_injective H.coordinates.injective]
  · exact (H.coordinates.submoduleMap C).finrank_eq.symm

end
end ThirteenPlanes.Cartan.SecondRowCompactRealization
