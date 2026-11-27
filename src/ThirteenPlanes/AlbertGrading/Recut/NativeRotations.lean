module

public import ThirteenPlanes.AlbertGrading.NativeSystem
public import ThirteenPlanes.AlbertGrading.Recut.Recut

@[expose] public section

set_option backward.privateInPublic true

/-! Coordinate transport for line rotations in the complexified Albert algebra. -/

namespace ThirteenPlanes.AlbertGrading

noncomputable section

private def toGrading : Recut.JC ≃ₗ[ℂ] Grading.JC where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem mem_charSpace_iff (ρ : Recut.TernaryAction) (g : Charge) (z : Recut.JC) :
    toGrading z ∈ Grading.charSpace ρ g ↔ z ∈ Recut.charSpace ρ g := by
  constructor
  · intro h s
    exact toGrading.injective (h s)
  · intro h s
    exact congrArg toGrading (h s)

private theorem charSpace_map (ρ : Recut.TernaryAction) (g : Charge) :
    (Recut.charSpace ρ g).map toGrading.toLinearMap = Grading.charSpace ρ g := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_charSpace_iff ρ g w).mpr hw
  · intro hz
    have hz' : toGrading (toGrading.symm z) ∈ Grading.charSpace ρ g := by simpa using hz
    exact ⟨toGrading.symm z, (mem_charSpace_iff ρ g _).mp hz', toGrading.apply_symm_apply z⟩

private theorem grading_of_recut (ρ : Recut.TernaryAction) (hρ : Recut.IsTernaryGrading ρ) :
    Grading.IsTernaryGrading ρ where
  injective := hρ.injective
  automorphism := hρ.automorphism
  lineDim g := by
    rw [← charSpace_map]
    exact (toGrading.submoduleMap (Recut.charSpace ρ g)).finrank_eq.symm.trans (hρ.lineDim g)

private theorem toGrading_mul (x y : Recut.JC) :
    toGrading (Recut.JC.mul x y) = Grading.JC.mul (toGrading x) (toGrading y) := by
  cases x
  cases y
  rfl

private theorem toGrading_conj (x : Recut.JC) : toGrading (Recut.JC.conj x) = Grading.JC.conj (toGrading x) := rfl

private theorem toGrading_one : toGrading Recut.JC.one = Grading.JC.one := rfl

private theorem normalized_iff (z : Recut.JC) : Grading.IsNormalized (toGrading z) ↔ Recut.IsNormalized z := by
  unfold Grading.IsNormalized Recut.IsNormalized
  simp only [← toGrading_mul, ← toGrading_conj, ← toGrading_one, toGrading.injective.eq_iff]

private theorem frameOf_iff (z : Recut.JC) (p : Fin 3 → Glennie.Albert) :
    Grading.IsFrameOf (toGrading z) p ↔ Recut.IsFrameOf z p :=
  ⟨fun h => ⟨h.1, fun a => toGrading.injective (h.2 a)⟩,
    fun h => ⟨h.1, fun a => congrArg toGrading (h.2 a)⟩⟩

private theorem gradedPlaneJ_eq (ρ : Recut.TernaryAction) (g : Charge) :
    Recut.gradedPlaneJ ρ g = Grading.gradedPlaneJ ρ g := by
  ext x
  change Recut.JC.of x ∈ Recut.charSpace ρ g ⊔ Recut.charSpace ρ (-g) ↔
    Grading.JC.of x ∈ Grading.charSpace ρ g ⊔ Grading.charSpace ρ (-g)
  rw [← charSpace_map ρ g, ← charSpace_map ρ (-g), ← Submodule.map_sup]
  constructor
  · intro hx
    exact ⟨Recut.JC.of x, hx, rfl⟩
  · rintro ⟨z, hz, he⟩
    have eq : z = Recut.JC.of x := toGrading.injective he
    exact eq ▸ hz

private theorem gradedPlane_eq (ρ : Recut.TernaryAction) (g : Charge) :
    Recut.gradedPlane ρ g = Grading.gradedPlane ρ g := by
  rw [Recut.gradedPlane, Grading.gradedPlane, gradedPlaneJ_eq]

private theorem pointPlane_eq (ρ : Recut.TernaryAction) (p : SignedPlaneIndex) :
    Recut.pointPlane ρ p = Grading.pointPlane ρ p := gradedPlane_eq ρ _

private theorem lineAlgebraOf_eq (ρ : Recut.TernaryAction) (l : SignedPlaneIndex) :
    Recut.lineAlgebraOf ρ l = Grading.lineAlgebraOf ρ l := by
  simp only [Recut.lineAlgebraOf, Grading.lineAlgebraOf, gradedPlaneJ_eq]

/-- The five graded facts used by the rotated-system proof on its original carrier. -/
theorem nativeGradedFacts : Recut.GradingData.GradedFacts := by
  intro ρ hρ
  have hg := grading_of_recut ρ hρ
  obtain ⟨_, _, _, _, second, third, _, mixed, shares, fifth, _⟩ := nativeGradedSystem ρ hg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hne u hu hn
    obtain ⟨p, hp, _, hU, hj⟩ := (second g hne).2.2 _ ((mem_charSpace_iff ρ g u).mpr hu)
      ((normalized_iff u).mpr hn)
    exact ⟨p, (frameOf_iff u p).mp hp, (gradedPlane_eq ρ g).symm ▸ hU, (gradedPlaneJ_eq ρ g).symm ▸ hj⟩
  · intro u P hP
    apply third (fun g => toGrading (u g)) P
    intro g hg0
    obtain ⟨he, hn, hp⟩ := hP g hg0
    exact ⟨(mem_charSpace_iff ρ g (u g)).mpr he, (normalized_iff (u g)).mpr hn, (frameOf_iff (u g) (P g)).mpr hp⟩
  · simpa only [pointPlane_eq] using mixed
  · simpa only [pointPlane_eq] using shares
  · intro l
    simpa only [lineAlgebraOf_eq] using (fifth l).1

/-- The rotated-system result with the five graded facts discharged. -/
theorem lineRotatedPlaneSystems : Recut.Statements.OtherSystems := Recut.otherSystems nativeGradedFacts

end

end ThirteenPlanes.AlbertGrading
