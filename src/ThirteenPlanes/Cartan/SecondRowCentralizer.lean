module

public import ThirteenPlanes.Cartan.OperatorFrames
public import ThirteenPlanes.Cartan.SecondRow

@[expose] public section

set_option backward.privateInPublic true

/-! The centralizer in the actual second-row operator space. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]

private theorem commute_smul_left {R A : Type*} [CommSemiring R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (r : R) {a b : A} (h : Commute a b) :
    Commute (r • a) b := by
  change (r • a) * b = b * (r • a)
  rw [smul_mul_assoc, mul_smul_comm, h.eq]

omit [FiniteDimensional ℝ J] in
private theorem frame_leftMul_commute (M : TraceJordanData J) (F : M.Frame)
    {x y : M.traceFree} (hx : x ∈ F.plane M) (hy : y ∈ F.plane M) :
    Commute (M.L x.val) (M.L y.val) := by
  have hp (a b : Fin 3) : Commute (M.L (F.point a)) (M.L (F.point b)) := by
    by_cases hab : a = b
    · subst b
      exact Commute.refl _
    · apply orthogonal_idempotents_leftMul_commute M
      · simpa using F.mul_point a a
      · simpa using F.mul_point b b
      · simpa [hab] using F.mul_point a b
  have hc (a b : Fin 3) :
      Commute (M.L (M.center (F.point a)).val) (M.L (M.center (F.point b)).val) := by
    change Commute (M.L (F.point a - _ • M.unit)) (M.L (F.point b - _ • M.unit))
    simp only [map_sub, map_smul, M.L_unit]
    have hu (A : Module.End ℝ J) : Commute (LinearMap.id : Module.End ℝ J) A := Commute.one_left A
    exact ((hp a b).sub_right (commute_smul_left _ (hu _)).symm).sub_left
      ((commute_smul_left _ (hu _)).sub_right
        (commute_smul_left _ (commute_smul_left _ (hu _)).symm))
  have extend (u : M.traceFree) (h : ∀ a, Commute (M.L (M.center (F.point a)).val) (M.L u.val))
      {v : M.traceFree} (hv : v ∈ F.plane M) : Commute (M.L v.val) (M.L u.val) := by
    refine Submodule.span_induction (p := fun v _ => Commute (M.L v.val) (M.L u.val))
      (fun v hv => ?_) ?_ (fun v w hv hw hV hW => ?_) (fun r v hv hV => ?_) hv
    · obtain ⟨a, rfl⟩ := hv
      exact h a
    · exact (M.L.map_zero.symm ▸ Commute.zero_left (M.L u.val))
    · simpa only [Submodule.coe_add, map_add] using hV.add_left hW
    · simpa only [Submodule.coe_smul, map_smul] using commute_smul_left r hV
  exact extend y (fun a => (extend _ (fun b => hc b a) hy).symm) hx

omit [FiniteDimensional ℝ J] in
private theorem realImag_commute (A B L M : Module.End ℝ J)
    (hab : Commute A B) (ham : Commute A M) (hlb : Commute L B) (hlm : Commute L M) :
    Commute (realImagOperator A L) (realImagOperator B M) := by
  have base (X Y : Module.End ℝ J) (h : Commute X Y) :
      Commute (X.baseChange ℂ) (Y.baseChange ℂ) := by
    change X.baseChange ℂ * Y.baseChange ℂ = Y.baseChange ℂ * X.baseChange ℂ
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h.eq]
  exact ((base A B hab).add_right (commute_smul_left Complex.I (base A M ham).symm).symm).add_left
    ((commute_smul_left Complex.I (base L B hlb)).add_right
      (commute_smul_left Complex.I (commute_smul_left Complex.I (base L M hlm)).symm).symm)

omit [FiniteDimensional ℝ J] in
theorem secondRow_algebra_commutes (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J))
    (hK : K ≤ M.skewDerivations) (T : Submodule ℝ K)
    (hT : ∀ A B : T, Commute A.val.val.val B.val.val.val)
    (F : M.Frame) (hF : representedFixedPlane M T = F.plane M) :
    ∀ X Y, X ∈ secondRowPiece M T → Y ∈ secondRowPiece M T → Commute X Y := by
  rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
  have hx := (fixedPlane_iff M T p.2).mp hp.2 ⟨q.1, hq.1⟩
  have hy := (fixedPlane_iff M T q.2).mp hq.2 ⟨p.1, hp.1⟩
  have hLx : Commute q.1.val.val (M.L p.2.val) := sub_eq_zero.mp (by
    change operatorBracket q.1.val.val (M.L p.2.val) = 0
    rw [M.bracket_leftMul (hK q.1.property), hx, map_zero])
  have hLy : Commute p.1.val.val (M.L q.2.val) := sub_eq_zero.mp (by
    change operatorBracket p.1.val.val (M.L q.2.val) = 0
    rw [M.bracket_leftMul (hK p.1.property), hy, map_zero])
  exact realImag_commute _ _ _ _ (hT ⟨p.1, hp.1⟩ ⟨q.1, hq.1⟩) hLy hLx.symm
    (frame_leftMul_commute M F (hF ▸ hp.2) (hF ▸ hq.2))

/-- The second-row summand as a submodule of the actual real second row. -/
def secondRowPieceInSpace (M : TraceJordanData J) {K : Submodule ℝ (SkewOperator J)}
    (T : Submodule ℝ K) : Submodule ℝ (secondRowSpace M K) :=
  (T.prod (representedFixedPlane M T)).map (secondRowCoordinates M K).toLinearMap

omit [FiniteDimensional ℝ J] in
/-- Proposition 7.9(a) on the literal complexified endomorphisms. -/
theorem secondRow_operatorCentralizer (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J))
    (hK : K ≤ M.skewDerivations) (T : Submodule ℝ K)
    (hT : ∀ A B : T, Commute A.val.val.val B.val.val.val)
    (selfCent : ∀ D : K,
      (∀ H : T, operatorBracket H.val.val.val D.val.val = 0) ↔ D ∈ T)
    (F : M.Frame) (hF : representedFixedPlane M T = F.plane M) :
    (∀ X : secondRowSpace M K,
      (∀ H : T, operatorBracket (H.val.val.val.baseChange ℂ) X.val = 0) ↔
        X ∈ secondRowPieceInSpace M T) ∧
    (∀ X Y, X ∈ secondRowPiece M T → Y ∈ secondRowPiece M T → Commute X Y) ∧
    (secondRowPieceInSpace M T).map (secondRowTheta M K).toLinearMap =
      secondRowPieceInSpace M T ∧
    (∀ B : Submodule ℝ (secondRowSpace M K),
      (∀ X Y : B, Commute X.val.val Y.val.val) →
      (∀ H : T, secondRowCoordinates M K (H.val, 0) ∈ B) →
      B ≤ secondRowPieceInSpace M T) := by
  have he (p : K × M.traceFree) :
      secondRowCoordinates M K p ∈ secondRowPieceInSpace M T ↔
        p ∈ T.prod (representedFixedPlane M T) := by
    rw [secondRowPieceInSpace, Submodule.mem_map_equiv]
    simp only [LinearEquiv.symm_apply_apply]
  have hcent (X : secondRowSpace M K) :
      (∀ H : T, operatorBracket (H.val.val.val.baseChange ℂ) X.val = 0) ↔
        X ∈ secondRowPieceInSpace M T := by
    obtain ⟨p, rfl⟩ := (secondRowCoordinates M K).surjective X
    rw [he]
    exact secondRow_centralizer_iff M K hK T selfCent p
  refine ⟨hcent, secondRow_algebra_commutes M K hK T hT F hF, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      change secondRowTheta M K (secondRowCoordinates M K p) ∈ secondRowPieceInSpace M T
      rw [secondRowTheta_coordinates, he]
      exact ⟨hp.1, Submodule.neg_mem _ hp.2⟩
    · rintro _ ⟨p, hp, rfl⟩
      refine ⟨secondRowCoordinates M K (p.1, -p.2), (he _).mpr ⟨hp.1, Submodule.neg_mem _ hp.2⟩, ?_⟩
      change secondRowTheta M K (secondRowCoordinates M K (p.1, -p.2)) =
        secondRowCoordinates M K p
      rw [secondRowTheta_coordinates, neg_neg]
  · intro B hB ht X hX
    apply (hcent X).mp
    intro H
    have hc := (hB ⟨_, ht H⟩ ⟨X, hX⟩).eq
    change operatorBracket (H.val.val.val.baseChange ℂ) X.val = 0
    apply sub_eq_zero.mpr
    have hh : (secondRowCoordinates M K (H.val, 0)).val = H.val.val.val.baseChange ℂ := by
      change realImagOperator H.val.val.val (M.L (0 : J)) = _
      simp [realImagOperator]
    change (secondRowCoordinates M K (H.val, 0)).val * X.val =
      X.val * (secondRowCoordinates M K (H.val, 0)).val at hc
    exact hh ▸ hc

end

end ThirteenPlanes.Cartan
