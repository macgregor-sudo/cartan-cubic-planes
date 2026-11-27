module

public import ThirteenPlanes.Cartan.NativeSecondRow

@[expose] public section

/-! Maximal commuting subspaces and unique Cartan extensions in the native second row. -/

namespace ThirteenPlanes.Cartan

noncomputable section

section Maximal

variable {E A : Type*} [AddCommMonoid E] [Module ℝ E] [Ring A] [Module ℝ A]
  [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]

/-- The self-centralizing condition on the operators represented by a real subspace. -/
def IsOperatorCartanFor (f : E →ₗ[ℝ] A) (T : Submodule ℝ E) : Prop :=
  ∀ x : E, (∀ y : T, Commute (f x) (f y)) ↔ x ∈ T

/-- The commuting subspaces maximal for inclusion are exactly the self-centralizing ones. -/
theorem isOperatorCartanFor_iff_maximal (f : E →ₗ[ℝ] A) (T : Submodule ℝ E) :
    IsOperatorCartanFor f T ↔
      (∀ x y : T, Commute (f x) (f y)) ∧
        ∀ S : Submodule ℝ E, T ≤ S → (∀ x y : S, Commute (f x) (f y)) → S ≤ T := by
  constructor
  · intro h
    refine ⟨fun x y => ((h x).mpr x.property) y, ?_⟩
    intro S hTS hS x hx
    exact (h x).mp fun y => hS ⟨x, hx⟩ ⟨y, hTS y.property⟩
  · rintro ⟨hcomm, hmax⟩ x
    refine ⟨?_, fun hx y => hcomm ⟨x, hx⟩ y⟩
    intro hx
    let S := T ⊔ ℝ ∙ x
    have hS (a b : S) : Commute (f a) (f b) := by
      obtain ⟨a₀, ha, a₁, ha₁, hA⟩ := Submodule.mem_sup.mp a.property
      obtain ⟨b₀, hb, b₁, hb₁, hB⟩ := Submodule.mem_sup.mp b.property
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp ha₁
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hb₁
      have ha' : (a : E) = a₀ + r • x := hA.symm.trans (congrArg (a₀ + ·) hr.symm)
      have hb' : (b : E) = b₀ + s • x := hB.symm.trans (congrArg (b₀ + ·) hs.symm)
      change Commute (f a.val) (f b.val)
      rw [ha', hb', map_add, map_add, map_smul, map_smul]
      exact ((hcomm ⟨a₀, ha⟩ ⟨b₀, hb⟩).add_right ((hx ⟨a₀, ha⟩).symm.smul_right s)).add_left
        (((hx ⟨b₀, hb⟩).smul_left r).add_right (((Commute.refl (f x)).smul_left r).smul_right s))
    exact hmax S le_sup_left hS ((show ℝ ∙ x ≤ S from le_sup_right) (Submodule.mem_span_singleton_self x))

end Maximal

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- The faithful inclusion of the marked skew operators in the full native endomorphism space. -/
def representedOperatorMap (K : Submodule ℝ (SkewOperator J)) : K →ₗ[ℝ] Module.End ℝ J where
  toFun x := x.val.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev IsRepresentedOperatorCartan {K : Submodule ℝ (SkewOperator J)} (T : Submodule ℝ K) : Prop :=
  IsOperatorCartanFor (E := ↥K) (representedOperatorMap K) T

theorem isRepresentedOperatorCartan_iff_maximal {K : Submodule ℝ (SkewOperator J)}
    (T : Submodule ℝ K) :
    IsRepresentedOperatorCartan T ↔
      (∀ x y : T, Commute x.val.val.val y.val.val.val) ∧
        ∀ S : Submodule ℝ K, T ≤ S →
          (∀ x y : S, Commute x.val.val.val y.val.val.val) → S ≤ T :=
  isOperatorCartanFor_iff_maximal (representedOperatorMap K) T

theorem IsRepresentedOperatorCartan.commutes {K : Submodule ℝ (SkewOperator J)}
    {T : Submodule ℝ K} (h : IsRepresentedOperatorCartan T) (x y : T) :
    Commute x.val.val.val y.val.val.val :=
  ((h x).mpr x.property) y

theorem IsRepresentedOperatorCartan.selfCent {K : Submodule ℝ (SkewOperator J)}
    {T : Submodule ℝ K} (h : IsRepresentedOperatorCartan T) (D : K) :
    (∀ H : T, operatorBracket H.val.val.val D.val.val = 0) ↔ D ∈ T := by
  rw [← h D]
  constructor
  · intro hh H
    exact (sub_eq_zero.mp (hh H)).symm
  · intro hh H
    exact sub_eq_zero.mpr (hh H).symm.eq

abbrev IsSecondRowOperatorCartan (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J))
    (C : Submodule ℝ (secondRowSpace M K)) : Prop :=
  IsOperatorCartanFor (E := ↥(secondRowSpace M K)) (secondRowSpace M K).subtype C

/-- Embed an operator in the real summand of the actual second-row operator space. -/
def secondRowRealInclusion (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J)) :
    K →ₗ[ℝ] secondRowSpace M K :=
  (secondRowCoordinates M K).toLinearMap.comp (LinearMap.inl ℝ K M.traceFree)

@[simp] theorem secondRowRealInclusion_apply (M : TraceJordanData J)
    (K : Submodule ℝ (SkewOperator J)) (D : K) :
    secondRowRealInclusion M K D = secondRowCoordinates M K (D, 0) := rfl

theorem secondRowRealInclusion_mem_piece (M : TraceJordanData J)
    {K : Submodule ℝ (SkewOperator J)} (T : Submodule ℝ K) (H : T) :
    secondRowRealInclusion M K H.val ∈ secondRowPieceInSpace M T := by
  exact Submodule.mem_map_of_mem
    (show (H.val, 0) ∈ T.prod (representedFixedPlane M T) from ⟨H.property, Submodule.zero_mem _⟩)

@[simp] theorem secondRowRealInclusion_operator (M : TraceJordanData J)
    (K : Submodule ℝ (SkewOperator J)) (D : K) :
    (secondRowRealInclusion M K D).val = D.val.val.baseChange ℂ := by
  change realImagOperator D.val.val (M.L (0 : J)) = _
  simp [realImagOperator]

/-- The Cartan extension of a real operator Cartan in the second row. -/
structure SecondRowCartanExtension (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J))
    (T : Submodule ℝ K) (rank : ℕ) : Prop where
  isCartan : IsSecondRowOperatorCartan M K (secondRowPieceInSpace M T)
  commutes : ∀ X Y : secondRowPieceInSpace M T, Commute X.val.val Y.val.val
  stable : (secondRowPieceInSpace M T).map (secondRowTheta M K).toLinearMap =
    secondRowPieceInSpace M T
  finrank_eq : Module.finrank ℝ (secondRowPieceInSpace M T) = rank + 2
  unique : ∀ C : Submodule ℝ (secondRowSpace M K), IsSecondRowOperatorCartan M K C →
    (∀ H : T, secondRowRealInclusion M K H.val ∈ C) → C = secondRowPieceInSpace M T

variable [FiniteDimensional ℝ J]

theorem secondRowCartanExtension_of_centralizer (M : TraceJordanData J)
    {K : Submodule ℝ (SkewOperator J)} (T : Submodule ℝ K) {rank : ℕ}
    (hRank : Module.finrank ℝ T = rank)
    (hPlane : Module.finrank ℝ (representedFixedPlane M T) = 2)
    (hCent : ∀ X : secondRowSpace M K,
      (∀ H : T, operatorBracket (H.val.val.val.baseChange ℂ) X.val = 0) ↔
        X ∈ secondRowPieceInSpace M T)
    (hComm : ∀ X Y, X ∈ secondRowPiece M T → Y ∈ secondRowPiece M T → Commute X Y)
    (hStable : (secondRowPieceInSpace M T).map (secondRowTheta M K).toLinearMap =
      secondRowPieceInSpace M T) :
    SecondRowCartanExtension M K T rank := by
  let P := secondRowPieceInSpace M T
  have mem_op {X : secondRowSpace M K} (hx : X ∈ P) : X.val ∈ secondRowPiece M T := by
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map_of_mem hp
  have comm (X Y : P) : Commute X.val.val Y.val.val :=
    hComm _ _ (mem_op X.property) (mem_op Y.property)
  have hcenter (C : Submodule ℝ (secondRowSpace M K))
      (hC : ∀ X Y : C, Commute X.val.val Y.val.val)
      (ht : ∀ H : T, secondRowRealInclusion M K H.val ∈ C) : C ≤ P := by
    intro X hx
    apply (hCent X).mp
    intro H
    rw [← secondRowRealInclusion_operator M K H.val]
    exact sub_eq_zero.mpr (hC ⟨_, ht H⟩ ⟨X, hx⟩).eq
  have hCartan : IsSecondRowOperatorCartan M K P := by
    intro X
    refine ⟨?_, fun hx Y => comm ⟨X, hx⟩ Y⟩
    intro hX
    apply (hCent X).mp
    intro H
    rw [← secondRowRealInclusion_operator M K H.val]
    exact sub_eq_zero.mpr ((hX ⟨_, secondRowRealInclusion_mem_piece M T H⟩).symm).eq
  refine ⟨hCartan, comm, hStable, ?_, ?_⟩
  · rw [secondRow_piece_dim, hRank, hPlane]
  · intro C hC ht
    have hc := (isOperatorCartanFor_iff_maximal (secondRowSpace M K).subtype C).mp hC
    have hCP : C ≤ P := hcenter C hc.1 ht
    exact le_antisymm hCP (hc.2 P hCP comm)

end
end ThirteenPlanes.Cartan
