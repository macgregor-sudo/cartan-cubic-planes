module

public import ThirteenPlanes.Shares.RecoveryUnlabelled
public import ThirteenPlanes.Shares.RecoveryEndpoints

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] {h : SymmetricCubic V} {P : PlaneDecomposition V ι} {c t : ℝ}

abbrev OrthogonalMap (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :=
  V ≃ₗᵢ[ℝ] V

/-- The orthogonal stabilizer of the symmetric trilinear form. -/
def cubicPreserved (h : SymmetricCubic V) (g : OrthogonalMap V) : Prop :=
  h.pullback g.toLinearMap = h

/-- An orthogonal map permutes the planes if its pullback relabels the system. -/
def permutesPlanes (P : PlaneDecomposition V ι) (g : OrthogonalMap V) : Prop :=
  ∃ e : ι ≃ ι, ∀ (i : ι) (x : V), g x ∈ P.plane i ↔ x ∈ P.plane (e i)

def energyPreserved (h : SymmetricCubic V) (P : PlaneDecomposition V ι)
    (c t : ℝ) (g : OrthogonalMap V) : Prop :=
  ∀ x : V, ‖x‖ = 1 → normalizedPencilEnergy h P c t (g x) = normalizedPencilEnergy h P c t x

theorem cubicPreserved_iff (g : OrthogonalMap V) :
    cubicPreserved h g ↔ ∀ x y z, h.apply (g x) (g y) (g z) = h.apply x y z := by
  constructor
  · intro he x y z
    have hv := congrArg (fun C : SymmetricCubic V => C.apply x y z) he
    rw [SymmetricCubic.pullback_apply] at hv
    exact hv
  · intro he
    apply SymmetricCubic.ext
    intro x y z
    rw [SymmetricCubic.pullback_apply]
    exact he x y z

/-- The group of orthogonal symmetries of the round cubic that permute its planes. -/
def planeCubicStabilizer (h : SymmetricCubic V) (P : PlaneDecomposition V ι) :
    Subgroup (OrthogonalMap V) where
  carrier := {g | cubicPreserved h g ∧ permutesPlanes P g}
  one_mem' := ⟨(cubicPreserved_iff _).mpr fun _ _ _ => rfl, ⟨Equiv.refl _, fun _ _ => Iff.rfl⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, e, he⟩ ⟨hb, f, hf⟩
    refine ⟨(cubicPreserved_iff _).mpr fun x y z => ?_, ⟨e.trans f, fun i x => ?_⟩⟩
    · change h.apply (a (b x)) (a (b y)) (a (b z)) = _
      rw [(cubicPreserved_iff a).mp ha, (cubicPreserved_iff b).mp hb]
    · exact (he i (b x)).trans (hf (e i) x)
  inv_mem' := by
    rintro a ⟨ha, e, he⟩
    refine ⟨(cubicPreserved_iff _).mpr fun x y z => ?_, ⟨e.symm, fun i x => ?_⟩⟩
    · simpa using ((cubicPreserved_iff a).mp ha (a.symm x) (a.symm y) (a.symm z)).symm
    · change a.symm x ∈ P.plane i ↔ x ∈ P.plane (e.symm i)
      simpa using (he (e.symm i) (a.symm x)).symm

/-- The orthogonal symmetries of the energy on the unit sphere. -/
def pencilEnergyStabilizer (h : SymmetricCubic V) (P : PlaneDecomposition V ι) (c t : ℝ) :
    Subgroup (OrthogonalMap V) where
  carrier := {g | energyPreserved h P c t g}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x hx
    exact (ha (b x) (by rwa [b.norm_map])).trans (hb x hx)
  inv_mem' := by
    intro a ha x hx
    simpa using (ha (a.symm x) (by rwa [a.symm.norm_map])).symm

theorem normalizedPencilEnergy_smul (r : ℝ) (x : V) :
    normalizedPencilEnergy h P c t (r • x) = r ^ 4 * normalizedPencilEnergy h P c t x := by
  unfold normalizedPencilEnergy
  let q := interactionCubic (planePencil h P) t
  change ‖q.L (r • x) (r • x)‖ ^ 2 / c = r ^ 4 * (‖q.L x x‖ ^ 2 / c)
  rw [map_smul q.L, LinearMap.smul_apply, map_smul, smul_smul, ← pow_two,
    norm_smul, Real.norm_of_nonneg (sq_nonneg r), mul_pow]
  ring

private theorem normalizedPencilEnergies_eq_of_unit {k : SymmetricCubic V}
    {Q : PlaneDecomposition V ι} {s : ℝ}
    (eq : ∀ x : V, ‖x‖ = 1 → normalizedPencilEnergy h P c t x =
      normalizedPencilEnergy k Q c s x) :
    ∀ x : V, normalizedPencilEnergy h P c t x = normalizedPencilEnergy k Q c s x := by
  intro x
  by_cases hx : x = 0
  · simp [hx, normalizedPencilEnergy, SymmetricCubic.squareMap]
  let u := ‖x‖⁻¹ • x
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hn]
  have hr : ‖x‖ • u = x := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [← hr]
  rw [normalizedPencilEnergy_smul (h := h), normalizedPencilEnergy_smul (h := k), eq u hu]

private theorem cubic_nondegenerate (round : IsRound h c) (closed : IsClosedPlaneSystem h P)
    (m : 1 < Fintype.card ι) :
    interactionCubic (planePencil h P) t ≠ -interactionCubic (planePencil h P) t := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let i : ι := Classical.choice ‹Nonempty ι›
  obtain ⟨_, z, hz⟩ := binaryPlaneNormalForm (restriction_isRound round closed i) (P.dimension i)
  let u := z.symm 1
  have hu := hz u
  rw [z.apply_symm_apply, one_pow, Complex.one_re, mul_one, P.restriction_apply] at hu
  intro he
  have hv := congrArg (fun q : SymmetricCubic V => q.apply (u : V) u u) he
  have hneg (q : SymmetricCubic V) : (-q).apply (u : V) u u = -q.apply (u : V) u u := by
    rw [← neg_one_smul ℝ q, SymmetricCubic.apply_smul, neg_one_mul]
  rw [hneg, pencil_cubic_on_plane closed, hu] at hv
  linarith [Real.sqrt_pos.2 round.positive]

private theorem preserve_pencil_of_mem (g : OrthogonalMap V) (hg : g ∈ planeCubicStabilizer h P) :
    cubicPreserved (interactionCubic (planePencil h P) t) g := by
  obtain ⟨hd, e, he⟩ := hg
  have hP : pullbackPlaneSystem P g = reindexPlaneSystem P e := by
    apply planeSystem_eq_of_pointwise
    intro i
    ext x
    exact (mem_pullbackPlaneSystem P g i x).trans (he i x)
  unfold cubicPreserved at hd ⊢
  rw [← interactionCubic_pencil_pullback, hP, hd, interactionCubic_pencil_reindex]

private theorem energy_of_preserve_pencil (g : OrthogonalMap V)
    (hg : cubicPreserved (interactionCubic (planePencil h P) t) g) :
    g ∈ pencilEnergyStabilizer h P c t := by
  intro x _
  have hp := Peirce.pullback_intertwines_product g hg.symm x x
  change ‖(interactionCubic (planePencil h P) t).L (g x) (g x)‖ ^ 2 / c =
    ‖(interactionCubic (planePencil h P) t).L x x‖ ^ 2 / c
  rw [← hp, g.norm_map]

private theorem energy_even (x : V) :
    normalizedPencilEnergy h P c t (-x) = normalizedPencilEnergy h P c t x := by
  have he := normalizedPencilEnergy_smul (h := h) (P := P) (c := c) (t := t) (-1) x
  rw [neg_one_smul] at he
  norm_num at he
  exact he

private theorem energy_recovery_of_mem (round : IsRound h c) (closed : IsClosedPlaneSystem h P)
    (m : 1 < Fintype.card ι) (ht : 0 < t) (ht₁ : t ≠ 1)
    (g : OrthogonalMap V) (hg : g ∈ pencilEnergyStabilizer h P c t) :
    permutesPlanes P g ∧
      ((h.pullback g.toLinearMap = h ∧ cubicPreserved (interactionCubic (planePencil h P) t) g) ∨
      (h.pullback g.toLinearMap = -h ∧
        (interactionCubic (planePencil h P) t).pullback g.toLinearMap =
        -interactionCubic (planePencil h P) t)) := by
  have eq : ∀ x : V, normalizedPencilEnergy h P c t x =
      normalizedPencilEnergy (h.pullback g.toLinearMap) (pullbackPlaneSystem P g) c t x := by
    apply normalizedPencilEnergies_eq_of_unit
    intro x hx
    rw [normalizedPencilEnergy_pullback]
    exact (hg x hx).symm
  obtain ⟨e, he, _, signs⟩ := planePencil_unlabelled_recovery P (pullbackPlaneSystem P g)
    round (IsRound.pullback_isometry round g) closed (IsClosedPlaneSystem.pullback_isometry closed g) m m ht ht ht₁ ht₁ eq
  refine ⟨⟨e.symm, fun i x => ?_⟩, ?_⟩
  · rw [← mem_pullbackPlaneSystem P g i x, he (e.symm i), e.apply_symm_apply]
  · simp only [interactionCubic_pencil_pullback] at signs
    exact signs

/-- The orthogonal pencil-cubic stabilizer is the plane-permuting round-cubic group. -/
theorem pencilCubic_stabilizer_eq (round : IsRound h c) (closed : IsClosedPlaneSystem h P)
    (m : 1 < Fintype.card ι) (ht : 0 < t) (ht₁ : t ≠ 1) (g : OrthogonalMap V) :
    cubicPreserved (interactionCubic (planePencil h P) t) g ↔ g ∈ planeCubicStabilizer h P := by
  refine ⟨fun hg => ?_, preserve_pencil_of_mem g⟩
  obtain ⟨hp, hs | hs⟩ :=
    energy_recovery_of_mem round closed m ht ht₁ g (energy_of_preserve_pencil g hg)
  · exact ⟨hs.1, hp⟩
  · exact (cubic_nondegenerate round closed m (hg.symm.trans hs.2)).elim

private theorem cubic_pullback_neg (q : SymmetricCubic V) (g : OrthogonalMap V) :
    q.pullback (g * LinearIsometryEquiv.neg ℝ).toLinearMap = -(q.pullback g.toLinearMap) := by
  apply SymmetricCubic.ext
  intro x y z
  rw [← neg_one_smul ℝ (q.pullback g.toLinearMap), SymmetricCubic.apply_smul, neg_one_mul,
    SymmetricCubic.pullback_apply, SymmetricCubic.pullback_apply]
  change q.apply (g (-x)) (g (-y)) (g (-z)) = _
  rw [map_neg, map_neg, map_neg, cubic_negate_three_inputs]
  rfl

private theorem neg_mem_pencilEnergyStabilizer :
    LinearIsometryEquiv.neg ℝ ∈ pencilEnergyStabilizer h P c t := fun x _ => energy_even x

/-- The plane-permuting cubic group and its negative exhaust the energy stabilizer. -/
theorem pencilEnergy_stabilizer_mem_iff (round : IsRound h c) (closed : IsClosedPlaneSystem h P)
    (m : 1 < Fintype.card ι) (ht : 0 < t) (ht₁ : t ≠ 1) (g : OrthogonalMap V) :
    g ∈ pencilEnergyStabilizer h P c t ↔
      g ∈ planeCubicStabilizer h P ∨ g * LinearIsometryEquiv.neg ℝ ∈ planeCubicStabilizer h P := by
  constructor
  · intro hg
    obtain ⟨hp, hs | hs⟩ := energy_recovery_of_mem round closed m ht ht₁ g hg
    · exact Or.inl ⟨hs.1, hp⟩
    · refine Or.inr ((pencilCubic_stabilizer_eq round closed m ht ht₁ _).mp ?_)
      unfold cubicPreserved
      rw [cubic_pullback_neg, hs.2]
      exact neg_neg (interactionCubic (planePencil h P) t)
  · rintro (hg | hg)
    · exact energy_of_preserve_pencil g (preserve_pencil_of_mem g hg)
    · have hm := (pencilEnergyStabilizer h P c t).mul_mem
          (energy_of_preserve_pencil _ (preserve_pencil_of_mem _ hg))
          neg_mem_pencilEnergyStabilizer
      convert hm using 1
      ext x
      change g x = g (-(-x))
      rw [neg_neg]

omit [FiniteDimensional ℝ V] in
private theorem sign_mul_self : (LinearIsometryEquiv.neg ℝ : OrthogonalMap V) *
    LinearIsometryEquiv.neg ℝ = 1 := by
  ext x
  exact neg_neg x

/-- The central subgroup consisting of the identity and minus the identity. -/
def signIsometries (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    Subgroup (OrthogonalMap V) where
  carrier := {g | g = 1 ∨ g = LinearIsometryEquiv.neg ℝ}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul _)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl sign_mul_self
  inv_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr LinearIsometryEquiv.symm_neg

omit [FiniteDimensional ℝ V] in
private theorem sign_commutes (a : OrthogonalMap V) (b : signIsometries V) :
    Commute a b.val := by
  rcases b.property with hb | hb
  · rw [hb]
    exact Commute.one_right a
  · rw [hb]
    ext x
    exact a.map_neg x

/-- For positive unequal couplings the energy stabilizer is the direct product with
the two central signs, via multiplication of the actual isometries. -/
def pencilEnergy_stabilizer_mulEquiv (round : IsRound h c) (closed : IsClosedPlaneSystem h P)
    (m : 1 < Fintype.card ι) (ht : 0 < t) (ht₁ : t ≠ 1) :
    planeCubicStabilizer h P × signIsometries V ≃* pencilEnergyStabilizer h P c t := by
  let G := planeCubicStabilizer h P
  let E := pencilEnergyStabilizer h P c t
  have hGE : G ≤ E := fun {g} hg => energy_of_preserve_pencil g (preserve_pencil_of_mem g hg)
  have hSE : signIsometries V ≤ E := by
    rintro g (rfl | rfl)
    · exact E.one_mem
    · exact neg_mem_pencilEnergyStabilizer
  have hn : LinearIsometryEquiv.neg ℝ ∉ G := by
    intro hg
    have hs := preserve_pencil_of_mem (t := t) _ hg
    have hneg := cubic_pullback_neg (interactionCubic (planePencil h P) t) (1 : OrthogonalMap V)
    rw [one_mul] at hneg
    have h1 : cubicPreserved (interactionCubic (planePencil h P) t) (1 : OrthogonalMap V) :=
      (cubicPreserved_iff _).mpr fun _ _ _ => rfl
    unfold cubicPreserved at hs h1
    rw [h1, hs] at hneg
    exact cubic_nondegenerate round closed m hneg
  let f : G × signIsometries V →* E :=
    { toFun := fun a => ⟨a.1.val * a.2.val, E.mul_mem (hGE a.1.property) (hSE a.2.property)⟩
      map_one' := Subtype.ext (one_mul _)
      map_mul' := fun a b => Subtype.ext (by
        change (a.1.val * b.1.val) * (a.2.val * b.2.val) =
          (a.1.val * a.2.val) * (b.1.val * b.2.val)
        calc
          _ = a.1.val * ((b.1.val * a.2.val) * b.2.val) := by simp only [mul_assoc]
          _ = _ := by rw [(sign_commutes b.1.val a.2).eq]; simp only [mul_assoc]) }
  apply MulEquiv.ofBijective f
  constructor
  · rintro ⟨a, ε⟩ ⟨b, δ⟩ hmul
    have hg : a.val * ε.val = b.val * δ.val := congrArg Subtype.val hmul
    have heq : a.val = b.val → (a, ε) = (b, δ) := by
      intro ha
      have hequal : a.val * ε.val = a.val * δ.val := by
        simpa only [ha] using hg
      have hsign : ε.val = δ.val := mul_left_cancel hequal
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hsign)
    have hmixed {a b : G} (hab : a.val = b.val * LinearIsometryEquiv.neg ℝ) : False := by
      apply hn
      have hba := G.mul_mem (G.inv_mem b.property) a.property
      rwa [hab, ← mul_assoc, inv_mul_cancel, one_mul] at hba
    rcases ε.property with hε | hε <;> rcases δ.property with hδ | hδ
    · apply heq
      simpa only [hε, hδ, mul_one] using hg
    · exact (hmixed (a := a) (b := b) (by simpa only [hε, hδ, mul_one] using hg)).elim
    · exact (hmixed (a := b) (b := a) (by simpa only [hε, hδ, mul_one] using hg.symm)).elim
    · apply heq
      rw [hε, hδ] at hg
      exact mul_right_cancel hg
  · intro g
    rcases (pencilEnergy_stabilizer_mem_iff round closed m ht ht₁ g.val).mp g.property with hp | hp
    · exact ⟨(⟨g.val, hp⟩, 1), Subtype.ext (mul_one _)⟩
    · refine ⟨(⟨g.val * LinearIsometryEquiv.neg ℝ, hp⟩,
        ⟨LinearIsometryEquiv.neg ℝ, Or.inr rfl⟩), Subtype.ext ?_⟩
      change (g.val * LinearIsometryEquiv.neg ℝ) * LinearIsometryEquiv.neg ℝ = g.val
      rw [mul_assoc, sign_mul_self, mul_one]

/-- The full orthogonal group preserves the energy exactly at the round endpoint. -/
theorem pencilEnergy_stabilizer_top_iff (round : IsRound h c) (closed : IsClosedPlaneSystem h P)
    (m : 1 < Fintype.card ι) :
    pencilEnergyStabilizer h P c t = ⊤ ↔ t = 1 := by
  constructor
  · intro he
    have hc := (planePencilEnergy round closed m).2 t
    apply hc.mp
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    let i : ι := Classical.choice ‹Nonempty ι›
    let b := (stdOrthonormalBasis ℝ (P.plane i)).reindex (finCongr (P.dimension i))
    let u : V := b 0
    have hu : ‖u‖ = 1 := b.orthonormal.norm_eq_one 0
    refine ⟨normalizedPencilEnergy h P c t u, fun x hx => ?_⟩
    let g := (ℝ ∙ (u - x))ᗮ.reflection
    have hg : g ∈ pencilEnergyStabilizer h P c t := by rw [he]; exact Subgroup.mem_top g
    have hgx : g u = x := Submodule.reflection_sub (hu.trans hx.symm)
    simpa only [hgx] using hg u hu
  · intro ht
    subst t
    apply top_unique
    intro g _ x _
    rw [normalizedPencilEnergy_one round, normalizedPencilEnergy_one round, g.norm_map]

/-- Every orthogonal map preserving each plane preserves the energy at zero coupling. -/
theorem pencilEnergy_zero_stabilizer (round : IsRound h c) (closed : IsClosedPlaneSystem h P)
    (g : OrthogonalMap V) (hg : ∀ i x, g x ∈ P.plane i ↔ x ∈ P.plane i) :
    g ∈ pencilEnergyStabilizer h P c 0 := by
  have he : pullbackPlaneSystem P g = P := by
    apply planeSystem_eq_of_pointwise
    intro i
    ext x
    exact (mem_pullbackPlaneSystem P g i x).trans (hg i x)
  intro x _
  rw [normalizedPencilEnergy_zero round closed, normalizedPencilEnergy_zero round closed]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pullbackPlaneSystem_proj, he, g.norm_map]

end

end ThirteenPlanes.RoundCubics
