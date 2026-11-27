module

public import ThirteenPlanes.Cartan.LieComplexification
public import Mathlib.Tactic.Module

@[expose] public section

set_option backward.privateInPublic true

/-! Killing-orthogonal Cartan decompositions under complexification and real descent. -/

namespace ThirteenPlanes.Cartan

open scoped TensorProduct
open LieAlgebra

noncomputable section

/-- In finite dimensions, a real semisimple Lie algebra is compact exactly when its Killing
form is negative definite. This formulation includes the zero algebra. -/
def CompactKilling (K : Type*) [LieRing K] [LieAlgebra ℝ K] : Prop :=
  ∀ x : K, x ≠ 0 → killingForm ℝ K x x < 0

/-- Abelian and self-centralizing, the usual compact definition of a Cartan subalgebra. -/
def IsCompactCartan {K : Type*} [LieRing K] [LieAlgebra ℝ K]
    (T : LieSubalgebra ℝ K) : Prop :=
  ∀ x : K, (∀ y ∈ T, ⁅x,y⁆ = 0) ↔ x ∈ T

/-- A complete internal direct sum of pairwise Killing-orthogonal Cartan subalgebras. -/
def IsKillingCartanOD {𝕜 L ι : Type*} [Field 𝕜] [LieRing L] [LieAlgebra 𝕜 L]
    [DecidableEq ι] (T : ι → LieSubalgebra 𝕜 L) : Prop :=
  (∀ i, (T i).IsCartanSubalgebra) ∧
    Pairwise (fun i j => ∀ x ∈ T i, ∀ y ∈ T j, killingForm 𝕜 L x y = 0) ∧
    DirectSum.IsInternal (fun i => (T i).toSubmodule)

variable {K : Type*} [LieRing K] [LieAlgebra ℝ K]

theorem compactCartan_iff_cartan [Module.Finite ℝ K] (hK : CompactKilling K)
    (T : LieSubalgebra ℝ K) : IsCompactCartan T ↔ T.IsCartanSubalgebra := by
  constructor
  · intro h
    have : IsLieAbelian T := ⟨fun x y => Subtype.ext ((h x).2 x.property y y.property)⟩
    refine ⟨inferInstance, le_antisymm ?_ T.le_normalizer⟩
    intro x hx
    apply (h x).1
    intro y hy
    have hxy := (T.mem_normalizer_iff x).mp hx y hy
    by_contra hne
    have hneg := hK ⁅x,y⁆ hne
    have hzero : ⁅y, ⁅x,y⁆⁆ = 0 := (h y).2 hy _ hxy
    rw [LieModule.traceForm_apply_lie_apply, hzero, map_zero] at hneg
    exact lt_irrefl _ hneg
  · intro h x
    have : T.IsCartanSubalgebra := h
    have hab : IsLieAbelian T := by
      apply LieModule.isLieAbelian_of_ker_traceForm_eq_bot (R := ℝ) (L := T) (M := K)
      rw [eq_bot_iff]
      intro z hz
      have hz0 : LieModule.traceForm ℝ T K z z = 0 :=
        LinearMap.congr_fun (LinearMap.mem_ker.mp hz) z
      by_contra hne
      have hneg := hK z (fun hz => hne (by simpa using (Subtype.ext hz : z = 0)))
      have he : killingForm ℝ K z z = LieModule.traceForm ℝ T K z z := rfl
      rw [he, hz0] at hneg
      exact lt_irrefl _ hneg
    constructor
    · intro hx
      have hn : x ∈ T.normalizer :=
        (T.mem_normalizer_iff x).mpr fun y hy => hx y hy ▸ T.zero_mem
      simpa only [h.self_normalizing] using hn
    · intro hx y hy
      exact congrArg Subtype.val (@LieModule.IsTrivial.trivial T T _ _ hab ⟨x, hx⟩ ⟨y, hy⟩)

namespace LieComplex

/-- A complexified subalgebra consists of vectors whose two real coordinates belong to it. -/
def extend (T : LieSubalgebra ℝ K) : LieSubalgebra ℂ (LieComplex K) where
  carrier := {x | realPart x ∈ T ∧ imagPart x ∈ T}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact ⟨by simpa only [map_add] using T.add_mem hx.1 hy.1,
      by simpa only [map_add] using T.add_mem hx.2 hy.2⟩
  smul_mem' := by
    intro r x hx
    exact ⟨by rw [realPart_smul]; exact T.sub_mem (T.smul_mem _ hx.1) (T.smul_mem _ hx.2),
      by rw [imagPart_smul]; exact T.add_mem (T.smul_mem _ hx.2) (T.smul_mem _ hx.1)⟩
  lie_mem' := by
    intro x y hx hy
    exact ⟨by rw [realPart_bracket]; exact T.sub_mem (T.lie_mem hx.1 hy.1) (T.lie_mem hx.2 hy.2),
      by rw [imagPart_bracket]; exact T.add_mem (T.lie_mem hx.1 hy.2) (T.lie_mem hx.2 hy.1)⟩

@[simp] theorem mem_extend (T : LieSubalgebra ℝ K) (x : LieComplex K) :
    x ∈ extend T ↔ realPart x ∈ T ∧ imagPart x ∈ T := Iff.rfl

/-- Intersection with the embedded real Lie algebra. -/
def descend (H : LieSubalgebra ℂ (LieComplex K)) : LieSubalgebra ℝ K where
  carrier := {x | ofReal x ∈ H}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ofReal (x + y) ∈ H
    rw [map_add]
    exact H.add_mem hx hy
  smul_mem' := by
    intro r x hx
    change ofReal (r • x) ∈ H
    rw [map_smul]
    exact H.smul_mem (r : ℂ) hx
  lie_mem' := by
    intro x y hx hy
    change ofReal ⁅x, y⁆ ∈ H
    rw [LieHom.map_lie]
    exact H.lie_mem hx hy

@[simp] theorem mem_descend (H : LieSubalgebra ℂ (LieComplex K)) (x : K) :
    x ∈ descend H ↔ ofReal x ∈ H := Iff.rfl

@[simp] theorem descend_extend (T : LieSubalgebra ℝ K) : descend (extend T) = T := by
  ext x
  simp

theorem killing_ofReal [Module.Finite ℝ K] (x y : K) :
    killingForm ℂ (LieComplex K) (ofReal x) (ofReal y) =
      (killingForm ℝ K x y : ℂ) := by
  change LinearMap.trace ℂ (LieComplex K)
    ((LieModule.toEnd ℂ (LieComplex K) (LieComplex K) (1 ⊗ₜ[ℝ] x)).comp
      (LieModule.toEnd ℂ (LieComplex K) (LieComplex K) (1 ⊗ₜ[ℝ] y))) = _
  rw [LieModule.toEnd_baseChange, LieModule.toEnd_baseChange, ← LinearMap.baseChange_comp,
    LinearMap.trace_baseChange]
  rfl

theorem killing_parts [Module.Finite ℝ K] (a b c d : K) :
    killingForm ℂ (LieComplex K) (ofReal a + Complex.I • ofReal b) (ofReal c + Complex.I • ofReal d) =
      (killingForm ℝ K a c : ℂ) - (killingForm ℝ K b d : ℂ) +
        Complex.I * ((killingForm ℝ K a d : ℂ) + (killingForm ℝ K b c : ℂ)) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    killing_ofReal, mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  ring

theorem killing_conjugation_self [Module.Finite ℝ K] (x : LieComplex K) :
    killingForm ℂ (LieComplex K) x (conjugation x) =
      ((killingForm ℝ K (realPart x) (realPart x) + killingForm ℝ K (imagPart x) (imagPart x) : ℝ) : ℂ) := by
  rw [conjugation_decompose, sub_eq_add_neg, ← smul_neg, ← map_neg ofReal]
  nth_rw 1 [← decompose_smul x]
  rw [killing_parts]
  simp only [map_neg, Complex.ofReal_neg, Complex.ofReal_add, sub_neg_eq_add]
  rw [LieModule.traceForm_comm ℝ K K (realPart x) (imagPart x), neg_add_cancel, mul_zero, add_zero]

theorem killing_conjugation_negative [Module.Finite ℝ K] (hK : CompactKilling K)
    {x : LieComplex K} (hx : x ≠ 0) :
    (killingForm ℂ (LieComplex K) x (conjugation x)).re < 0 := by
  rw [killing_conjugation_self, Complex.ofReal_re]
  by_cases hr : realPart x = 0
  · have hi : imagPart x ≠ 0 := by
      intro hi
      exact hx (by simpa [hr, hi] using (decompose x).symm)
    simpa [hr] using hK _ hi
  · have hi : killingForm ℝ K (imagPart x) (imagPart x) ≤ 0 := by
      by_cases h : imagPart x = 0
      · simp [h]
      · exact (hK _ h).le
    exact add_neg_of_neg_of_nonpos (hK _ hr) hi

private theorem eq_of_parts {x y : LieComplex K}
    (hr : realPart x = realPart y) (hi : imagPart x = imagPart y) : x = y := by
  rw [← decompose x, ← decompose y, hr, hi]

@[simp] theorem realPart_conjugation (x : LieComplex K) :
    realPart (conjugation x) = realPart x := by
  rw [conjugation_decompose, map_sub, realPart_smul]
  simp

@[simp] theorem imagPart_conjugation (x : LieComplex K) :
    imagPart (conjugation x) = -imagPart x := by
  rw [conjugation_decompose, map_sub, imagPart_smul]
  simp

theorem conjugation_involutive : Function.Involutive (conjugation : LieComplex K → LieComplex K) :=
  fun x => eq_of_parts (by simp) (by simp)

theorem extend_descend_of_stable (H : LieSubalgebra ℂ (LieComplex K))
    (hH : Set.MapsTo conjugation (H : Set (LieComplex K)) (H : Set (LieComplex K))) : extend (descend H) = H := by
  ext x
  constructor
  · rintro ⟨hr, hi⟩
    rw [← decompose_smul x]
    exact H.add_mem hr (H.smul_mem Complex.I hi)
  · intro hx
    have hxc := hH hx
    have hr : ofReal (realPart x) = (1 / 2 : ℂ) • (x + conjugation x) := by
      apply eq_of_parts
      · simp [realPart_smul]; module
      · simp [imagPart_smul]
    have hi : ofReal (imagPart x) = (-Complex.I / 2) • (x - conjugation x) := by
      apply eq_of_parts
      · simp [realPart_smul, sub_neg_eq_add]; module
      · simp [imagPart_smul, sub_neg_eq_add]
    exact ⟨by rw [mem_descend, hr]; exact H.smul_mem _ (H.add_mem hx hxc),
      by rw [mem_descend, hi]; exact H.smul_mem _ (H.sub_mem hx hxc)⟩

/- See Anthony Knapp, Structure Theory of Semisimple Lie Groups (1997), §3, pp. 16–17,
for complexification of compact Cartan subalgebras. This proof works with the explicit
normalizer in the explicit complexification. -/
theorem extend_cartan [Module.Finite ℝ K] (hK : CompactKilling K)
    (T : LieSubalgebra ℝ K) (hT : IsCompactCartan T) :
    (extend T).IsCartanSubalgebra := by
  have : IsLieAbelian (extend T) := by
    constructor
    intro x y
    apply Subtype.ext
    obtain ⟨hxr, hxi⟩ := x.property
    obtain ⟨hyr, hyi⟩ := y.property
    change ⁅(x : LieComplex K), (y : LieComplex K)⁆ = 0
    refine eq_of_parts ?_ ?_
    · simp only [realPart_bracket, (hT _).2 hxr _ hyr, (hT _).2 hxi _ hyi, sub_self, map_zero]
    · simp only [imagPart_bracket, (hT _).2 hxr _ hyi, (hT _).2 hxi _ hyr, add_zero, map_zero]
  refine ⟨inferInstance, le_antisymm ?_ (extend T).le_normalizer⟩
  intro x hx
  have hrim (y : K) (hy : y ∈ T) :
      ⁅realPart x,y⁆ ∈ T ∧ ⁅imagPart x,y⁆ ∈ T := by
    have hreal : ofReal y ∈ extend T := by simp [hy]
    have h := ((extend T).mem_normalizer_iff x).mp hx (ofReal y) hreal
    simpa only [mem_extend, realPart_bracket, imagPart_bracket, realPart_ofReal,
      imagPart_ofReal, lie_zero, sub_zero, zero_add] using h
  have hN := ((compactCartan_iff_cartan hK T).mp hT).self_normalizing
  have hr : realPart x ∈ T := by
    rw [← hN, T.mem_normalizer_iff]
    exact fun y hy => (hrim y hy).1
  have hi : imagPart x ∈ T := by
    rw [← hN, T.mem_normalizer_iff]
    exact fun y hy => (hrim y hy).2
  exact ⟨hr, hi⟩

/-- Pull the real part of a setwise stable Cartan back through the real inclusion. -/
theorem descend_cartan (H : LieSubalgebra ℂ (LieComplex K))
    (hH : Set.MapsTo conjugation (H : Set (LieComplex K)) (H : Set (LieComplex K))) (hC : H.IsCartanSubalgebra) :
    (descend H).IsCartanSubalgebra := by
  have : H.IsCartanSubalgebra := hC
  let e : descend H →ₗ⁅ℝ⁆ RestrictScalars ℝ ℂ H :=
    { toFun := fun x => ⟨ofReal x.val, x.property⟩
      map_add' := fun x y => Subtype.ext (map_add ofReal x.val y.val)
      map_smul' := fun a x => Subtype.ext (map_smul ofReal a x.val)
      map_lie' := fun {x y} => Subtype.ext (LieHom.map_lie ofReal x.val y.val) }
  have he : Function.Injective e := fun x y h => Subtype.ext (ofReal_injective (congrArg Subtype.val h))
  have : LieRing.IsNilpotent (RestrictScalars ℝ ℂ H) := by
    change LieRing.IsNilpotent H
    exact hC.nilpotent
  have hNil : LieRing.IsNilpotent (descend H) := he.lieAlgebra_isNilpotent
  refine ⟨hNil, le_antisymm ?_ (descend H).le_normalizer⟩
  intro x hx
  change ofReal x ∈ H
  rw [← hC.self_normalizing]
  apply (H.mem_normalizer_iff _).mpr
  intro y hy
  have hext : y ∈ extend (descend H) := by rw [extend_descend_of_stable H hH]; exact hy
  have hparts := (mem_extend (descend H) y).mp hext
  have hr := ((descend H).mem_normalizer_iff x).mp hx _ hparts.1
  have hi := ((descend H).mem_normalizer_iff x).mp hx _ hparts.2
  rw [← decompose_smul y, lie_add, lie_smul, ← LieHom.map_lie, ← LieHom.map_lie]
  exact H.add_mem hr (H.smul_mem _ hi)

end LieComplex

private theorem internal_of_orthogonal {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [DecidableEq ι] (T : ι → Submodule 𝕜 V) (B : LinearMap.BilinForm 𝕜 V)
    (test : V → V) (hT : ∀ i x, x ∈ T i → test x ∈ T i)
    (hB : ∀ x, B x (test x) = 0 → x = 0)
    (horth : Pairwise (fun i j => ∀ x ∈ T i, ∀ y ∈ T j, B x y = 0))
    (hspan : iSup T = ⊤) : DirectSum.IsInternal T := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _ hspan
  rw [iSupIndep_def]
  intro i
  refine Submodule.disjoint_def.mpr fun x hxi hx => hB x ?_
  have ht := hT i x hxi
  refine Submodule.iSup_induction _ (motive := fun z => B z (test x) = 0) hx ?_ (by simp) ?_
  · intro j y hy
    refine Submodule.iSup_induction _ (motive := fun z => B z (test x) = 0) hy ?_ (by simp) ?_
    · exact fun hj z hz => horth hj z hz _ ht
    · intro a b ha hb
      simp [ha, hb]
  · intro a b ha hb
    simp [ha, hb]

open LieComplex in
/-- Lemma 7.2, complexification. The Killing form used in both decompositions is the
trace of the adjoint representation of the actual Lie algebra. -/
theorem compactCartanOD_complexification [Module.Finite ℝ K] (hK : CompactKilling K)
    {ι : Type*} [DecidableEq ι] (T : ι → LieSubalgebra ℝ K) (hT : IsKillingCartanOD T) :
    IsKillingCartanOD (fun i => extend (T i)) := by
  have horth : Pairwise (fun i j => ∀ x ∈ extend (T i), ∀ y ∈ extend (T j),
      killingForm ℂ (LieComplex K) x y = 0) := by
    intro i j hij x hx y hy
    obtain ⟨hrx, hix⟩ := hx
    obtain ⟨hry, hiy⟩ := hy
    conv_lhs => rw [← decompose_smul x, ← decompose_smul y]
    rw [killing_parts]
    simp [hT.2.1 hij _ hrx _ hry, hT.2.1 hij _ hrx _ hiy,
      hT.2.1 hij _ hix _ hry, hT.2.1 hij _ hix _ hiy]
  have ht : iSup (fun i => (extend (T i)).toSubmodule) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have he (y : K) : ofReal y ∈ ⨆ i, (extend (T i)).toSubmodule := by
      have hy : y ∈ ⨆ i, (T i).toSubmodule := by
        rw [hT.2.2.submodule_iSup_eq_top]
        trivial
      refine Submodule.iSup_induction _ (motive := fun z => ofReal z ∈
        ⨆ i, (extend (T i)).toSubmodule) hy ?_ ?_ ?_
      · intro i z hz
        exact Submodule.mem_iSup_of_mem i (by change ofReal z ∈ extend (T i); simpa using hz)
      · rw [map_zero]; exact Submodule.zero_mem _
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    rw [← decompose_smul x]
    exact Submodule.add_mem _ (he _) (Submodule.smul_mem _ _ (he _))
  refine ⟨fun i => extend_cartan hK (T i) ((compactCartan_iff_cartan hK _).mpr (hT.1 i)),
    horth, internal_of_orthogonal _ (killingForm ℂ (LieComplex K)) conjugation ?_ ?_ horth ht⟩
  · intro i x hx
    simpa only [LieSubalgebra.mem_toSubmodule, mem_extend, realPart_conjugation,
      imagPart_conjugation, neg_mem_iff] using hx
  · intro x hx
    by_contra hn
    have h := killing_conjugation_negative hK hn
    rw [hx, Complex.zero_re] at h
    exact lt_irrefl _ h

open LieComplex in
/-- Lemma 7.2, descent. A conjugation that permutes the summands fixes every summand
as a subspace. The descended real intersections form a complete Killing-orthogonal sum. -/
theorem compactCartanOD_descent [Module.Finite ℝ K] (hK : CompactKilling K)
    {ι : Type*} [DecidableEq ι] (H : ι → LieSubalgebra ℂ (LieComplex K))
    (hH : IsKillingCartanOD H) (π : Equiv.Perm ι)
    (hp : ∀ i, conjugation '' (H i : Set (LieComplex K)) = H (π i)) :
    (∀ i, conjugation '' (H i : Set (LieComplex K)) = H i) ∧
      IsKillingCartanOD (fun i => descend (H i)) := by
  have hs : ∀ i, Set.MapsTo conjugation (H i : Set (LieComplex K)) (H i : Set (LieComplex K)) := by
    intro i x hx
    change conjugation x ∈ H i
    have hc : conjugation x ∈ H (π i) := by
      change conjugation x ∈ (H (π i) : Set (LieComplex K))
      rw [← hp i]
      exact ⟨x, hx, rfl⟩
    by_cases hi : π i = i
    · simpa only [hi] using hc
    · have h0 : x = 0 := by
        by_contra hn
        have hneg := killing_conjugation_negative hK hn
        rw [hH.2.1 (Ne.symm hi) _ hx _ hc, Complex.zero_re] at hneg
        exact lt_irrefl _ hneg
      simp [h0]
  have hs' (i : ι) : conjugation '' (H i : Set (LieComplex K)) = H i := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hs i hy
    · intro hx
      exact ⟨conjugation x, hs i hx, conjugation_involutive x⟩
  have he (i : ι) : extend (descend (H i)) = H i := extend_descend_of_stable _ (hs i)
  have hort : Pairwise (fun i j => ∀ x ∈ descend (H i), ∀ y ∈ descend (H j),
      killingForm ℝ K x y = 0) := by
    intro i j hij x hx y hy
    have h := hH.2.1 hij (ofReal x) hx (ofReal y) hy
    rwa [killing_ofReal, Complex.ofReal_eq_zero] at h
  have hspan : iSup (fun i => (descend (H i)).toSubmodule) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hh : ofReal x ∈ ⨆ i, (H i).toSubmodule := by
      rw [hH.2.2.submodule_iSup_eq_top]
      trivial
    suffices h : LieComplex.realPart (ofReal x) ∈ ⨆ i, (descend (H i)).toSubmodule by simpa using h
    refine Submodule.iSup_induction _ (motive := fun z => LieComplex.realPart z ∈
      ⨆ i, (descend (H i)).toSubmodule) hh ?_ ?_ ?_
    · intro i z hz
      apply Submodule.mem_iSup_of_mem i
      change LieComplex.realPart z ∈ descend (H i)
      have hz' : z ∈ extend (descend (H i)) := by rw [he]; exact hz
      exact hz'.1
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  refine ⟨hs', fun i => descend_cartan _ (hs i) (hH.1 i), hort,
    internal_of_orthogonal _ (killingForm ℝ K) id (fun _ _ hx => hx) ?_ hort hspan⟩
  intro x h
  by_contra hn
  exact (hK x hn).ne (by simpa using h)


end
end ThirteenPlanes.Cartan
