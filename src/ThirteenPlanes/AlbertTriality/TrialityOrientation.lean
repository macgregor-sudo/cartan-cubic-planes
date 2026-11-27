module

public import ThirteenPlanes.AlbertTriality.TrialityAction
public import ThirteenPlanes.AlbertTriality.TrialityConjObstruction
public import ThirteenPlanes.Isotope.NativeOctonion
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

set_option backward.privateInPublic true

/-!
# Orientation of orthogonal octonion related triples

Pairs of hyperplane reflections lift to related triples by the middle Moufang
identity. Cartan–Dieudonné supplies the reflection factorization. A related
triple of negative determinant would therefore extend octonion conjugation,
which is ruled out by noncommutativity. This is the argument of Yokota,
§1.14, Theorem 1.14.2 and Lemma 1.14.4.
-/

namespace ThirteenPlanes.AlbertTriality

open Glennie
open scoped ThirteenPlanes.MarkedPlane.NativeOctonionEuclidean
open scoped RealInnerProductSpace
open Submodule

noncomputable section
set_option backward.isDefEq.respectTransparency false

local instance : FiniteDimensional ℝ AlbertSequential.Octonion := by
  change FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ)
  infer_instance

private abbrev OctIsometry := AlbertSequential.Octonion ≃ₗᵢ[ℝ] AlbertSequential.Octonion

private abbrev reflect (a : AlbertSequential.Octonion) : OctIsometry :=
  (ℝ ∙ a)ᗮ.reflection

private theorem det_reflect {a : AlbertSequential.Octonion} (ha : a ≠ 0) :
    LinearMap.det (reflect a).toLinearMap = -1 := by
  rw [reflect, Submodule.det_reflection]
  have hdim : Module.finrank ℝ (ℝ ∙ a)ᗮᗮ = 1 := by
    rw [Submodule.orthogonal_orthogonal, finrank_span_singleton ha]
  rw [hdim, pow_one]

private theorem reflect_smul {r : ℝ} (hr : r ≠ 0) (a : AlbertSequential.Octonion) :
    reflect (r • a) = reflect a := by
  simp only [reflect, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hr)]

private theorem glennie_inner (x y : AlbertSequential.Octonion) : ⟪x, y⟫ = octDot x y := by
  rfl

private theorem glennie_norm (x : AlbertSequential.Octonion) : ‖x‖ ^ 2 = octNormSq x := by
  rw [← real_inner_self_eq_norm_sq, glennie_inner]
  exact octDot_self x

private def toOctIsometry (g : OctEquiv) (hg : OctOrtho g) : OctIsometry where
  toLinearEquiv := g
  norm_map' x := by
    have h := (glennie_norm (g x)).trans ((hg x).trans (glennie_norm x).symm)
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

private theorem reflect_unit (a : AlbertSequential.Octonion) (ha : octNormSq a = 1) (x : AlbertSequential.Octonion) :
    reflect a x = -octMul (octMul a (octConj x)) a := by
  rw [reflect, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  have hNorm : ‖a‖ ^ 2 = 1 := (glennie_norm a).trans ha
  change -(2 • (⟪a,x⟫ / ‖a‖ ^ 2) • a - x) = _
  rw [hNorm, div_one, neg_inj, glennie_inner]
  have hpolar :
      octMul x (octConj a) + octMul a (octConj x) =
        (2 : ℝ) • octScalar (octDot a x) := by
    have h := octAdd_conj (octMul x (octConj a))
    rw [octConj_mul, octConj_conj, show octRe (octMul x (octConj a)) = octDot a x
      from octDot_comm x a] at h
    exact h
  have h := congrArg (fun y => octMul y a) hpolar
  rw [octMul_add_left, octMul_smul_left, octMul_scalar_left,
    octMul_right_conj_cancel, ha, one_smul] at h
  rw [two_smul] at h ⊢
  exact (eq_sub_of_add_eq (add_comm x _ ▸ h)).symm

private theorem reflect_pair (a b : AlbertSequential.Octonion) (ha : octNormSq a = 1)
    (hb : octNormSq b = 1) (x : AlbertSequential.Octonion) :
    reflect a (reflect b x) =
      ((octMiddleTriple a ha).comp
        (octMiddleTriple (octConj b) (by exact (octNormSq_conj (b : Glennie.Octonion)).trans hb))).C x := by
  rw [reflect_unit a ha, reflect_unit b hb]
  change -octMul (octMul a (octConj (-(octMiddleTriple b hb).C (octConj x)))) a = _
  rw [show octConj (-(octMiddleTriple b hb).C (octConj x)) =
      -(octConj ((octMiddleTriple b hb).C (octConj x))) from
      map_neg octConjEquiv _]
  rw [show ∀ y, octMul a (-y) = -octMul a y from
    fun y => map_neg (octLeftUnitEquiv a ha) y]
  rw [show ∀ y, octMul (-y) a = -octMul y a from
    fun y => map_neg (octRightUnitEquiv a ha) y, neg_neg]
  simp only [OctRelatedTriple.comp, LinearEquiv.trans_apply, OctRelatedTriple.middle_C,
    octConj_mul, octConj_conj]
  rw [← octMul_flexible (octConj b) x]


private def isometryDet : OctIsometry →* ℝ where
  toFun g := LinearMap.det g.toLinearMap
  map_one' := LinearMap.det_id
  map_mul' g h := LinearMap.det_comp g.toLinearMap h.toLinearMap

private theorem reflect_zero : reflect (0 : AlbertSequential.Octonion) = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  change (ℝ ∙ (0 : AlbertSequential.Octonion))ᗮ.reflection x = x
  apply Submodule.reflection_mem_subspace_eq_self
  simp

private theorem reflections_nonzero (g : OctIsometry) :
    ∃ l : List AlbertSequential.Octonion, (∀ a ∈ l, a ≠ 0) ∧
      g = (l.map reflect).prod := by
  obtain ⟨l, hlen, hl⟩ := g.reflections_generate_dim
  change g = (l.map reflect).prod at hl
  rw [hl]
  clear hl hlen
  induction l with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons a l ih =>
    obtain ⟨l', hn, hprod⟩ := ih
    by_cases ha : a = 0
    · exact ⟨l', hn, by simpa only [List.map_cons, List.prod_cons, ha, reflect_zero, one_mul]
        using hprod⟩
    · refine ⟨a :: l', ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hn b hb
      · simp only [List.map_cons, List.prod_cons, hprod]

private theorem det_reflections (l : List AlbertSequential.Octonion)
    (hn : ∀ a ∈ l, a ≠ 0) : isometryDet (l.map reflect).prod = (-1) ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : isometryDet (reflect a) = -1 := det_reflect (hn a List.mem_cons_self)
    simp only [List.map_cons, List.prod_cons, List.length_cons, map_mul, ha,
      ih (fun b hb => hn b (List.mem_cons_of_mem a hb)), pow_succ, mul_comm]

private theorem det_ortho (g : OctEquiv) (hg : OctOrtho g) :
    LinearMap.det g.toLinearMap = 1 ∨ LinearMap.det g.toLinearMap = -1 := by
  obtain ⟨l, hn, hl⟩ := reflections_nonzero (toOctIsometry g hg)
  change isometryDet (toOctIsometry g hg) = 1 ∨ isometryDet (toOctIsometry g hg) = -1
  rw [hl, det_reflections l hn]
  exact neg_one_pow_eq_or (R := ℝ) l.length

private def identityTriple : OctRelatedTriple where
  A := LinearEquiv.refl ℝ Glennie.Octonion
  B := LinearEquiv.refl ℝ Glennie.Octonion
  C := LinearEquiv.refl ℝ Glennie.Octonion
  norm_A _ := rfl
  norm_B _ := rfl
  norm_C _ := rfl
  product := related_identity

private theorem reflect_normalize (a : AlbertSequential.Octonion) (ha : a ≠ 0) :
    ∃ a' : AlbertSequential.Octonion, octNormSq a' = 1 ∧ reflect a = reflect a' := by
  obtain ⟨a', r, hr, hu, h⟩ := octUnit_decomposition (a : Glennie.Octonion) ha
  exact ⟨a', hu, by rw [h, reflect_smul hr.ne']⟩

set_option maxHeartbeats 600000 in
private theorem complete_reflections (l : List AlbertSequential.Octonion)
    (hn : ∀ a ∈ l, a ≠ 0) (hd : isometryDet (l.map reflect).prod = 1) :
    ∃ g : OctRelatedTriple, g.C = (l.map reflect).prod.toLinearEquiv := by
  match l with
  | [] => exact ⟨identityTriple, rfl⟩
  | [a] =>
    have ha : isometryDet (reflect a) = -1 := det_reflect (hn a (by simp))
    norm_num [ha] at hd
  | a :: b :: l =>
    have ha : isometryDet (reflect a) = -1 := det_reflect (hn a (by simp))
    have hb : isometryDet (reflect b) = -1 := det_reflect (hn b (by simp))
    have hd' : isometryDet (l.map reflect).prod = 1 := by
      simpa only [List.map_cons, List.prod_cons, map_mul, ha, hb, neg_one_mul, neg_neg]
        using hd
    obtain ⟨g, hg⟩ := complete_reflections l (fun c hc => hn c (by simp [hc])) hd'
    obtain ⟨a', ha', ea⟩ := reflect_normalize a (hn a (by simp))
    obtain ⟨b', hb', eb⟩ := reflect_normalize b (hn b (by simp))
    let pair := (octMiddleTriple a' ha').comp
      (octMiddleTriple (octConj b') ((octNormSq_conj (b' : Glennie.Octonion)).trans hb'))
    have hp : pair.C = (reflect a * reflect b).toLinearEquiv := by
      apply LinearEquiv.ext
      intro x
      change pair.C x = reflect a (reflect b x)
      rw [ea, eb]
      exact (reflect_pair a' b' ha' hb' _).symm
    refine ⟨pair.comp g, ?_⟩
    change g.C.trans pair.C = _
    rw [hg, hp]
    simp only [List.map_cons, List.prod_cons]
    rfl

/-- Every proper orthogonal map occurs in the output slot of a related triple.
This is the existence assertion in Yokota, Theorem 1.14.2. -/
theorem exists_related_output (g : OctEquiv) (hg : OctOrtho g)
    (hd : LinearMap.det g.toLinearMap = 1) : ∃ T : OctRelatedTriple, T.C = g := by
  obtain ⟨l, hn, hl⟩ := reflections_nonzero (toOctIsometry g hg)
  change isometryDet (toOctIsometry g hg) = 1 at hd
  rw [hl] at hd
  obtain ⟨T, hT⟩ := complete_reflections l hn hd
  exact ⟨T, hT.trans (congrArg LinearIsometryEquiv.toLinearEquiv hl.symm)⟩

/-- Octonion conjugation has determinant minus one in the real eight-dimensional carrier. -/
theorem octConjEquiv_det :
    LinearMap.det octConjEquiv.toLinearMap = -1 := by
  let u : AlbertSequential.Octonion := octScalar 1
  have hu : octNormSq (u : Glennie.Octonion) = 1 := by
    norm_num [u, octNormSq, octScalar, Quaternion.normSq_def']
  have hu0 : u ≠ 0 := by
    intro h
    have h' : (1 : ℝ) = 0 := congrArg (fun x : AlbertSequential.Octonion => x.1.re) h
    exact one_ne_zero h'
  have heq : (ℝ ∙ u).reflection.toLinearEquiv = octConjEquiv := by
    apply LinearEquiv.ext
    intro x
    change (ℝ ∙ u).reflection x = octConj x
    have hr := reflect_unit u hu x
    rw [reflect, Submodule.reflection_orthogonal_apply] at hr
    simpa only [u, octMul_scalar_left, octMul_scalar_right, one_smul, neg_inj] using hr
  let : Fact (Module.finrank ℝ AlbertSequential.Octonion = 7 + 1) :=
    ⟨AlbertSequential.oct_finrank⟩
  have h : LinearMap.det (ℝ ∙ u).reflection.toLinearMap = -1 := by
    rw [Submodule.det_reflection, Submodule.finrank_orthogonal_span_singleton (n := 7) hu0]
    norm_num
  exact (congrArg (fun e : OctEquiv => LinearMap.det e.toLinearMap) heq).symm.trans h

private theorem related_output_det (g : OctRelatedTriple) :
    LinearMap.det g.C.toLinearMap = 1 := by
  rcases det_ortho g.C g.norm_C with h | h
  · exact h
  let f := g.C.symm.trans octConjEquiv
  have hf : OctOrtho f := by
    intro x
    change octNormSq (octConj (g.C.symm x)) = octNormSq x
    rw [octNormSq_conj, ← g.norm_C (g.C.symm x), g.C.apply_symm_apply]
  have hcomp : g.C.trans f = octConjEquiv := by
    apply LinearEquiv.ext
    intro x
    change octConj (g.C.symm (g.C x)) = octConj x
    rw [g.C.symm_apply_apply]
  have hdet := congrArg (fun e : OctEquiv => LinearMap.det e.toLinearMap) hcomp
  change LinearMap.det (f.toLinearMap.comp g.C.toLinearMap) = _ at hdet
  rw [LinearMap.det_comp, h, octConjEquiv_det] at hdet
  have hdet' : LinearMap.det f.toLinearMap = 1 := by linarith
  obtain ⟨T, hT⟩ := exists_related_output f hf hdet'
  have hc : (T.comp g).C = octConjEquiv := by
    change g.C.trans T.C = octConjEquiv
    rwa [hT]
  exfalso
  apply no_related_first_conj (cyclicRelated (T.comp g))
  change octConjMap (T.comp g).C = octConjEquiv
  rw [hc]
  apply LinearEquiv.ext
  intro x
  exact octConj_conj (octConj x)

/-- An orthogonal related triple consists of three proper orthogonal maps. -/
theorem related_det_one (g₁ g₂ g₃ : OctEquiv) (h₁ : OctOrtho g₁)
    (h₂ : OctOrtho g₂) (h₃ : OctOrtho g₃) (h : Related g₁ g₂ g₃) :
    LinearMap.det g₁.toLinearMap = 1 ∧ LinearMap.det g₂.toLinearMap = 1 ∧
      LinearMap.det g₃.toLinearMap = 1 := by
  let g : OctRelatedTriple := ⟨g₁, g₂, g₃, h₁, h₂, h₃, h⟩
  have hA := related_output_det (cyclicRelated (cyclicRelated g))
  have hB := related_output_det (cyclicRelated g)
  change LinearMap.det (octConjMap g₁).toLinearMap = 1 at hA
  change LinearMap.det (octConjMap g₂).toLinearMap = 1 at hB
  exact ⟨(octConjMap_det g₁).symm.trans hA, (octConjMap_det g₂).symm.trans hB,
    related_output_det g⟩

end
end ThirteenPlanes.AlbertTriality
