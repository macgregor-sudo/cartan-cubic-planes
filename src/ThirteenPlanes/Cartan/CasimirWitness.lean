module

public import ThirteenPlanes.Cartan.Casimir
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

set_option backward.privateInPublic true

/-! Two independent rotations witness all hypotheses of the Casimir lemma. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace

noncomputable section

private abbrev W := WithLp 2 (ℂ × ℂ)

private def blockMap (f g : Module.End ℝ ℂ) : Module.End ℝ W :=
  (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm.toLinearMap.comp
    ((f.prodMap g).comp (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).toLinearMap)

@[simp] private theorem blockMap_apply (f g : Module.End ℝ ℂ) (x : W) :
    blockMap f g x = WithLp.toLp 2 (f x.fst, g x.snd) := rfl

private def rot : Module.End ℝ ℂ := LinearMap.mulLeft ℝ Complex.I

@[simp] private theorem rot_apply (z : ℂ) : rot z = Complex.I * z := rfl

private theorem rot_skew (x y : ℂ) : ⟪rot x, y⟫ = -⟪x, rot y⟫ := by
  simp only [rot_apply, Complex.inner, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

private def leftRot : SkewOperator W :=
  ⟨blockMap rot 0, by
    intro x y
    simpa only [WithLp.prod_inner_apply, blockMap_apply, LinearMap.zero_apply,
      WithLp.ofLp_toLp, WithLp.fst, inner_zero_left, inner_zero_right, add_zero] using rot_skew x.fst y.fst⟩

private def rightRot : SkewOperator W :=
  ⟨blockMap 0 rot, by
    intro x y
    simpa only [WithLp.prod_inner_apply, blockMap_apply, LinearMap.zero_apply,
      WithLp.ofLp_toLp, WithLp.snd, inner_zero_left, inner_zero_right, zero_add] using rot_skew x.snd y.snd⟩

private def leftProj : Module.End ℝ W := blockMap LinearMap.id 0
private def rightProj : Module.End ℝ W := blockMap 0 LinearMap.id

private theorem leftRot_sq : leftRot.val * leftRot.val = -leftProj := by
  apply LinearMap.ext
  intro x
  apply (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).injective
  apply Prod.ext
  · change Complex.I * (Complex.I * x.fst) = -x.fst
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  · change (0 : ℂ) = -(0 : ℂ)
    exact neg_zero.symm

private theorem rightRot_sq : rightRot.val * rightRot.val = -rightProj := by
  apply LinearMap.ext
  intro x
  apply (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).injective
  apply Prod.ext
  · change (0 : ℂ) = -(0 : ℂ)
    exact neg_zero.symm
  · change Complex.I * (Complex.I * x.snd) = -x.snd
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

private theorem leftRot_rightRot : leftRot.val * rightRot.val = 0 := by
  apply LinearMap.ext
  intro x
  apply (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).injective
  change (Complex.I * 0, (0 : ℂ)) = (0, 0)
  rw [mul_zero]

private theorem block_projs_sum : leftProj + rightProj = (LinearMap.id : Module.End ℝ W) := by
  apply LinearMap.ext
  intro x
  apply (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).injective
  change (x.fst + 0, (0 : ℂ) + x.snd) = (x.fst, x.snd)
  simp

private theorem block_trace : LinearMap.trace ℝ W leftProj = 2 ∧
    LinearMap.trace ℝ W rightProj = 2 := by
  let b := Complex.orthonormalBasisOneI
  let B := b.prod b
  have hL (i : Fin 2) : leftProj (B (.inl i)) = B (.inl i) := by
    simp [B, leftProj, OrthonormalBasis.prod_apply]
  have hR (i : Fin 2) : leftProj (B (.inr i)) = 0 := by
    simp [B, leftProj, OrthonormalBasis.prod_apply]
  have hL' (i : Fin 2) : rightProj (B (.inl i)) = 0 := by
    simp [B, rightProj, OrthonormalBasis.prod_apply]
  have hR' (i : Fin 2) : rightProj (B (.inr i)) = B (.inr i) := by
    simp [B, rightProj, OrthonormalBasis.prod_apply]
  constructor
  · rw [SymmetricCubic.trace_eq_sum_inner B, Fintype.sum_sum_type]
    simp [hL, hR, B.orthonormal.norm_eq_one]
  · rw [SymmetricCubic.trace_eq_sum_inner B, Fintype.sum_sum_type]
    simp [hL', hR', B.orthonormal.norm_eq_one]

private def s : ℝ := (Real.sqrt 2)⁻¹

private theorem s_sq : s * s = 1 / 2 := by
  unfold s
  rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num)]
  rw [one_div]

private def rotations : Fin 2 → SkewOperator W :=
  ![s • leftRot, s • rightRot]

private theorem rotations_orthonormal : Orthonormal ℝ rotations := by
  have hL : ⟪leftRot, leftRot⟫ = 2 := by rw [skewOperator_inner, leftRot_sq, map_neg, neg_neg, block_trace.1]
  have hR : ⟪rightRot, rightRot⟫ = 2 := by rw [skewOperator_inner, rightRot_sq, map_neg, neg_neg, block_trace.2]
  have hLR : ⟪leftRot, rightRot⟫ = 0 := by rw [skewOperator_inner, leftRot_rightRot, map_zero, neg_zero]
  have hs (x y : SkewOperator W) : ⟪s • x, s • y⟫ = (1 / 2 : ℝ) * ⟪x, y⟫ := by
    calc
      _ = s * ⟪x, s • y⟫ := real_inner_smul_left (F := SkewOperator W) x (s • y) s
      _ = s * (s * ⟪x, y⟫) := congrArg (s * ·) (real_inner_smul_right (F := SkewOperator W) x y s)
      _ = _ := by rw [← mul_assoc, s_sq]
  apply orthonormal_iff_ite.mpr
  intro i j
  fin_cases i <;> fin_cases j
  · change ⟪s • leftRot, s • leftRot⟫ = 1
    rw [hs, hL]
    norm_num
  · change ⟪s • leftRot, s • rightRot⟫ = 0
    rw [hs, hLR, mul_zero]
  · change ⟪s • rightRot, s • leftRot⟫ = 0
    rw [hs, real_inner_comm (F := SkewOperator W) leftRot rightRot, hLR, mul_zero]
  · change ⟪s • rightRot, s • rightRot⟫ = 1
    rw [hs, hR]
    norm_num

private def K : Submodule ℝ (SkewOperator W) := Submodule.span ℝ (Set.range rotations)

private def basisRot (i : Fin 2) : K :=
  ⟨rotations i, Submodule.subset_span ⟨i, rfl⟩⟩

private def T (i : Fin 2) : Submodule ℝ K := ℝ ∙ basisRot i

private theorem T_map (i : Fin 2) :
    (T i).map K.subtype = ℝ ∙ rotations i := by
  rw [T, Submodule.map_span, Set.image_singleton]
  rfl

private theorem spanLines_orthogonalSplit {ι V : Type*} [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (u : ι → V) (hu : Orthonormal ℝ u) :
    let S := Submodule.span ℝ (Set.range u)
    OrthogonalSplit (E := ↥S) (fun i => ℝ ∙ (⟨u i, Submodule.subset_span ⟨i, rfl⟩⟩ : S)) := by
  let S := Submodule.span ℝ (Set.range u)
  let v (i : ι) : S := ⟨u i, Submodule.subset_span ⟨i, rfl⟩⟩
  let lines (i : ι) : Submodule ℝ S := ℝ ∙ v i
  change OrthogonalSplit (E := ↥S) lines
  have hpair : Pairwise fun i j => (lines i).IsOrtho (lines j) := by
    intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    calc
      _ = a * ⟪v i, b • v j⟫ := real_inner_smul_left (v i) (b • v j) a
      _ = a * (b * ⟪v i, v j⟫) := congrArg (a * ·) (real_inner_smul_right (v i) (v j) b)
      _ = 0 := by
        change a * (b * ⟪u i, u j⟫) = 0
        rw [hu.2 hij, mul_zero, mul_zero]
  refine ⟨hpair, (OrthogonalFamily.of_pairwise hpair).isInternal_iff.mpr ?_⟩
  suffices ht : (⨆ i, lines i) = ⊤ by rw [ht, Submodule.top_orthogonal_eq_bot]
  apply eq_top_iff.mpr
  intro x _
  have hm (i : ι) : (lines i).map S.subtype = ℝ ∙ u i := by
    change (ℝ ∙ v i).map S.subtype = _
    rw [Submodule.map_span, Set.image_singleton]
    rfl
  have he : (⨆ i, lines i).map S.subtype = S := by
    rw [Submodule.map_iSup]
    simp only [hm]
    exact Submodule.span_range_eq_iSup.symm
  have hx : x.val ∈ (⨆ i, lines i).map S.subtype := he.symm ▸ x.property
  obtain ⟨y, hy, ey⟩ := hx
  exact (Subtype.ext ey : y = x) ▸ hy

private theorem splitRotations : OrthogonalSplit (E := ↥K) T :=
  spanLines_orthogonalSplit rotations rotations_orthonormal

private theorem lineCasimir (A : SkewOperator W) (hA : ‖A‖ = 1) :
    operatorCasimir (ℝ ∙ A) = -(A.val * A.val) := by
  let a : (ℝ ∙ A : Submodule ℝ _) := ⟨A, Submodule.mem_span_singleton_self A⟩
  have hdim : Module.finrank ℝ (ℝ ∙ A : Submodule ℝ _) =
      1 := finrank_span_singleton (by intro h; rw [h, norm_zero] at hA; norm_num at hA)
  have ha : ‖a‖ = 1 := hA
  let b : OrthonormalBasis Unit ℝ (ℝ ∙ A : Submodule ℝ (SkewOperator W)) :=
    FiniteDimensional.orthonormalBasisSingleton Unit ℝ hdim a ha
  rw [operatorCasimir_eq_sum _ b, Fintype.sum_unique]
  simp [b, a]

private theorem fixedLine_eq_ker (A : SkewOperator W) :
    fixedSpace (ℝ ∙ A) = LinearMap.ker A.val := by
  ext x
  rw [mem_fixedSpace, LinearMap.mem_ker]
  constructor
  · intro h
    exact h ⟨A, Submodule.mem_span_singleton_self A⟩
  · intro h B
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp B.property
    have he : B.val = r • A := hr.symm
    change B.val.val x = 0
    rw [he]
    change r • A.val x = 0
    rw [h, smul_zero]

private theorem s_ne : s ≠ 0 := by
  intro h
  have he := s_sq
  rw [h, zero_mul] at he
  norm_num at he

private theorem fixed_first_iff (x : W) :
    x ∈ fixedSpace (ℝ ∙ rotations 0) ↔ x.fst = 0 := by
  rw [fixedLine_eq_ker, LinearMap.mem_ker]
  change s • leftRot.val x = 0 ↔ x.fst = 0
  rw [smul_eq_zero, or_iff_right s_ne]
  constructor
  · intro h
    have he : Complex.I * x.fst = 0 := congrArg (fun y : W => y.fst) h
    exact (mul_eq_zero.mp he).resolve_left Complex.I_ne_zero
  · intro h
    change WithLp.toLp 2 (Complex.I * x.fst, (0 : ℂ)) = 0
    rw [h, mul_zero]
    rfl

private theorem fixed_second_iff (x : W) :
    x ∈ fixedSpace (ℝ ∙ rotations 1) ↔ x.snd = 0 := by
  rw [fixedLine_eq_ker, LinearMap.mem_ker]
  change s • rightRot.val x = 0 ↔ x.snd = 0
  rw [smul_eq_zero, or_iff_right s_ne]
  constructor
  · intro h
    have he : Complex.I * x.snd = 0 := congrArg (fun y : W => y.snd) h
    exact (mul_eq_zero.mp he).resolve_left Complex.I_ne_zero
  · intro h
    change WithLp.toLp 2 ((0 : ℂ), Complex.I * x.snd) = 0
    rw [h, mul_zero]
    rfl

private theorem first_projection : projection (fixedSpace (ℝ ∙ rotations 0)) = rightProj := by
  apply LinearMap.ext
  intro x
  change (fixedSpace (ℝ ∙ rotations 0)).starProjection x = rightProj x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (fixed_first_iff _).mpr rfl
  · intro y hy
    have he := (fixed_first_iff y).mp hy
    rw [WithLp.prod_inner_apply]
    change ⟪x.fst - 0, y.fst⟫ + ⟪x.snd - x.snd, y.snd⟫ = 0
    rw [he, inner_zero_right, sub_self, inner_zero_left, add_zero]

private theorem second_projection : projection (fixedSpace (ℝ ∙ rotations 1)) = leftProj := by
  apply LinearMap.ext
  intro x
  change (fixedSpace (ℝ ∙ rotations 1)).starProjection x = leftProj x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (fixed_second_iff _).mpr rfl
  · intro y hy
    have he := (fixed_second_iff y).mp hy
    rw [WithLp.prod_inner_apply]
    change ⟪x.fst - x.fst, y.fst⟫ + ⟪x.snd - 0, y.snd⟫ = 0
    rw [he, inner_zero_right, sub_self, inner_zero_left, add_zero]

private theorem rotation_norm (i : Fin 2) : ‖rotations i‖ = 1 :=
  rotations_orthonormal.norm_eq_one i

private theorem piecesCasimir (i : Fin 2) :
    operatorCasimir ((T i).map K.subtype) =
      (1 / 2 : ℝ) • (LinearMap.id - projection (fixedSpace ((T i).map K.subtype))) := by
  rw [T_map, lineCasimir _ (rotation_norm i)]
  fin_cases i
  · change -((s • leftRot.val) * (s • leftRot.val)) =
        (1 / 2 : ℝ) • (LinearMap.id - projection (fixedSpace (ℝ ∙ rotations 0)))
    rw [first_projection]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, s_sq, leftRot_sq, smul_neg, neg_neg]
    congr 1
    rw [← block_projs_sum, add_sub_cancel_right]
  · change -((s • rightRot.val) * (s • rightRot.val)) =
        (1 / 2 : ℝ) • (LinearMap.id - projection (fixedSpace (ℝ ∙ rotations 1)))
    rw [second_projection]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, s_sq, rightRot_sq, smul_neg, neg_neg]
    congr 1
    rw [← block_projs_sum, add_sub_cancel_left]

private theorem numbers : (∑ i, Module.finrank ℝ (fixedSpace ((T i).map K.subtype))) =
    Module.finrank ℝ W := by
  rw [Fin.sum_univ_two, T_map 0, T_map 1]
  have hs : (∑ i : Fin 2, projection (fixedSpace (ℝ ∙ rotations i))) =
      (LinearMap.id : Module.End ℝ W) := by
    rw [Fin.sum_univ_two, first_projection, second_projection, add_comm, block_projs_sum]
  have ht := congrArg (LinearMap.trace ℝ W) hs
  rw [map_sum, LinearMap.trace_id, Fin.sum_univ_two] at ht
  have hproj (U : Submodule ℝ W) : LinearMap.trace ℝ W (projection U) = Module.finrank ℝ U := by
    have h : LinearMap.IsProj U (projection U) :=
      ⟨U.starProjection_apply_mem, fun x hx => U.starProjection_mem_subspace_eq_self ⟨x, hx⟩⟩
    exact h.trace
  rw [hproj, hproj] at ht
  exact_mod_cast ht

private theorem full : operatorCasimir K = (1 / 2 : ℝ) • LinearMap.id := by
  rw [operatorCasimir_sum K T splitRotations, Fin.sum_univ_two, piecesCasimir, piecesCasimir,
    T_map, T_map, first_projection, second_projection, ← smul_add, ← block_projs_sum]
  congr 1
  abel

/-- Two nonzero skew lines with two nonzero fixed planes realize the Casimir hypotheses. -/
theorem two_rotations_casimir_witness :
    ∃ (K : Submodule ℝ (SkewOperator W)) (T : Fin 2 → Submodule ℝ K),
      (∀ i, ∃ x : T i, x ≠ 0) ∧
      (∀ i, ∃ x : fixedSpace ((T i).map K.subtype), x ≠ 0) ∧
      OrthogonalSplit (E := ↥K) T ∧ operatorCasimir K = (1 / 2 : ℝ) • LinearMap.id ∧
      (∀ i, operatorCasimir ((T i).map K.subtype) =
        (1 / 2 : ℝ) • (LinearMap.id - projection (fixedSpace ((T i).map K.subtype)))) ∧
      (∑ i, Module.finrank ℝ (fixedSpace ((T i).map K.subtype))) = Module.finrank ℝ W ∧
      OrthogonalSplit (fun i => fixedSpace ((T i).map K.subtype)) := by
  refine ⟨K, T, ?_, ?_, splitRotations, full, piecesCasimir, numbers, ?_⟩
  · intro i
    refine ⟨⟨basisRot i, Submodule.mem_span_singleton_self _⟩, ?_⟩
    intro h
    have he : rotations i = 0 :=
      congrArg (fun x : T i => x.val.val) h
    have hn := rotation_norm i
    rw [he, norm_zero] at hn
    norm_num at hn
  · intro i
    fin_cases i
    · refine ⟨⟨WithLp.toLp 2 (0, 1), ?_⟩, ?_⟩
      · change WithLp.toLp 2 (0, 1) ∈ fixedSpace ((T 0).map K.subtype)
        rw [T_map, fixed_first_iff]
        rfl
      · intro h
        have he : (1 : ℂ) = 0 := congrArg (fun x : fixedSpace ((T 0).map K.subtype) => x.val.snd) h
        exact one_ne_zero he
    · refine ⟨⟨WithLp.toLp 2 (1, 0), ?_⟩, ?_⟩
      · change WithLp.toLp 2 (1, 0) ∈ fixedSpace ((T 1).map K.subtype)
        rw [T_map, fixed_second_iff]
        rfl
      · intro h
        have he : (1 : ℂ) = 0 := congrArg (fun x : fixedSpace ((T 1).map K.subtype) => x.val.fst) h
        exact one_ne_zero he
  · exact fixedSpaces_orthSplit_of_casimir K T splitRotations (1 / 2) (1 / 2)
      (by norm_num) full piecesCasimir numbers

end

end ThirteenPlanes.Cartan
