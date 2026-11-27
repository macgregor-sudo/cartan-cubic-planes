module

public import ThirteenPlanes.NativeFramesCarrier
public import Glennie.Diagonalization
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option backward.privateInPublic true

/-! Scalar commutants for the genuine native compact Albert automorphism action. -/

namespace ThirteenPlanes.Cartan

open scoped RealInnerProductSpace

noncomputable section

/-- The native compact automorphism acting on the actual trace-free Hilbert space. -/
def albertTracelessAction (g : Glennie.CompactAutomorphism) : NativeTraceless ≃ₗᵢ[ℝ] NativeTraceless where
  toFun x := ⟨g.equiv x.val, (g.map_trace x.val).trans x.property⟩
  invFun x := ⟨g.symm.equiv x.val, (g.symm.map_trace x.val).trans x.property⟩
  left_inv x := Subtype.ext (g.equiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.equiv.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (g.equiv.map_add x.val y.val)
  map_smul' r x := Subtype.ext (g.equiv.map_smul r x.val)
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖g.equiv x.val‖ ^ 2 = ‖x.val‖ ^ 2
    rw [Glennie.native_norm_sq, Glennie.native_norm_sq, g.inner_map]

@[simp] theorem albertTracelessAction_val (g : Glennie.CompactAutomorphism) (x : NativeTraceless) :
    (albertTracelessAction g x).val = g.equiv x.val := rfl

private def signFirst : Glennie.CompactAutomorphism :=
  Glennie.realRotation12Automorphism (-1) 0 (by norm_num)

private theorem signFirst_coordinates (x : Glennie.Albert) :
    signFirst.equiv x = ⟨x.d0, x.d1, x.d2, -x.o01, -x.o02, x.o12⟩ := by
  change Glennie.realConjugateAlbert _ x = _
  apply Glennie.Albert.ext
  all_goals simp [Glennie.realConjugateAlbert, Glennie.fromMatrix, Glennie.matrixConjugateReal,
    Glennie.matrixRowMix, Glennie.matrixColMix, Glennie.realRotation12, Fin.sum_univ_three,
    Glennie.toMatrix, Glennie.octRe, Glennie.octScalar]

private theorem swap01_coordinates (x : Glennie.Albert) :
    Glennie.realSwap01Automorphism.equiv x =
      ⟨x.d1, x.d0, x.d2, Glennie.octConj x.o01, x.o12, x.o02⟩ :=
  Glennie.realSwap01_coordinates x

private theorem swap02_coordinates (x : Glennie.Albert) :
    Glennie.realSwap02Automorphism.equiv x =
      ⟨x.d2, x.d1, x.d0, Glennie.octConj x.o12, Glennie.octConj x.o02, Glennie.octConj x.o01⟩ :=
  Glennie.realSwap02_coordinates x

private theorem signFirst_fixed_of_diagonal (x : NativeTraceless)
    (hx : Glennie.IsDiagonal x.val) : albertTracelessAction signFirst x = x := by
  apply Subtype.ext
  rw [albertTracelessAction_val, signFirst_coordinates]
  apply Glennie.Albert.ext <;> simp [Glennie.IsDiagonal] at hx <;> simp [hx.1, hx.2.1, hx.2.2]

private theorem oct_zero_of_neg_eq {x : Glennie.Octonion} (h : -x = x) : x = 0 := by
  have h2 : (2 : ℝ) • x = 0 := by
    rw [two_smul]
    calc
      x + x = -x + x := congrArg (fun y => y + x) h.symm
      _ = 0 := neg_add_cancel x
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

private theorem signFirst_fixed_offdiagonal (x : NativeTraceless)
    (hx : albertTracelessAction signFirst x = x) : x.val.o01 = 0 ∧ x.val.o02 = 0 := by
  have h := congrArg Subtype.val hx
  rw [albertTracelessAction_val, signFirst_coordinates] at h
  exact ⟨oct_zero_of_neg_eq (congrArg Glennie.Albert.o01 h),
    oct_zero_of_neg_eq (congrArg Glennie.Albert.o02 h)⟩

private theorem swap01_diagonal (x : NativeTraceless) (hx : Glennie.IsDiagonal x.val) :
    Glennie.IsDiagonal (albertTracelessAction Glennie.realSwap01Automorphism x).val := by
  rw [albertTracelessAction_val, swap01_coordinates]
  refine ⟨?_, hx.2.2, hx.2.1⟩
  change Glennie.octConj x.val.o01 = 0
  rw [hx.1]
  simp [Glennie.octConj]

private theorem commuting_preserves_diagonal (S : Module.End ℝ NativeTraceless)
    (hS : ∀ (g : Glennie.CompactAutomorphism) (x : NativeTraceless),
      S (albertTracelessAction g x) = albertTracelessAction g (S x))
    (x : NativeTraceless) (hx : Glennie.IsDiagonal x.val) : Glennie.IsDiagonal (S x).val := by
  have h0 := hS signFirst x
  rw [signFirst_fixed_of_diagonal x hx] at h0
  have hf := signFirst_fixed_offdiagonal (S x) h0.symm
  let y := albertTracelessAction Glennie.realSwap01Automorphism x
  have hy : Glennie.IsDiagonal y.val := swap01_diagonal x hx
  have h1 := hS signFirst y
  rw [signFirst_fixed_of_diagonal y hy] at h1
  have h2 := (signFirst_fixed_offdiagonal (S y) h1.symm).2
  change (S (albertTracelessAction Glennie.realSwap01Automorphism x)).val.o02 = 0 at h2
  rw [hS, albertTracelessAction_val, swap01_coordinates] at h2
  exact ⟨hf.1, hf.2, h2⟩

private def diagonalDifference : NativeTraceless :=
  ⟨⟨1, -1, 0, 0, 0, 0⟩, by norm_num [Glennie.traceLinear, Glennie.trace]⟩

private theorem swap01_diagonalDifference :
    albertTracelessAction Glennie.realSwap01Automorphism diagonalDifference = -diagonalDifference := by
  apply Subtype.ext
  rw [albertTracelessAction_val, swap01_coordinates, ← neg_one_smul ℝ diagonalDifference]
  change (⟨-1, 1, 0, Glennie.octConj 0, 0, 0⟩ : Glennie.Albert) =
    (-1 : ℝ) • diagonalDifference.val
  apply Glennie.Albert.ext
  · change (-1 : ℝ) = -1 * 1
    ring
  · change (1 : ℝ) = -1 * (-1)
    ring
  · change (0 : ℝ) = -1 * 0
    ring
  · change Glennie.octConj (0 : Glennie.Octonion) = (-1 : ℝ) • 0
    simp [Glennie.octConj]
  · change (0 : Glennie.Octonion) = (-1 : ℝ) • 0
    simp
  · change (0 : Glennie.Octonion) = (-1 : ℝ) • 0
    simp

private theorem swappedDiagonalDifference :
    (albertTracelessAction Glennie.realSwap02Automorphism diagonalDifference).val =
      ⟨0, -1, 1, 0, 0, 0⟩ := by
  rw [albertTracelessAction_val, swap02_coordinates]
  simp [diagonalDifference, Glennie.octConj]

/-- A real operator commuting with every actual native compact Albert automorphism is scalar
on the real trace-free Albert representation. Symmetry is unnecessary here. -/
theorem albert_commuting_eq_smul_id (S : Module.End ℝ NativeTraceless)
    (hS : ∀ (g : Glennie.CompactAutomorphism) (x : NativeTraceless),
      S (albertTracelessAction g x) = albertTracelessAction g (S x)) :
    ∃ a : ℝ, S = a • LinearMap.id := by
  let e := diagonalDifference
  let f := albertTracelessAction Glennie.realSwap02Automorphism e
  let a := (S e).val.d0
  have hd : Glennie.IsDiagonal (S e).val :=
    commuting_preserves_diagonal S hS e ⟨rfl, rfl, rfl⟩
  have he₀ : albertTracelessAction Glennie.realSwap01Automorphism (S e) = -(S e) := by
    rw [← hS, show e = diagonalDifference from rfl, swap01_diagonalDifference, map_neg]
  have he₁ := congrArg Subtype.val he₀
  rw [albertTracelessAction_val, swap01_coordinates] at he₁
  have h1 : (S e).val.d1 = -a := congrArg Glennie.Albert.d0 he₁
  have h2 : (S e).val.d2 = 0 := by
    have hh : (S e).val.d2 = -(S e).val.d2 := congrArg Glennie.Albert.d2 he₁
    linarith
  have he : S e = a • e := by
    apply Subtype.ext
    apply Glennie.Albert.ext
    · change a = a * 1
      ring
    · change (S e).val.d1 = a * (-1)
      rw [h1]
      ring
    · change (S e).val.d2 = a * 0
      simp [h2]
    · change (S e).val.o01 = a • (0 : Glennie.Octonion)
      simp [hd.1]
    · change (S e).val.o02 = a • (0 : Glennie.Octonion)
      simp [hd.2.1]
    · change (S e).val.o12 = a • (0 : Glennie.Octonion)
      simp [hd.2.2]
  have hf : S f = a • f := by
    change S (albertTracelessAction Glennie.realSwap02Automorphism e) = _
    rw [hS, he, map_smul]
  have hdiag (x : NativeTraceless) (hx : Glennie.IsDiagonal x.val) : S x = a • x := by
    have hr : x = x.val.d0 • e + x.val.d2 • f := by
      apply Subtype.ext
      change x.val = x.val.d0 • e.val + x.val.d2 • f.val
      rw [show f.val = ⟨0, -1, 1, 0, 0, 0⟩ from swappedDiagonalDifference]
      have ht : x.val.d0 + x.val.d1 + x.val.d2 = 0 := x.property
      apply Glennie.Albert.ext
      · change x.val.d0 = x.val.d0 * 1 + x.val.d2 * 0
        ring
      · change x.val.d1 = x.val.d0 * (-1) + x.val.d2 * (-1)
        linarith
      · change x.val.d2 = x.val.d0 * 0 + x.val.d2 * 1
        ring
      · change x.val.o01 = x.val.d0 • (0 : Glennie.Octonion) + x.val.d2 • (0 : Glennie.Octonion)
        simp [hx.1]
      · change x.val.o02 = x.val.d0 • (0 : Glennie.Octonion) + x.val.d2 • (0 : Glennie.Octonion)
        simp [hx.2.1]
      · change x.val.o12 = x.val.d0 • (0 : Glennie.Octonion) + x.val.d2 • (0 : Glennie.Octonion)
        simp [hx.2.2]
    calc
      S x = a • (x.val.d0 • e + x.val.d2 • f) := by
        conv_lhs => rw [hr]
        rw [map_add, map_smul, map_smul, he, hf, smul_add, smul_comm x.val.d0 a, smul_comm x.val.d2 a]
      _ = a • x := congrArg (fun x : NativeTraceless => a • x) hr.symm
  refine ⟨a, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨g, hg⟩ := Glennie.native_diagonalization x.val
  apply (albertTracelessAction g).injective
  rw [← hS, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  exact hdiag (albertTracelessAction g x) hg

end

end ThirteenPlanes.Cartan
