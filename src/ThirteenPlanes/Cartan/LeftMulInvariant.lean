module

public import ThirteenPlanes.Cartan.JordanAction

@[expose] public section

/-! Invariant multiplication-operator trace pairing on a traceless Jordan representation. -/

namespace ThirteenPlanes.Cartan

open scoped RealInnerProductSpace

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]

/-- The trace of the composed left multiplications is scalar on any scalar-commutant model. -/
theorem leftMul_trace_eq_inner (M : TraceJordanData J) {G : Type*}
    (act : G → M.Automorphism)
    (commutant : ∀ S : Module.End ℝ M.traceFree,
      (∀ g x, S ((act g).traceAction M x) = (act g).traceAction M (S x)) →
        ∃ a : ℝ, S = a • LinearMap.id) :
    ∃ a : ℝ, ∀ x y : M.traceFree,
      LinearMap.trace ℝ J (M.L x.val * M.L y.val) = a * ⟪x, y⟫ := by
  let B : M.traceFree →ₗ[ℝ] M.traceFree →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun x y => LinearMap.trace ℝ J (M.L x.val * M.L y.val))
    (fun x y z => by simp [add_mul])
    (fun r x y => by simp)
    (fun x y z => by simp [mul_add])
    (fun r x y => by simp)
  let S : Module.End ℝ M.traceFree := SymmetricCubic.riesz.comp B
  have hS (x y : M.traceFree) :
      ⟪S x, y⟫ = LinearMap.trace ℝ J (M.L x.val * M.L y.val) :=
    SymmetricCubic.inner_riesz (B x) y
  have hComm (g : G) (x : M.traceFree) :
      S ((act g).traceAction M x) = (act g).traceAction M (S x) := by
    apply ext_inner_right ℝ
    intro y
    obtain ⟨y, rfl⟩ := ((act g).traceAction M).surjective y
    rw [((act g).traceAction M).inner_map_map, hS, hS]
    change LinearMap.trace ℝ J (M.L ((act g).action x.val) * M.L ((act g).action y.val)) = _
    rw [(act g).leftMul_conjugate M, (act g).leftMul_conjugate M,
      ← conj_mul, LinearMap.trace_conj']
  obtain ⟨a, ha⟩ := commutant S hComm
  refine ⟨a, fun x y => ?_⟩
  rw [← hS, ha, LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_left]

end

end ThirteenPlanes.Cartan
