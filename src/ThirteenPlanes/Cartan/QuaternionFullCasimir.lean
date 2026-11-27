module

public import ThirteenPlanes.Cartan.QuaternionRepresentation

@[expose] public section

set_option backward.privateInPublic true

/-! The trace-normalized Casimir of the full compact quaternionic algebra. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB

noncomputable section

private abbrev V := quaternionJordan.traceFree
private abbrev K := quaternionDerivationOperators

private theorem quaternion_casimir_commutes (U : QBasis) (x : V) :
    let g := (quaternionJordanAction U).traceAction quaternionJordan
    operatorCasimir K (g x) = g (operatorCasimir K x) := by
  let g := (quaternionJordanAction U).traceAction quaternionJordan
  have e := operatorCasimir_conjugate g K
  have hK : K.map (conjugateSkew g).toLinearMap = K :=
    quaternionDerivationOperators_normalizes U
  rw [hK] at e
  have h := LinearMap.congr_fun e (g x)
  change operatorCasimir K (g x) = g (operatorCasimir K (g.symm (g x))) at h
  simpa only [g.symm_apply_apply] using h

private theorem quaternion_casimir_scalar : ∃ a : ℝ, operatorCasimir K = a • LinearMap.id :=
  quaternionJordan_commuting_eq_smul_id (operatorCasimir K) quaternion_casimir_commutes

/-- The full quaternionic Casimir has the trace-normalized dimension ratio. -/
theorem quaternionFullCasimir :
    operatorCasimir quaternionDerivationOperators =
      (Module.finrank ℝ quaternionDerivationOperators / (14 : ℝ)) • LinearMap.id := by
  change operatorCasimir K = (Module.finrank ℝ K / (14 : ℝ)) • LinearMap.id
  obtain ⟨a, ha⟩ := quaternion_casimir_scalar
  let tr : Module.End ℝ V →ₗ[ℝ] ℝ := LinearMap.trace ℝ V
  let I : Module.End ℝ V := LinearMap.id
  have ht : tr (operatorCasimir K) = Module.finrank ℝ K := trace_operatorCasimir K
  have hid : tr I = (14 : ℝ) := by
    have h := LinearMap.trace_id (R := ℝ) (M := V)
    simpa only [quaternionTraceFree_finrank, Nat.cast_ofNat] using h
  have hs : tr (operatorCasimir K) = a * (14 : ℝ) := by
    calc
      _ = tr (a • I) := congrArg tr ha
      _ = a • tr I := tr.map_smul a I
      _ = _ := congrArg (fun r : ℝ => a * r) hid
  have hratio : a = (Module.finrank ℝ K / (14 : ℝ)) :=
    (eq_div_iff (by norm_num)).mpr (hs.symm.trans ht)
  exact ha.trans (congrArg (fun b : ℝ => b • I) hratio)

end

end ThirteenPlanes.Cartan
