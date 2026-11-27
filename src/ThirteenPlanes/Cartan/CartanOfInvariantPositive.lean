module

public import ThirteenPlanes.Cartan.LieOrthogonalDecomposition

@[expose] public section

set_option backward.privateInPublic true

/-! The characterization of Cartans in a real Lie algebra with a positive invariant form. -/

namespace ThirteenPlanes.Cartan

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem skew_nilpotent_eq_zero (B : LinearMap.BilinForm ℝ E)
    (positive : ∀ x : E, x ≠ 0 → 0 < B x x) (f : Module.End ℝ E)
    (skew : ∀ x y, B (f x) y = - B x (f y)) (nilpotent : IsNilpotent f) : f = 0 := by
  have step (x : E) (hx : f (f x) = 0) : f x = 0 := by
    by_contra hn
    have hs := skew x (f x)
    rw [hx, map_zero, neg_zero] at hs
    exact (positive _ hn).ne' hs
  have reduce (n : ℕ) (x : E) (hx : (f ^ (n + 1)) x = 0) : f x = 0 := by
    induction n generalizing x with
    | zero => simpa using hx
    | succ n ih =>
      apply step
      apply ih
      simpa only [pow_succ f (n + 1), Module.End.mul_apply] using hx
  obtain ⟨n, hn⟩ := nilpotent
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply]
  apply reduce n
  rw [pow_succ, hn, zero_mul, LinearMap.zero_apply]

end

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- A positive invariant form suffices for maximal commutative subalgebras to be precisely the
nilpotent self-normalizing Cartans. The restriction of a compact Killing form can be used even
when the subalgebra has a centre. -/
theorem compactCartan_iff_cartan_of_invariant_positive (B : LinearMap.BilinForm ℝ L)
    (positive : ∀ x : L, x ≠ 0 → 0 < B x x)
    (invariant : ∀ x y z, B ⁅x,y⁆ z = B x ⁅y,z⁆)
    (T : LieSubalgebra ℝ L) : IsCompactCartan T ↔ T.IsCartanSubalgebra := by
  constructor
  · intro h
    have : IsLieAbelian T := ⟨fun x y => Subtype.ext (((h x.val).mpr x.property) y.val y.property)⟩
    refine ⟨inferInstance, le_antisymm ?_ T.le_normalizer⟩
    intro x hx
    apply (h x).mp
    intro y hy
    have hxy := (T.mem_normalizer_iff x).mp hx y hy
    have hzero : ⁅y, ⁅x,y⁆⁆ = 0 := ((h y).mpr hy) _ hxy
    by_contra hn
    have hb := invariant x y ⁅x,y⁆
    rw [hzero, map_zero] at hb
    exact (positive _ hn).ne' hb
  · intro h x
    have : T.IsCartanSubalgebra := h
    obtain ⟨n, hn⟩ := LieAlgebra.nilpotent_ad_of_nilpotent_algebra ℝ T
    let S : LinearMap.BilinForm ℝ T := B.compl₁₂ T.toSubmodule.subtype T.toSubmodule.subtype
    have hab (a b : T) : ⁅a,b⁆ = 0 := by
      let f := LieAlgebra.ad ℝ T a
      have hs (u v : T) : S (f u) v = - S u (f v) := by
        change B ⁅a.val,u.val⁆ v.val = -B u.val ⁅a.val,v.val⁆
        rw [← lie_skew a.val u.val, map_neg, LinearMap.neg_apply, invariant]
      have hp (v : T) (hv : v ≠ 0) : 0 < S v v :=
        positive v.val (fun he => hv (Subtype.ext he))
      have hf : f = 0 := skew_nilpotent_eq_zero S hp f hs ⟨n, hn a⟩
      exact LinearMap.congr_fun hf b
    constructor
    · intro hx
      have he := (T.mem_normalizer_iff x).mpr fun y hy => hx y hy ▸ T.zero_mem
      simpa only [h.self_normalizing] using he
    · intro hx y hy
      exact congrArg Subtype.val (hab ⟨x,hx⟩ ⟨y,hy⟩)

end ThirteenPlanes.Cartan
