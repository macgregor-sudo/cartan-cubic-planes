module

public import Mathlib.Data.Sym.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! The dimension of the space of real skew-symmetric `n × n` arrays is `n.choose 2`. -/

open BigOperators

namespace ThirteenPlanes

noncomputable section

variable (n : ℕ)

/-- The real skew-symmetric arrays indexed by `Fin n`. -/
def skewArrays : Submodule ℝ (Fin n → Fin n → ℝ) where
  carrier := {Ω | ∀ a i, Ω a i = -Ω i a}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun {Ω Θ} hΩ hΘ a i => by simp only [Pi.add_apply, hΩ a i, hΘ a i]; ring
  smul_mem' := fun r Ω hΩ a i => by simp only [Pi.smul_apply, smul_eq_mul, hΩ a i]; ring

/-- Strictly increasing index pairs. -/
abbrev UpperPair := {p : Fin n × Fin n // p.1 < p.2}

theorem card_upperPair : Fintype.card (UpperPair n) = n.choose 2 := by
  classical
  let f : UpperPair n → {z : Sym2 (Fin n) // ¬ z.IsDiag} :=
    fun p => ⟨s(p.1.1, p.1.2), by rw [Sym2.mk_isDiag_iff]; exact p.2.ne⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
      have h' : s(a, b) = s(c, d) := congrArg Subtype.val h
      rcases Sym2.eq_iff.mp h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact absurd (hab.trans hcd) (lt_irrefl _)
    · rintro ⟨z, hz⟩
      induction z using Sym2.ind with
      | _ a b =>
        rw [Sym2.mk_isDiag_iff] at hz
        rcases lt_or_gt_of_ne hz with h | h
        · exact ⟨⟨(a, b), h⟩, rfl⟩
        · exact ⟨⟨(b, a), h⟩, Subtype.ext (Sym2.eq_swap)⟩
  rw [Fintype.card_of_bijective hf, Sym2.card_subtype_not_diag, Fintype.card_fin]

/-- Upper entries of a skew array. -/
def skewUpper : skewArrays n →ₗ[ℝ] (UpperPair n → ℝ) where
  toFun Ω p := (Ω : Fin n → Fin n → ℝ) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem skewUpper_bijective : Function.Bijective (skewUpper n) := by
  constructor
  · rintro ⟨Ω, hΩ⟩ ⟨Θ, hΘ⟩ h
    apply Subtype.ext
    funext a i
    change Ω a i = Θ a i
    have e : ∀ p : UpperPair n, Ω p.1.1 p.1.2 = Θ p.1.1 p.1.2 := fun p => congrFun h p
    rcases lt_trichotomy a i with hai | rfl | hai
    · exact e ⟨(a, i), hai⟩
    · have h1 := hΩ a a; have h2 := hΘ a a; linarith
    · rw [hΩ a i, hΘ a i, e ⟨(i, a), hai⟩]
  · intro f
    refine ⟨⟨fun a i => if h : a < i then f ⟨(a, i), h⟩ else if h' : i < a then -f ⟨(i, a), h'⟩
      else 0, fun a i => ?_⟩, ?_⟩
    · rcases lt_trichotomy a i with hai | rfl | hai
      · simp [hai, not_lt_of_gt hai]
      · simp
      · simp [hai, not_lt_of_gt hai]
    · funext p
      simp [skewUpper, p.2]

/-- **Dimension of skew arrays:** `n.choose 2`. -/
theorem finrank_skewArrays : Module.finrank ℝ (skewArrays n) = n.choose 2 := by
  rw [(LinearEquiv.ofBijective _ (skewUpper_bijective n)).finrank_eq,
    Module.finrank_fintype_fun_eq_card, card_upperPair]

end

end ThirteenPlanes
