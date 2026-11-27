module

public import ThirteenPlanes.Potential.Coords
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! The dimension of the space of fully symmetric `n × n × n` arrays.

Symmetric arrays are the functions on 3-element multisets of `Fin n`, so their dimension is
`(n+2).choose 3 = n(n+1)(n+2)/6`. -/

open BigOperators

namespace ThirteenPlanes

noncomputable section

namespace SymArrays

variable {α : Type*}

theorem multiset_pair_eq {b d j k : α} (h : b ::ₘ d ::ₘ 0 = j ::ₘ k ::ₘ 0) :
    (b = j ∧ d = k) ∨ (b = k ∧ d = j) := by
  have hb : b ∈ j ::ₘ k ::ₘ 0 := h ▸ Multiset.mem_cons_self b _
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hb
  rcases hb with rfl | rfl
  · have h2 := (Multiset.cons_inj_right b).mp h
    rw [Multiset.cons_zero, Multiset.cons_zero, Multiset.singleton_inj] at h2
    exact Or.inl ⟨rfl, h2⟩
  · rw [Multiset.cons_swap j b] at h
    have h2 := (Multiset.cons_inj_right b).mp h
    rw [Multiset.cons_zero, Multiset.cons_zero, Multiset.singleton_inj] at h2
    exact Or.inr ⟨rfl, h2⟩

theorem symm_of_multiset_eq {c : α → α → α → ℝ} (hc : Coords.Symm c) {a b d i j k : α}
    (h : a ::ₘ b ::ₘ d ::ₘ 0 = i ::ₘ j ::ₘ k ::ₘ 0) : c a b d = c i j k := by
  have ha : a ∈ i ::ₘ j ::ₘ k ::ₘ 0 := h ▸ Multiset.mem_cons_self a _
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · rcases multiset_pair_eq ((Multiset.cons_inj_right a).mp h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hc.s23 a b d
  · rw [Multiset.cons_swap i a] at h
    rcases multiset_pair_eq ((Multiset.cons_inj_right a).mp h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hc.s12 a b d
    · rw [hc.s23 a b d, hc.s12 a d b]
  · rw [Multiset.cons_swap j a, Multiset.cons_swap i a] at h
    rcases multiset_pair_eq ((Multiset.cons_inj_right a).mp h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hc.s12 a b d, hc.s23 b a d]
    · rw [hc.s13 a b d]

theorem sym_three_eq_cons (s : Sym α 3) : ∃ i j k : α, s = i ::ₛ j ::ₛ k ::ₛ Sym.nil := by
  obtain ⟨x, y, z, h⟩ := Multiset.card_eq_three.mp s.2
  refine ⟨x, y, z, Subtype.ext ?_⟩
  rw [h]; simp [Sym.cons, Sym.nil, Multiset.insert_eq_cons]

theorem val_cons3 (i j k : α) :
    ((i ::ₛ j ::ₛ k ::ₛ Sym.nil : Sym α 3) : Multiset α) = i ::ₘ j ::ₘ k ::ₘ 0 := by
  simp [Sym.cons, Sym.nil]

end SymArrays

open SymArrays

variable (n : ℕ)

/-- The fully symmetric real arrays indexed by `Fin n`. -/
def symArrays : Submodule ℝ (Fin n → Fin n → Fin n → ℝ) where
  carrier := {c | Coords.Symm c}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  add_mem' := fun {c d} hc hd => ⟨fun i j k => by simp [hc.s12 i j k, hd.s12 i j k],
    fun i j k => by simp [hc.s23 i j k, hd.s23 i j k]⟩
  smul_mem' := fun a c hc => ⟨fun i j k => by simp [hc.s12 i j k],
    fun i j k => by simp [hc.s23 i j k]⟩

/-- Symmetric arrays from functions on 3-element multisets. -/
def ofSymFun : (Sym (Fin n) 3 → ℝ) →ₗ[ℝ] symArrays n where
  toFun f := ⟨fun i j k => f (i ::ₛ j ::ₛ k ::ₛ Sym.nil),
    ⟨fun i j k => by rw [Sym.cons_swap], fun i j k => by rw [Sym.cons_swap j k]⟩⟩
  map_add' f g := rfl
  map_smul' a f := rfl

theorem ofSymFun_bijective : Function.Bijective (ofSymFun n) := by
  constructor
  · intro f g h
    funext s
    obtain ⟨i, j, k, rfl⟩ := sym_three_eq_cons s
    exact congrFun (congrFun (congrFun (congrArg Subtype.val h) i) j) k
  · rintro ⟨c, hc⟩
    refine ⟨fun s => c (sym_three_eq_cons s).choose (sym_three_eq_cons s).choose_spec.choose
      (sym_three_eq_cons s).choose_spec.choose_spec.choose, Subtype.ext ?_⟩
    funext i j k
    change c _ _ _ = c i j k
    apply symm_of_multiset_eq hc
    have := (sym_three_eq_cons (i ::ₛ j ::ₛ k ::ₛ Sym.nil : Sym (Fin n) 3)).choose_spec.choose_spec.choose_spec
    have := congrArg (fun s : Sym (Fin n) 3 => (s : Multiset (Fin n))) this
    simp only [Sym.coe_cons, Sym.coe_nil] at this
    exact this.symm

/-- **Dimension of symmetric arrays:** `(n+2).choose 3`. -/
theorem finrank_symArrays : Module.finrank ℝ (symArrays n) = (n + 2).choose 3 := by
  rw [← (LinearEquiv.ofBijective _ (ofSymFun_bijective n)).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    show n + 3 - 1 = n + 2 by omega]

theorem six_mul_choose_three : 6 * (n + 2).choose 3 = n * (n + 1) * (n + 2) := by
  have h1 : (n + 2) * (n + 1).choose 2 = (n + 2).choose 3 * 3 := Nat.add_one_mul_choose_eq (n + 1) 2
  have h2 : (n + 1) * n = (n + 1).choose 2 * 2 := by
    have := Nat.add_one_mul_choose_eq n 1
    rwa [Nat.choose_one_right] at this
  calc 6 * (n + 2).choose 3 = 2 * ((n + 2).choose 3 * 3) := by ring
    _ = 2 * ((n + 2) * (n + 1).choose 2) := by rw [h1]
    _ = (n + 2) * ((n + 1).choose 2 * 2) := by ring
    _ = (n + 2) * ((n + 1) * n) := by rw [h2]
    _ = n * (n + 1) * (n + 2) := by ring

theorem two_mul_choose_two : 2 * n.choose 2 = n * (n - 1) := by
  rcases n with _ | m
  · simp
  · have h := Nat.add_one_mul_choose_eq m 1
    rw [Nat.choose_one_right] at h
    rw [Nat.add_sub_cancel, mul_comm 2, ← h]

end

end ThirteenPlanes
