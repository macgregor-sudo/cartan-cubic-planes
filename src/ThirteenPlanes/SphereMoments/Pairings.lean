module

public import ThirteenPlanes.SphereMoments.Gaussian

@[expose] public section

set_option backward.privateInPublic true

/-!
# Pairing sums on an orthonormal basis

Finite combinatorics for `wickSum` evaluated on families of orthonormal basis vectors: a recursion
that contracts the first index with each other index, and its consequences for sums weighted by a
symmetric four-index array without trace (`24 ⟨T, S⟩`).
-/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_pi_fin_succ {n : ℕ} (f : (Fin (n + 1) → ι) → ℝ) :
    ∑ i, f i = ∑ a, ∑ j : Fin n → ι, f (Fin.cons a j) := by
  rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_pi_insertNth {n : ℕ} (k : Fin (n + 1)) (f : (Fin (n + 1) → ι) → ℝ) :
    ∑ i, f i = ∑ a, ∑ j : Fin n → ι, f (Fin.insertNth k a j) := by
  rw [← (Fin.insertNthEquiv (fun _ => ι) k).sum_comp, Fintype.sum_prod_type]
  rfl

/-- Contracting the first index of a pairing sum on basis vectors with each other index. -/
theorem sum_mul_wickSum_basis {p : ℕ} (e : OrthonormalBasis ι ℝ V)
    (Φ : (Fin (p + 2) → ι) → ℝ) :
    ∑ i, Φ i * wickSum (p + 2) (fun k => e (i k)) =
      ∑ k : Fin (p + 1), ∑ j : Fin p → ι,
        (∑ t, Φ (Fin.cons t (Fin.insertNth k t j))) * wickSum p (fun m => e (j m)) := by
  simp_rw [wickSum_succ_succ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_pi_fin_succ]
  simp_rw [sum_pi_insertNth k]
  have e1 : ∀ (t s : ι) (j : Fin p → ι),
      Φ (Fin.cons t (Fin.insertNth k s j)) *
        (⟪e ((Fin.cons t (Fin.insertNth k s j) : Fin (p + 2) → ι) 0),
          e ((Fin.cons t (Fin.insertNth k s j) : Fin (p + 2) → ι) k.succ)⟫ *
        wickSum p (Fin.removeNth k (Fin.tail fun m =>
          e ((Fin.cons t (Fin.insertNth k s j) : Fin (p + 2) → ι) m)))) =
      if t = s then Φ (Fin.cons t (Fin.insertNth k t j)) * wickSum p (fun m => e (j m)) else 0 := by
    intro t s j
    have h1 : (Fin.removeNth k (Fin.tail fun m =>
        e ((Fin.cons t (Fin.insertNth k s j) : Fin (p + 2) → ι) m))) = fun m => e (j m) := by
      funext m
      simp [Fin.removeNth, Fin.tail]
    rw [h1]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.insertNth_apply_same, e.inner_eq_ite]
    split_ifs with h
    · subst h; ring
    · ring
  rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun j _ => e1 t s j]
  have e2 : ∀ t : ι, (∑ s : ι, ∑ j : Fin p → ι, if t = s then
      Φ (Fin.cons t (Fin.insertNth k t j)) * wickSum p (fun m => e (j m)) else 0) =
      ∑ j : Fin p → ι, Φ (Fin.cons t (Fin.insertNth k t j)) * wickSum p (fun m => e (j m)) := by
    intro t
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  simp_rw [e2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]

/-- A real four-index array invariant under all permutations of its indices. -/
structure IsSymmetric4 (T : ι → ι → ι → ι → ℝ) : Prop where
  swap₁₂ : ∀ a b c d, T a b c d = T b a c d
  swap₂₃ : ∀ a b c d, T a b c d = T a c b d
  swap₃₄ : ∀ a b c d, T a b c d = T a b d c

/-- A four-index array whose contraction of the first two indices vanishes. -/
def IsTraceFree4 (T : ι → ι → ι → ι → ℝ) : Prop := ∀ c d, ∑ t, T t t c d = 0

variable (e : OrthonormalBasis ι ℝ V)

theorem sum_mul_wickSum_basis_two (F : (Fin 2 → ι) → ℝ) :
    ∑ i, F i * wickSum 2 (fun k => e (i k)) = ∑ t, F ![t, t] := by
  rw [sum_mul_wickSum_basis]
  simp only [wickSum_zero, mul_one, Finset.univ_unique, Finset.sum_singleton]
  rw [Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun t _ => congrArg F ?_
  funext k; fin_cases k <;> rfl

/-- Pairing sum on basis vectors against an arbitrary four-index array. -/
theorem sum_mul_wickSum_basis_four (F : (Fin 4 → ι) → ℝ) :
    ∑ i, F i * wickSum 4 (fun k => e (i k)) =
      ∑ w, ∑ t, (F ![t, t, w, w] + F ![t, w, t, w] + F ![t, w, w, t]) := by
  rw [sum_mul_wickSum_basis, Fin.sum_univ_three]
  simp only [sum_mul_wickSum_basis_two, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun t _ => ?_
  congr 2 <;> (congr 1; funext k; fin_cases k <;> rfl)

section Stages

variable {T S : ι → ι → ι → ι → ℝ}

private theorem trace₁₃ (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T) (a b : ι) :
    ∑ t, T t a t b = 0 := by
  rw [← hT0 a b]; exact Finset.sum_congr rfl fun t _ => hT.swap₂₃ _ _ _ _

private theorem trace₁₄ (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T) (a b : ι) :
    ∑ t, T t a b t = 0 := by
  rw [← trace₁₃ hT hT0 a b]; exact Finset.sum_congr rfl fun t _ => hT.swap₃₄ _ _ _ _

private theorem trace₂₃ (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T) (a b : ι) :
    ∑ t, T a t t b = 0 := by
  rw [← trace₁₃ hT hT0 a b]; exact Finset.sum_congr rfl fun t _ => hT.swap₁₂ _ _ _ _

private theorem trace₂₄ (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T) (a b : ι) :
    ∑ t, T a t b t = 0 := by
  rw [← trace₂₃ hT hT0 a b]; exact Finset.sum_congr rfl fun t _ => hT.swap₃₄ _ _ _ _

private theorem trace₃₄ (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T) (a b : ι) :
    ∑ t, T a b t t = 0 := by
  rw [← trace₂₄ hT hT0 a b]; exact Finset.sum_congr rfl fun t _ => hT.swap₂₃ _ _ _ _

private theorem stage8 (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T) (hS : IsSymmetric4 S) :
    ∑ i : Fin 8 → ι, T (i 0) (i 1) (i 2) (i 3) * S (i 4) (i 5) (i 6) (i 7) *
        wickSum 8 (fun k => e (i k)) =
      4 * ∑ j : Fin 6 → ι, (∑ t, T t (j 0) (j 1) (j 2) * S t (j 3) (j 4) (j 5)) *
        wickSum 6 (fun k => e (j k)) := by
  rw [sum_mul_wickSum_basis (p := 6), Fin.sum_univ_seven]
  show ∑ j : Fin 6 → ι, (∑ t, T t t (j 0) (j 1) * S (j 2) (j 3) (j 4) (j 5)) *
        wickSum 6 (fun k => e (j k)) +
      ∑ j : Fin 6 → ι, (∑ t, T t (j 0) t (j 1) * S (j 2) (j 3) (j 4) (j 5)) *
        wickSum 6 (fun k => e (j k)) +
      ∑ j : Fin 6 → ι, (∑ t, T t (j 0) (j 1) t * S (j 2) (j 3) (j 4) (j 5)) *
        wickSum 6 (fun k => e (j k)) +
      ∑ j : Fin 6 → ι, (∑ t, T t (j 0) (j 1) (j 2) * S t (j 3) (j 4) (j 5)) *
        wickSum 6 (fun k => e (j k)) +
      ∑ j : Fin 6 → ι, (∑ t, T t (j 0) (j 1) (j 2) * S (j 3) t (j 4) (j 5)) *
        wickSum 6 (fun k => e (j k)) +
      ∑ j : Fin 6 → ι, (∑ t, T t (j 0) (j 1) (j 2) * S (j 3) (j 4) t (j 5)) *
        wickSum 6 (fun k => e (j k)) +
      ∑ j : Fin 6 → ι, (∑ t, T t (j 0) (j 1) (j 2) * S (j 3) (j 4) (j 5) t) *
        wickSum 6 (fun k => e (j k)) = _
  have z0 : ∀ a b c d f g : ι, ∑ t, T t t a b * S c d f g = 0 := fun a b c d f g => by
    rw [← Finset.sum_mul, hT0, zero_mul]
  have z1 : ∀ a b c d f g : ι, ∑ t, T t a t b * S c d f g = 0 := fun a b c d f g => by
    rw [← Finset.sum_mul, trace₁₃ hT hT0, zero_mul]
  have z2 : ∀ a b c d f g : ι, ∑ t, T t a b t * S c d f g = 0 := fun a b c d f g => by
    rw [← Finset.sum_mul, trace₁₄ hT hT0, zero_mul]
  have s1 : ∀ a b c d f g : ι, ∑ t, T t a b c * S d t f g = ∑ t, T t a b c * S t d f g :=
    fun _ _ _ _ _ _ => Finset.sum_congr rfl fun t _ => by rw [hS.swap₁₂]
  have s2 : ∀ a b c d f g : ι, ∑ t, T t a b c * S d f t g = ∑ t, T t a b c * S t d f g :=
    fun _ _ _ _ _ _ => Finset.sum_congr rfl fun t _ => by rw [hS.swap₂₃, hS.swap₁₂]
  have s3 : ∀ a b c d f g : ι, ∑ t, T t a b c * S d f g t = ∑ t, T t a b c * S t d f g :=
    fun _ _ _ _ _ _ => Finset.sum_congr rfl fun t _ => by rw [hS.swap₃₄, hS.swap₂₃, hS.swap₁₂]
  simp only [z0, z1, z2, s1, s2, s3, zero_mul, Finset.sum_const_zero, zero_add]
  ring

private theorem stage6 (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T) (hS : IsSymmetric4 S) :
    ∑ j : Fin 6 → ι, (∑ t, T t (j 0) (j 1) (j 2) * S t (j 3) (j 4) (j 5)) *
        wickSum 6 (fun k => e (j k)) =
      3 * ∑ j : Fin 4 → ι, (∑ u, ∑ t, T t u (j 0) (j 1) * S t u (j 2) (j 3)) *
        wickSum 4 (fun k => e (j k)) := by
  rw [sum_mul_wickSum_basis (p := 4) e
    (fun i => ∑ t, T t (i 0) (i 1) (i 2) * S t (i 3) (i 4) (i 5)), Fin.sum_univ_five]
  show ∑ j : Fin 4 → ι, (∑ u, ∑ t, T t u u (j 0) * S t (j 1) (j 2) (j 3)) *
        wickSum 4 (fun k => e (j k)) +
      ∑ j : Fin 4 → ι, (∑ u, ∑ t, T t u (j 0) u * S t (j 1) (j 2) (j 3)) *
        wickSum 4 (fun k => e (j k)) +
      ∑ j : Fin 4 → ι, (∑ u, ∑ t, T t u (j 0) (j 1) * S t u (j 2) (j 3)) *
        wickSum 4 (fun k => e (j k)) +
      ∑ j : Fin 4 → ι, (∑ u, ∑ t, T t u (j 0) (j 1) * S t (j 2) u (j 3)) *
        wickSum 4 (fun k => e (j k)) +
      ∑ j : Fin 4 → ι, (∑ u, ∑ t, T t u (j 0) (j 1) * S t (j 2) (j 3) u) *
        wickSum 4 (fun k => e (j k)) = _
  have z0 : ∀ a b c d : ι, ∑ u, ∑ t, T t u u a * S t b c d = 0 := fun a b c d => by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun t _ => by rw [← Finset.sum_mul, trace₂₃ hT hT0, zero_mul]
  have z1 : ∀ a b c d : ι, ∑ u, ∑ t, T t u a u * S t b c d = 0 := fun a b c d => by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun t _ => by rw [← Finset.sum_mul, trace₂₄ hT hT0, zero_mul]
  have s1 : ∀ a b c d : ι, ∑ u, ∑ t, T t u a b * S t c u d = ∑ u, ∑ t, T t u a b * S t u c d :=
    fun _ _ _ _ => Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => by
      rw [hS.swap₂₃]
  have s2 : ∀ a b c d : ι, ∑ u, ∑ t, T t u a b * S t c d u = ∑ u, ∑ t, T t u a b * S t u c d :=
    fun _ _ _ _ => Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => by
      rw [hS.swap₃₄, hS.swap₂₃]
  simp only [z0, z1, s1, s2, zero_mul, Finset.sum_const_zero, zero_add]
  ring

private theorem stage4 (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T) (hS : IsSymmetric4 S) :
    ∑ j : Fin 4 → ι, (∑ u, ∑ t, T t u (j 0) (j 1) * S t u (j 2) (j 3)) *
        wickSum 4 (fun k => e (j k)) =
      2 * ∑ j : Fin 2 → ι, (∑ v, ∑ u, ∑ t, T t u v (j 0) * S t u v (j 1)) *
        wickSum 2 (fun k => e (j k)) := by
  rw [sum_mul_wickSum_basis (p := 2) e
    (fun i => ∑ u, ∑ t, T t u (i 0) (i 1) * S t u (i 2) (i 3)), Fin.sum_univ_three]
  show ∑ j : Fin 2 → ι, (∑ v, ∑ u, ∑ t, T t u v v * S t u (j 0) (j 1)) *
        wickSum 2 (fun k => e (j k)) +
      ∑ j : Fin 2 → ι, (∑ v, ∑ u, ∑ t, T t u v (j 0) * S t u v (j 1)) *
        wickSum 2 (fun k => e (j k)) +
      ∑ j : Fin 2 → ι, (∑ v, ∑ u, ∑ t, T t u v (j 0) * S t u (j 1) v) *
        wickSum 2 (fun k => e (j k)) = _
  have z0 : ∀ a b : ι, ∑ v, ∑ u, ∑ t, T t u v v * S t u a b = 0 := fun a b => by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun t _ => by rw [← Finset.sum_mul, trace₃₄ hT hT0, zero_mul]
  have s1 : ∀ a b : ι, ∑ v, ∑ u, ∑ t, T t u v a * S t u b v =
      ∑ v, ∑ u, ∑ t, T t u v a * S t u v b :=
    fun _ _ => Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun t _ => by rw [hS.swap₃₄]
  simp only [z0, s1, zero_mul, Finset.sum_const_zero, zero_add]
  ring

private theorem reverse4 (hT : IsSymmetric4 T) (a b c d : ι) : T d c b a = T a b c d := by
  rw [hT.swap₁₂, hT.swap₂₃, hT.swap₃₄, hT.swap₁₂, hT.swap₂₃, hT.swap₁₂]

/-- Pairing sum of eight basis vectors weighted by `T ⊗ S`, with `T` symmetric and trace-free and `S`
symmetric: only the `4!` pairings joining the two factors survive. -/
theorem sum_wickSum_basis_eight (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T)
    (hS : IsSymmetric4 S) :
    ∑ i : Fin 8 → ι, T (i 0) (i 1) (i 2) (i 3) * S (i 4) (i 5) (i 6) (i 7) *
        wickSum 8 (fun k => e (i k)) =
      24 * ∑ a, ∑ b, ∑ c, ∑ d, T a b c d * S a b c d := by
  rw [stage8 e hT hT0 hS, stage6 e hT hT0 hS, stage4 e hT hT0 hS,
    sum_mul_wickSum_basis_two]
  show 4 * (3 * (2 * ∑ w, ∑ v, ∑ u, ∑ t, T t u v w * S t u v w)) = _
  simp_rw [← reverse4 hT, ← reverse4 hS]
  ring

/-- Pairing sum of six basis vectors weighted by `T ⊗ B`, with `T` symmetric and trace-free: zero. -/
theorem sum_wickSum_basis_six (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T) (B : ι → ι → ℝ) :
    ∑ i : Fin 6 → ι, T (i 0) (i 1) (i 2) (i 3) * B (i 4) (i 5) *
        wickSum 6 (fun k => e (i k)) = 0 := by
  rw [sum_mul_wickSum_basis (p := 4), Fin.sum_univ_five]
  show ∑ j : Fin 4 → ι, (∑ t, T t t (j 0) (j 1) * B (j 2) (j 3)) *
        wickSum 4 (fun k => e (j k)) +
      ∑ j : Fin 4 → ι, (∑ t, T t (j 0) t (j 1) * B (j 2) (j 3)) *
        wickSum 4 (fun k => e (j k)) +
      ∑ j : Fin 4 → ι, (∑ t, T t (j 0) (j 1) t * B (j 2) (j 3)) *
        wickSum 4 (fun k => e (j k)) +
      ∑ j : Fin 4 → ι, (∑ t, T t (j 0) (j 1) (j 2) * B t (j 3)) *
        wickSum 4 (fun k => e (j k)) +
      ∑ j : Fin 4 → ι, (∑ t, T t (j 0) (j 1) (j 2) * B (j 3) t) *
        wickSum 4 (fun k => e (j k)) = 0
  have z0 : ∀ a b c d : ι, ∑ t, T t t a b * B c d = 0 := fun a b c d => by
    rw [← Finset.sum_mul, hT0, zero_mul]
  have z1 : ∀ a b c d : ι, ∑ t, T t a t b * B c d = 0 := fun a b c d => by
    rw [← Finset.sum_mul, trace₁₃ hT hT0, zero_mul]
  have z2 : ∀ a b c d : ι, ∑ t, T t a b t * B c d = 0 := fun a b c d => by
    rw [← Finset.sum_mul, trace₁₄ hT hT0, zero_mul]
  have last : ∀ C : ι → ι → ℝ, ∑ j : Fin 4 → ι, (∑ t, T t (j 0) (j 1) (j 2) * C t (j 3)) *
      wickSum 4 (fun k => e (j k)) = 0 := by
    intro C
    rw [sum_mul_wickSum_basis_four]
    show ∑ w, ∑ s, ((∑ t, T t s s w * C t w) + (∑ t, T t s w s * C t w) +
      (∑ t, T t s w w * C t s)) = 0
    simp only [Finset.sum_add_distrib]
    have hA : ∀ w, ∑ s, ∑ t, T t s s w * C t w = 0 := fun w => by
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero fun t _ => by rw [← Finset.sum_mul, trace₂₃ hT hT0, zero_mul]
    have hB : ∀ w, ∑ s, ∑ t, T t s w s * C t w = 0 := fun w => by
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero fun t _ => by rw [← Finset.sum_mul, trace₂₄ hT hT0, zero_mul]
    have hC : ∑ w, ∑ s, ∑ t, T t s w w * C t s = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero fun t _ => by rw [← Finset.sum_mul, trace₃₄ hT hT0, zero_mul]
    simp only [hA, hB, hC, Finset.sum_const_zero, add_zero]
  simp only [z0, z1, z2, zero_mul, Finset.sum_const_zero, zero_add]
  rw [last B, last (fun a b => B b a), add_zero]

/-- Pairing sum of four basis vectors weighted by a symmetric trace-free `T`: zero. -/
theorem sum_wickSum_basis_four_traceFree (hT : IsSymmetric4 T) (hT0 : IsTraceFree4 T) :
    ∑ i : Fin 4 → ι, T (i 0) (i 1) (i 2) (i 3) * wickSum 4 (fun k => e (i k)) = 0 := by
  rw [sum_mul_wickSum_basis_four]
  refine Finset.sum_eq_zero fun w _ => ?_
  show ∑ t, (T t t w w + T t w t w + T t w w t) = 0
  simp only [Finset.sum_add_distrib, hT0 w w, trace₁₃ hT hT0, trace₁₄ hT hT0, add_zero]

end Stages

end

end ThirteenPlanes
