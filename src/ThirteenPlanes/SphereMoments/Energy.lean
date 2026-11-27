module

public import ThirteenPlanes.SphereMoments.Tensor
public import ThirteenPlanes.Cubic

@[expose] public section

/-!
# Sphere mean and variance of the field energy of a cubic

For a real symmetric cubic `h` with metric-raised square `Q_h(x) = h.squareMap x`, the field energy
`‖Q_h(x)‖²` is the quartic form of the array `K_{abcd} = Σ_m h_{abm} h_{cdm}` and one third of the
quartic form of the symmetrized array `S = K_{abcd} + K_{acbd} + K_{adbc}`.  We compute its sphere
mean in terms of the trace vector and the coefficient norm, and the variance of
`U = ‖Q_h‖² / 8` whenever `S - λ Π` is trace-free, `Π` the pairing array.
-/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)

namespace SymmetricCubic

theorem coefficient_swap₁₂ (h : SymmetricCubic V) (a b c : ι) :
    h.coefficient e a b c = h.coefficient e b a c := h.apply_swap₁₂ _ _ _

theorem coefficient_swap₂₃ (h : SymmetricCubic V) (a b c : ι) :
    h.coefficient e a b c = h.coefficient e a c b := h.apply_swap₂₃ _ _ _

/-- The array `K_{abcd} = Σ_m h_{abm} h_{cdm}`. -/
def squareArray (h : SymmetricCubic V) (a b c d : ι) : ℝ :=
  ∑ m, h.coefficient e a b m * h.coefficient e c d m

/-- The symmetrized quartic array `S_{abcd} = K_{abcd} + K_{acbd} + K_{adbc}`. -/
def symmetrizedArray (h : SymmetricCubic V) (a b c d : ι) : ℝ :=
  h.squareArray e a b c d + h.squareArray e a c b d + h.squareArray e a d b c

theorem apply_expand (h : SymmetricCubic V) (x z : V) :
    h.apply x x z = ∑ a, ∑ b, ⟪e a, x⟫ * ⟪e b, x⟫ * h.apply (e a) (e b) z := by
  have hx := e.sum_repr' x
  have := congrArg (fun y => h.trilinear y y z) hx.symm
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, trilinear_apply,
    smul_eq_mul] at this
  rw [this]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [h.apply_swap₁₂]; ring

/-- The field energy is the quartic form of the square array. -/
theorem norm_squareMap_sq (h : SymmetricCubic V) (x : V) :
    ‖h.squareMap x‖ ^ 2 = quarticForm e (h.squareArray e) x := by
  rw [← e.sum_sq_inner_right]
  have hm : ∀ m, ⟪e m, h.squareMap x⟫ =
      ∑ a, ∑ b, ⟪e a, x⟫ * ⟪e b, x⟫ * h.coefficient e a b m := by
    intro m
    rw [real_inner_comm]
    exact h.apply_expand e x (e m)
  simp only [hm, sq, quarticForm, squareArray, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun m _ => ?_
  ring

/-- The quartic form of the symmetrized array is three times the field energy. -/
theorem quarticForm_symmetrizedArray (h : SymmetricCubic V) (x : V) :
    quarticForm e (h.symmetrizedArray e) x = 3 * ‖h.squareMap x‖ ^ 2 := by
  rw [norm_squareMap_sq e]
  have h1 : quarticForm e (fun a b c d => h.squareArray e a c b d) x =
      quarticForm e (h.squareArray e) x := by
    unfold quarticForm
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    ring
  have h2 : quarticForm e (fun a b c d => h.squareArray e a d b c) x =
      quarticForm e (h.squareArray e) x := by
    have g1 : quarticForm e (fun a b c d => h.squareArray e a d b c) x =
        quarticForm e (fun a b c d => h.squareArray e a c b d) x := by
      unfold quarticForm
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [g1, h1]
  have hsum : quarticForm e (h.symmetrizedArray e) x =
      quarticForm e (h.squareArray e) x +
        quarticForm e (fun a b c d => h.squareArray e a c b d) x +
        quarticForm e (fun a b c d => h.squareArray e a d b c) x := by
    simp only [quarticForm, symmetrizedArray, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hsum, h1, h2]; ring

theorem isSymmetric4_symmetrizedArray (h : SymmetricCubic V) :
    IsSymmetric4 (h.symmetrizedArray e) := by
  have K12 : ∀ a b c d, h.squareArray e a b c d = h.squareArray e b a c d := fun a b c d =>
    Finset.sum_congr rfl fun m _ => by rw [h.coefficient_swap₁₂ e a b]
  have K34 : ∀ a b c d, h.squareArray e a b c d = h.squareArray e a b d c := fun a b c d =>
    Finset.sum_congr rfl fun m _ => by rw [h.coefficient_swap₁₂ e c d]
  have Kswap : ∀ a b c d, h.squareArray e a b c d = h.squareArray e c d a b := fun a b c d =>
    Finset.sum_congr rfl fun m _ => mul_comm _ _
  refine ⟨fun a b c d => ?_, fun a b c d => ?_, fun a b c d => ?_⟩ <;>
    simp only [symmetrizedArray]
  · rw [K12 b a c d, Kswap b c a d, Kswap b d a c]; ring
  · rw [K34 a d c b]; ring
  · rw [K34 a b d c]; ring

/-- Sum of the squared traces `Σ_m (tr L(e m))²`, the squared norm of the trace vector. -/
def traceNormSq (h : SymmetricCubic V) : ℝ := ∑ m, (LinearMap.trace ℝ V (h.L (e m))) ^ 2

theorem trace_L_basis (h : SymmetricCubic V) (m : ι) :
    LinearMap.trace ℝ V (h.L (e m)) = ∑ t, h.coefficient e t t m := by
  rw [trace_eq_sum_inner e]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [real_inner_comm]
  change h.apply (e m) (e t) (e t) = h.apply (e t) (e t) (e m)
  rw [h.apply_swap₁₂, h.apply_swap₂₃]

end SymmetricCubic

open SymmetricCubic

variable [Nontrivial V]

/-- The mean of the field energy over the unit sphere:
`E ‖Q_h(x)‖² = (‖v‖² + 2 ⟨h, h⟩) / (n (n + 2))`, `v` the trace vector. -/
theorem sphereAverage_norm_squareMap_sq (h : SymmetricCubic V) :
    sphereAverage (fun x => ‖h.squareMap x‖ ^ 2) =
      (h.traceNormSq e + 2 * h.tensorPairing h) /
        (Module.finrank ℝ V * (Module.finrank ℝ V + 2)) := by
  simp_rw [norm_squareMap_sq e]
  rw [show (fun x => quarticForm e (h.squareArray e) x) = quarticForm e (h.squareArray e) from rfl,
    sphereAverage_quarticForm]
  congr 1
  simp only [squareArray, traceNormSq, trace_L_basis, tensorPairing_eq_sum e, sq,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  have E1 : ∑ w, ∑ t, ∑ m, h.coefficient e t t m * h.coefficient e w w m =
      ∑ m, ∑ w, ∑ t, h.coefficient e t t m * h.coefficient e w w m := by
    calc _ = ∑ w, ∑ m, ∑ t, h.coefficient e t t m * h.coefficient e w w m :=
          Finset.sum_congr rfl fun w _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [E1]
  have E2 : ∀ w t m : ι, h.coefficient e t w m * h.coefficient e w t m =
      h.coefficient e w t m * h.coefficient e w t m := fun w t m => by
    rw [h.coefficient_swap₁₂ e t w]
  have E3 : ∀ w t m : ι, h.coefficient e t w m * h.coefficient e t w m =
      h.coefficient e w t m * h.coefficient e w t m := fun w t m => by
    rw [h.coefficient_swap₁₂ e t w]
  simp only [E2, E3]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => ?_
  ring

omit [Nontrivial V] in
theorem continuous_quarticForm (T : ι → ι → ι → ι → ℝ) : Continuous (quarticForm e T) := by
  unfold quarticForm; fun_prop

/-- The pairing array `Π_{abcd} = δ_{ab}δ_{cd} + δ_{ac}δ_{bd} + δ_{ad}δ_{bc}`. -/
def pairingArray (a b c d : ι) : ℝ :=
  (if a = b then 1 else 0) * (if c = d then 1 else 0) +
    (if a = c then 1 else 0) * (if b = d then 1 else 0) +
    (if a = d then 1 else 0) * (if b = c then 1 else 0)

omit [Nontrivial V] [FiniteDimensional ℝ V] in
theorem isSymmetric4_pairingArray : IsSymmetric4 (pairingArray (ι := ι)) := by
  have dc : ∀ a b : ι, (if a = b then (1 : ℝ) else 0) = if b = a then 1 else 0 := fun a b => by
    by_cases h : a = b <;> simp [h, eq_comm]
  refine ⟨fun a b c d => ?_, fun a b c d => ?_, fun a b c d => ?_⟩ <;> unfold pairingArray
  · rw [dc b a, dc b c, dc b d]; ring
  · rw [dc c b]; ring
  · rw [dc d c]; ring

omit [Nontrivial V] [FiniteDimensional ℝ V] [DecidableEq ι] in
theorem quarticForm_perm₂₃ (T : ι → ι → ι → ι → ℝ) (x : V) :
    quarticForm e (fun a b c d => T a c b d) x = quarticForm e T x := by
  unfold quarticForm
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  ring

omit [Nontrivial V] [FiniteDimensional ℝ V] [DecidableEq ι] in
theorem quarticForm_perm₃₄ (T : ι → ι → ι → ι → ℝ) (x : V) :
    quarticForm e (fun a b c d => T a b d c) x = quarticForm e T x := by
  unfold quarticForm
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

omit [Nontrivial V] [FiniteDimensional ℝ V] [DecidableEq ι] in
theorem quarticForm_add (T T' : ι → ι → ι → ι → ℝ) (x : V) :
    quarticForm e (fun a b c d => T a b c d + T' a b c d) x =
      quarticForm e T x + quarticForm e T' x := by
  simp only [quarticForm, add_mul, Finset.sum_add_distrib]

omit [Nontrivial V] in
theorem quarticForm_pairingArray (x : V) :
    quarticForm e (pairingArray (ι := ι)) x = 3 * ‖x‖ ^ 4 := by
  set P : ι → ι → ι → ι → ℝ := fun a b c d =>
    (if a = b then 1 else 0) * (if c = d then 1 else 0)
  have hP : quarticForm e P x = ‖x‖ ^ 4 := by
    have hcol : ∀ g : ι → ι → ℝ, ∑ a, ∑ b, (if a = b then (1 : ℝ) else 0) * g a b =
        ∑ a, g a a := fun g => by simp [ite_mul, Finset.sum_ite_eq]
    have step : quarticForm e P x = ∑ a, ∑ b, (if a = b then (1 : ℝ) else 0) *
        (⟪e a, x⟫ * ⟪e b, x⟫ * ∑ c, ∑ d, (if c = d then (1 : ℝ) else 0) *
          (⟪e c, x⟫ * ⟪e d, x⟫)) := by
      unfold quarticForm
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      simp only [P]; ring
    rw [step, hcol, hcol, ← Finset.sum_mul]
    have hn : ∑ a, ⟪e a, x⟫ * ⟪e a, x⟫ = ‖x‖ ^ 2 := by
      rw [← e.sum_sq_inner_right]; simp only [sq]
    rw [hn]; ring
  have hPi : (pairingArray (ι := ι)) = fun a b c d =>
      (P a b c d + (fun a b c d => P a c b d) a b c d) +
        (fun a b c d => (fun a b c d => P a c b d) a b d c) a b c d := by
    funext a b c d; simp only [pairingArray, P]
  have e1 : quarticForm e pairingArray x = quarticForm e P x +
      quarticForm e (fun a b c d => P a c b d) x + quarticForm e (fun a b c d => P a d b c) x := by
    rw [hPi, quarticForm_add, quarticForm_add]
  have e2 := quarticForm_perm₂₃ e P x
  have e3 : quarticForm e (fun a b c d => P a d b c) x =
      quarticForm e (fun a b c d => P a c b d) x :=
    quarticForm_perm₃₄ e (fun a b c d => P a c b d) x
  linarith

omit [Nontrivial V] in
theorem quarticForm_sub_mul (S P : ι → ι → ι → ι → ℝ) (c : ℝ) (x : V) :
    quarticForm e (fun a b d f => S a b d f - c * P a b d f) x =
      quarticForm e S x - c * quarticForm e P x := by
  simp only [quarticForm, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

/-- On the unit sphere, `‖Q_h(x)‖²/8 = λ/8 + H(x,x,x,x)/24` with `H = S - λ Π`. -/
theorem energy_eq_on_sphere (h : SymmetricCubic V) (c : ℝ) (x : V) (hx : ‖x‖ = 1) :
    ‖h.squareMap x‖ ^ 2 / 8 = c / 8 +
      quarticForm e (fun a b d f => h.symmetrizedArray e a b d f - c * pairingArray a b d f) x / 24 := by
  rw [quarticForm_sub_mul, quarticForm_symmetrizedArray, quarticForm_pairingArray, hx]
  ring

/-- If `H = S - λ Π` is trace-free, the mean of `U = ‖Q_h‖²/8` over the unit sphere is `λ/8`. -/
theorem sphereAverage_energy_of_traceFree (h : SymmetricCubic V) (c : ℝ)
    (hH : IsTraceFree4 fun a b d f => h.symmetrizedArray e a b d f - c * pairingArray a b d f) :
    sphereAverage (fun x => ‖h.squareMap x‖ ^ 2 / 8) = c / 8 := by
  set H := fun a b d f => h.symmetrizedArray e a b d f - c * pairingArray a b d f
  have hHs : IsSymmetric4 H := by
    have hS := isSymmetric4_symmetrizedArray e h
    have hP := isSymmetric4_pairingArray (ι := ι)
    exact ⟨fun a b d f => by simp only [H, hS.swap₁₂ a b, hP.swap₁₂ a b],
      fun a b d f => by simp only [H, hS.swap₂₃ a b, hP.swap₂₃ a b],
      fun a b d f => by simp only [H, hS.swap₃₄ a b, hP.swap₃₄ a b]⟩
  rw [sphereAverage_congr_sphere (g := fun x => c / 8 + (1 / 24) * quarticForm e H x)
    fun x hx => by rw [energy_eq_on_sphere e h c x hx]; ring]
  rw [sphereAverage_add continuous_const ((continuous_quarticForm e H).const_mul _),
    sphereAverage_const, sphereAverage_const_mul, sphereAverage_quarticForm_traceFree e hHs hH]
  ring

/-- If `H = S - λ Π` is trace-free, the variance of `U = ‖Q_h‖²/8` over the unit sphere is
`|H|² / (24 n (n+2) (n+4) (n+6))`. -/
theorem sphereVariance_energy_of_traceFree (h : SymmetricCubic V) (c : ℝ)
    (hH : IsTraceFree4 fun a b d f => h.symmetrizedArray e a b d f - c * pairingArray a b d f) :
    sphereVariance (fun x => ‖h.squareMap x‖ ^ 2 / 8) =
      (∑ a, ∑ b, ∑ d, ∑ f, (h.symmetrizedArray e a b d f - c * pairingArray a b d f) ^ 2) /
        (24 * (Module.finrank ℝ V * (Module.finrank ℝ V + 2) * (Module.finrank ℝ V + 4) *
          (Module.finrank ℝ V + 6))) := by
  set H := fun a b d f => h.symmetrizedArray e a b d f - c * pairingArray a b d f
  have hHs : IsSymmetric4 H := by
    have hS := isSymmetric4_symmetrizedArray e h
    have hP := isSymmetric4_pairingArray (ι := ι)
    exact ⟨fun a b d f => by simp only [H, hS.swap₁₂ a b, hP.swap₁₂ a b],
      fun a b d f => by simp only [H, hS.swap₂₃ a b, hP.swap₂₃ a b],
      fun a b d f => by simp only [H, hS.swap₃₄ a b, hP.swap₃₄ a b]⟩
  unfold sphereVariance
  rw [sphereAverage_energy_of_traceFree e h c hH]
  rw [sphereAverage_congr_sphere (g := fun x => (1 / 576) * (quarticForm e H x * quarticForm e H x))
    fun x hx => by
      show (‖h.squareMap x‖ ^ 2 / 8 - c / 8) ^ 2 = _
      rw [energy_eq_on_sphere e h c x hx]; ring]
  rw [sphereAverage_const_mul, sphereAverage_quarticForm_mul_quarticForm e hHs hH hHs]
  have hn : (0 : ℝ) < Module.finrank ℝ V := by exact_mod_cast Module.finrank_pos
  field_simp
  simp only [sq]
  ring

end

end ThirteenPlanes
