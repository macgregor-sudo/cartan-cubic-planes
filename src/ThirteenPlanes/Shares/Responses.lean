module

public import ThirteenPlanes.PlaneShares
public import ThirteenPlanes.PlanePencilEnergy

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open scoped BigOperators RealInnerProductSpace
open PlaneContractions

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} {h : SymmetricCubic V} {planes : PlaneDecomposition V ι} {c : ℝ}

/-- The symmetric polarization, in both repeated-plane slots, of the degree (2,1,1)
response of the normalized pencil energy. -/
def planeResponseForm (h : SymmetricCubic V) (c t : ℝ) (u u' y z : V) : ℝ :=
  (4 * t * (1 - t) / c) * ⟪h.L u u', h.L y z⟫

/-- Squared coefficient norm of the polarized energy response on the three indicated planes. -/
def planeResponseNormSq (h : SymmetricCubic V) (planes : PlaneDecomposition V ι)
    (e : (i : ι) → OrthonormalBasis (Fin 2) ℝ (planes.plane i))
    (c t : ℝ) (i j k : ι) : ℝ :=
  ∑ b : Fin 2, ∑ d : Fin 2, ∑ a : Fin 2, ∑ a' : Fin 2,
    (planeResponseForm h c t (e i a) (e i a') (e j b) (e k d)) ^ 2

private theorem restricted_product (closed : IsClosedPlaneSystem h planes) (i : ι)
    (x y : planes.plane i) : ((planes.restriction i h).L x y : V) = h.L x y := by
  let z : planes.plane i := ⟨h.L x y, closed i x.property y.property⟩
  have hz : (planes.restriction i h).L x y = z := by
    apply ext_inner_right ℝ
    intro w
    exact planes.restriction_apply i h x y w
  exact congrArg Subtype.val hz

private theorem plane_products_coefficient_sum (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (i : ι) (e : OrthonormalBasis (Fin 2) ℝ (planes.plane i)) (v : V) :
    (∑ a : Fin 2, ∑ b : Fin 2, ⟪h.L (e a : V) (e b : V), v⟫ ^ 2) =
      2 * c * ‖planes.proj i v‖ ^ 2 := by
  let S := planes.plane i
  let g := planes.restriction i h
  let w := piP planes i v
  have rg : IsRound g c := restriction_isRound round closed i
  have tf : g.TraceFree := traceFree_of_round_finrank_two rg (planes.dimension i)
  have hs := ((polarization_and_contractions rg).2.2 tf).1 e
  rw [planes.dimension, Nat.cast_ofNat] at hs
  have hswap (a : Fin 2) :
      (∑ b : Fin 2, ⟪h.L (e a : V) (e b : V), v⟫ ^ 2) = ‖g.L (e a) w‖ ^ 2 := by
    rw [← e.sum_sq_inner_right (g.L (e a) w)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hp : ⟪g.L (e a) (e b), w⟫ = ⟪h.L (e a : V) (e b : V), v⟫ :=
      (inner_piP_left planes i _ _).trans (by rw [restricted_product closed])
    rw [← hp, g.L_isSymmetric]
  have hc (a : Fin 2) : ⟪((g.L (e a)) ^ 2) w, w⟫ = ‖g.L (e a) w‖ ^ 2 := by
    rw [pow_two]
    change ⟪g.L (e a) (g.L (e a) w), w⟫ = _
    rw [g.L_isSymmetric, real_inner_self_eq_norm_sq]
  have henergy := congrArg (fun L : Module.End ℝ S => inner ℝ (L w) w) hs
  change ⟪(∑ a, ((g.L (e a)) ^ 2)) w, w⟫ =
    ⟪((c * (2 + 2) / 2) • (1 : Module.End ℝ S)) w, w⟫ at henergy
  simp only [LinearMap.sum_apply, sum_inner, hc, LinearMap.smul_apply, one_apply_eq_self,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at henergy
  simp only [hswap]
  change _ = 2 * c * ‖w‖ ^ 2
  linear_combination henergy

variable [Fintype ι]

omit [Fintype ι] in
/-- The squared polarized response is (32t^2(1-t)^2) times the actual projection share. -/
theorem planeResponseNormSq_eq_share (round : IsRound h c) (closed : IsClosedPlaneSystem h planes)
    (e : (i : ι) → OrthonormalBasis (Fin 2) ℝ (planes.plane i))
    (t : ℝ) {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) :
    planeResponseNormSq h planes e c t i j k =
      32 * t ^ 2 * (1 - t) ^ 2 * planeShare h planes i j k := by
  rw [planeShare_cycle round closed hij hjk, planeShare_eq_sum_projected_sq round closed hjk i (e j) (e k)]
  have hc (b d : Fin 2) :
      (∑ a : Fin 2, ∑ a' : Fin 2,
        (planeResponseForm h c t (e i a) (e i a') (e j b) (e k d)) ^ 2) =
        (4 * t * (1 - t) / c) ^ 2 * (2 * c * ‖planes.proj i (h.L (e j b : V) (e k d : V))‖ ^ 2) := by
    simp only [planeResponseForm, mul_pow, ← Finset.mul_sum, plane_products_coefficient_sum round closed]
  simp only [planeResponseNormSq, hc, ← Finset.mul_sum]
  field_simp [round.positive.ne']
  ring

/-- The quartic plane responses: response size and the recovery formula for each distinct triple. -/
theorem planePencilResponses [DecidableEq ι] (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes)
    (e : (i : ι) → OrthonormalBasis (Fin 2) ℝ (planes.plane i))
    (t : ℝ) {i j k : ι} (hij : i ≠ j) (_hik : i ≠ k) (hjk : j ≠ k) :
    planeResponseNormSq h planes e c t i j k =
      32 * t ^ 2 * (1 - t) ^ 2 * planeShare h planes i j k ∧
    (t ≠ 0 → t ≠ 1 → planeShare h planes i j k =
      (2 * planeResponseNormSq h planes e c t i j k) /
        (∑ r ∈ Finset.univ.filter (fun r => r ≠ j ∧ r ≠ k), planeResponseNormSq h planes e c t r j k)) := by
  have hi := planeResponseNormSq_eq_share round closed e t hij hjk
  refine ⟨hi, fun ht₀ ht₁ => ?_⟩
  have hsum : (∑ r ∈ Finset.univ.filter (fun r => r ≠ j ∧ r ≠ k),
    planeResponseNormSq h planes e c t r j k) = 64 * t ^ 2 * (1 - t) ^ 2 := by
    calc
      _ = ∑ r ∈ Finset.univ.filter (fun r => r ≠ j ∧ r ≠ k),
          (32 * t ^ 2 * (1 - t) ^ 2) * planeShare h planes j k r := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hrj := (Finset.mem_filter.mp hr).2.1
        rw [planeResponseNormSq_eq_share round closed e t hrj hjk,
          planeShare_cycle round closed hrj hjk]
      _ = _ := by rw [← Finset.mul_sum, planeShare_pair_sum round closed hjk]; ring
  have hden : 64 * t ^ 2 * (1 - t) ^ 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ht₀))
      (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm ht₁)))
  rw [hi, hsum, eq_div_iff hden]
  ring

/-- Extract the term of degree (2,1,1) in a quartic by taking the part odd in its last
two inputs and subtracting its value at zero in the first input. -/
def quarticResponse (f : V → ℝ) (u y z : V) : ℝ :=
  (f (u + y + z) - f (u + y + -z) - f (u + -y + z) + f (u + -y + -z) -
    (f (y + z) - f (y + -z) - f (-y + z) + f (-y + -z))) / 4

omit [FiniteDimensional ℝ V] [Fintype ι] in
set_option maxHeartbeats 1500000 in
private theorem quarticResponse_square (g : SymmetricCubic V) (u y z : V) :
    quarticResponse (fun x => ‖g.squareMap x‖ ^ 2) u y z =
      4 * ⟪g.L u u, g.L y z⟫ + 8 * ⟪g.L u y, g.L u z⟫ := by
  simp only [quarticResponse, ← real_inner_self_eq_norm_sq, SymmetricCubic.squareMap,
    map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply, inner_add_left, inner_add_right,
    inner_neg_left, inner_neg_right, g.L_comm, real_inner_comm]
  ring

private theorem pencil_product_expansion (t : ℝ) (x y : V) :
    (interactionCubic (planePencil h planes) t).L x y =
      (planePencil h planes).diagonalCubic.L x y +
        t • (h.L x y - (planePencil h planes).diagonalCubic.L x y) := by
  rw [interactionCubic, coupling_apply, one_smul]
  change ((planePencil h planes).diagonalCubic +
    t • (h - (planePencil h planes).diagonalCubic)).L x y = _
  simp only [map_add (SymmetricCubic.L (V := V)), map_smul (SymmetricCubic.L (V := V)),
    map_sub (SymmetricCubic.L (V := V)), LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply]

theorem pencil_product_same (closed : IsClosedPlaneSystem h planes) (t : ℝ)
    (i : ι) (x y : planes.plane i) :
    (interactionCubic (planePencil h planes) t).L (x : V) y = h.L (x : V) y := by
  have hm : (planePencil h planes).mixingCubic.L (x : V) y = 0 := by
    apply ext_inner_right ℝ
    intro w
    rw [inner_zero_left]
    exact planePencil_mixing_repeated closed i x y w
  change (h - (planePencil h planes).diagonalCubic).L (x : V) y = 0 at hm
  rw [map_sub (SymmetricCubic.L (V := V)), LinearMap.sub_apply, LinearMap.sub_apply] at hm
  rw [pencil_product_expansion, hm, smul_zero, add_zero, ← sub_eq_zero.mp hm]

theorem pencil_product_distinct (t : ℝ) {i j : ι} (hij : i ≠ j)
    (x : planes.plane i) (y : planes.plane j) :
    (interactionCubic (planePencil h planes) t).L (x : V) y = t • h.L (x : V) y := by
  have hd : (planePencil h planes).diagonalCubic.L (x : V) y = 0 := by
    apply ext_inner_right ℝ
    intro w
    rw [inner_zero_left]
    change (planePencil h planes).diagonalCubic.apply x y w = 0
    have hD : (planePencil h planes).diagonalCubic = ∑ k, h.pullback (planes.proj k) := rfl
    rw [hD, PlaneContractions.apply_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [SymmetricCubic.pullback_apply]
    by_cases hki : k = i
    · subst k
      have hz : planes.proj i y = 0 :=
        congrArg Subtype.val (LinearMap.congr_fun (piP_subtype_ne planes hij) y)
      rw [hz]
      change ⟪h.L _ 0, _⟫ = 0
      rw [map_zero, inner_zero_left]
    · have hz : planes.proj k x = 0 :=
        congrArg Subtype.val (LinearMap.congr_fun (piP_subtype_ne planes hki) x)
      rw [hz]
      change ⟪h.L 0 _, _⟫ = 0
      rw [map_zero, LinearMap.zero_apply, inner_zero_left]
  rw [pencil_product_expansion, hd, sub_zero, zero_add]

/-- Formula (8-response) for the actual normalized quartic of the plane pencil. -/
theorem quarticResponse_normalizedPencilEnergy (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) (t : ℝ) {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : planes.plane i) (y : planes.plane j) (z : planes.plane k) :
    quarticResponse (normalizedPencilEnergy h planes c t) (u : V) y z =
      planeResponseForm h c t (u : V) u y z := by
  let g := interactionCubic (planePencil h planes) t
  have hscale : quarticResponse (normalizedPencilEnergy h planes c t) (u : V) y z =
      quarticResponse (fun x => ‖g.squareMap x‖ ^ 2) (u : V) y z / c := by
    unfold quarticResponse normalizedPencilEnergy
    ring
  rw [hscale, quarticResponse_square]
  change (4 * ⟪g.L (u : V) u, g.L (y : V) z⟫ +
    8 * ⟪g.L (u : V) y, g.L (u : V) z⟫) / c = _
  have hu := pencil_product_same closed t i u u
  have hyz := pencil_product_distinct (h := h) t hjk y z
  have huy := pencil_product_distinct (h := h) t hij u y
  have huz := pencil_product_distinct (h := h) t hik u z
  change g.L (u : V) u = _ at hu
  change g.L (y : V) z = _ at hyz
  change g.L (u : V) y = _ at huy
  change g.L (u : V) z = _ at huz
  rw [hu, hyz, huy, huz, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right]
  have p := polarized round (u : V) u y z
  have hcomm : ⟪h.L (u : V) z, h.L (u : V) y⟫ = ⟪h.L (u : V) y, h.L (u : V) z⟫ := by
    rw [real_inner_comm]
  rw [hcomm] at p
  simp only [(planes.pairwise_orthogonal hij).inner_eq u.property y.property,
    (planes.pairwise_orthogonal hik).inner_eq u.property z.property,
    (planes.pairwise_orthogonal hjk).inner_eq y.property z.property, mul_zero,
    add_zero] at p
  unfold planeResponseForm
  linear_combination (4 * t ^ 2 / c) * p

/-- The four-input form is the polarization of the actual energy response in the repeated slot. -/
theorem planeResponseForm_eq_quartic_polarization (round : IsRound h c)
    (closed : IsClosedPlaneSystem h planes) (t : ℝ) {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u u' : planes.plane i) (y : planes.plane j) (z : planes.plane k) :
    planeResponseForm h c t (u : V) u' y z =
      (quarticResponse (normalizedPencilEnergy h planes c t) ((u + u' : planes.plane i) : V) y z -
        quarticResponse (normalizedPencilEnergy h planes c t) (u : V) y z -
        quarticResponse (normalizedPencilEnergy h planes c t) (u' : V) y z) / 2 := by
  rw [quarticResponse_normalizedPencilEnergy round closed t hij hik hjk,
    quarticResponse_normalizedPencilEnergy round closed t hij hik hjk,
    quarticResponse_normalizedPencilEnergy round closed t hij hik hjk]
  simp only [planeResponseForm, Submodule.coe_add, map_add, LinearMap.add_apply, inner_add_left]
  rw [h.L_comm (u' : V) (u : V)]
  ring

end
end ThirteenPlanes.RoundCubics
