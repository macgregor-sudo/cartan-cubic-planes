module

public import ThirteenPlanes.MatrixLine
public import ThirteenPlanes.MatrixLineLift

@[expose] public section

set_option backward.privateInPublic true

open scoped BigOperators

namespace ThirteenPlanes

noncomputable section

private def chargeShear (i j : Fin 3) (hij : i ≠ j) : Charge ≃+ Charge where
  toFun x k := if k = i then x k + x j else x k
  invFun x k := if k = i then x k - x j else x k
  left_inv x := by
    funext k
    by_cases h : k = i
    · subst k
      simp [Ne.symm hij]
    · simp [h]
  right_inv x := by
    funext k
    by_cases h : k = i
    · subst k
      simp [Ne.symm hij]
    · simp [h]
  map_add' x y := by
    funext k
    by_cases h : k = i
    · simp [h]
      abel
    · simp [h]

set_option maxRecDepth 3500 in
private def liftE12 : GradeLift where
  relabel := chargeShear 0 1 (by decide)
  phase _ := 0
  odd _ := by simp
  cocycle := by decide +kernel

set_option maxRecDepth 3500 in
private def liftE21 : GradeLift where
  relabel := chargeShear 1 0 (by decide)
  phase _ := 0
  odd _ := by simp
  cocycle := by decide +kernel

set_option maxRecDepth 3500 in
private def liftE32 : GradeLift where
  relabel := chargeShear 2 1 (by decide)
  phase x := x 0 * (x 1)^2
  odd := by decide +kernel
  cocycle := by decide +kernel

set_option maxRecDepth 3500 in
private def liftE13 : GradeLift where
  relabel := chargeShear 0 2 (by decide)
  phase x := -(x 1 * (x 2)^2)
  odd := by decide +kernel
  cocycle := by decide +kernel

private def liftGenerator : Fin 4 → GradeLift := ![liftE12, liftE21, liftE32, liftE13]

private def liftWord : List (Fin 4) → GradeLift
  | [] => GradeLift.identity
  | i :: is => (liftGenerator i).trans (liftWord is)

private def lineNormals : Fin 13 → Charge :=
  ![![0,0,1], ![0,1,0], ![0,1,1], ![0,1,2], ![1,0,0], ![1,0,1], ![1,0,2],
    ![1,1,0], ![1,1,1], ![1,1,2], ![1,2,0], ![1,2,1], ![1,2,2]]

private def lineWord : Fin 13 → List (Fin 4) :=
  ![[], [2,1,0,3,1], [2,2], [2], [2,1,0,0,3], [2,1,0,0], [2,1,1,0],
    [2,1,0,3], [2,1,0], [2,1,1], [2,1,3], [2,1], [2,2,1]]

set_option maxRecDepth 3500 in
private theorem lineWords_relabelToCoordinateLine (i : Fin 13) :
    ∀ q : Charge, chargeDot (lineNormals i) ((liftWord (lineWord i)).relabel q) = 0 ↔
      q 2 = 0 := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 3500 in
private theorem normal_list_complete : ∀ n : NonzeroCharge,
    ∃ i : Fin 13, n.val = lineNormals i ∨ n.val = -lineNormals i := by
  decide +kernel

theorem lineLift_exists (n : NonzeroCharge) :
    ∃ g : GradeLift, ∀ q : Charge, chargeDot n.val (g.relabel q) = 0 ↔ q 2 = 0 := by
  obtain ⟨i, he | he⟩ := normal_list_complete n
  · exact ⟨liftWord (lineWord i), by simpa only [he] using lineWords_relabelToCoordinateLine i⟩
  · exact ⟨liftWord (lineWord i), by
      simpa only [he, chargeDot_neg_left, neg_eq_zero] using lineWords_relabelToCoordinateLine i⟩

/-- Obtain the matrix embedding after transporting its charge line by the given lift. -/
def liftedMatrixLine (g : GradeLift) : TracelessHermitian3 →ₗᵢ[ℝ] SignedField :=
  g.action.toLinearIsometry.comp matrixLineEmbed

theorem liftedMatrixLine_square (g : GradeLift) (u : ℝ × ℝ) (x : TracelessHermitian3) :
    (coupling signedPair u).squareMap (liftedMatrixLine g x) =
      liftedMatrixLine g ((coupling fourPlanePair u).squareMap x) := by
  change (coupling signedPair u).squareMap (g.action (matrixLineEmbed x)) =
    g.action (matrixLineEmbed ((coupling fourPlanePair u).squareMap x))
  rw [g.preserves_square, matrixLineEmbed_coupling_square]

theorem liftedMatrixLine_range (n : NonzeroCharge) (g : GradeLift)
    (hg : ∀ q, chargeDot n.val (g.relabel q) = 0 ↔ q 2 = 0) (y : SignedField) :
    y ∈ LinearMap.range (liftedMatrixLine g).toLinearMap ↔
      ∀ q : NonzeroCharge, chargeDot n.val q.val ≠ 0 → signedCoordinates y q = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ q hq
    let p := g.nonzeroEquiv.symm q
    have hp : g.nonzeroEquiv p = q := g.nonzeroEquiv.apply_symm_apply q
    have hp₀ : p.val 2 ≠ 0 := by
      intro hz
      apply hq
      rw [← hp, GradeLift.nonzeroEquiv_val]
      exact (hg p.val).mpr hz
    change signedCoordinates (g.action (matrixLineEmbed x)) q = 0
    rw [← hp, g.action_coordinates, matrixLineEmbed_off_charge x p hp₀, mul_zero]
  · intro hy
    obtain ⟨x, rfl⟩ := g.action.surjective y
    have hx : x ∈ LinearMap.range matrixLineEmbed.toLinearMap := by
      apply (mem_matrixLineEmbed_range_iff x).mpr
      intro q hq
      have hz := hy (g.nonzeroEquiv q) (by
        change chargeDot n.val (g.relabel q.val) ≠ 0
        exact fun hz => hq ((hg q.val).mp hz))
      rw [g.action_coordinates] at hz
      refine (mul_eq_zero.mp hz).resolve_left ?_
      intro hp
      have hn := chargePhase_norm (g.phase q.val)
      simp [hp] at hn
    obtain ⟨x, rfl⟩ := hx
    exact ⟨x, rfl⟩

/-- Every projective charge line has the identified four-plane model, with its full ambient square. -/
theorem matrixLine_over_any_normal (n : NonzeroCharge) :
    ∃ j : TracelessHermitian3 →ₗᵢ[ℝ] SignedField,
      (∀ (u : ℝ × ℝ) (x : TracelessHermitian3),
        (coupling signedPair u).squareMap (j x) =
          j ((coupling fourPlanePair u).squareMap x)) ∧
      (∀ y : SignedField, y ∈ LinearMap.range j.toLinearMap ↔
        ∀ q : NonzeroCharge, chargeDot n.val q.val ≠ 0 → signedCoordinates y q = 0) := by
  obtain ⟨g, hg⟩ := lineLift_exists n
  exact ⟨liftedMatrixLine g, liftedMatrixLine_square g, liftedMatrixLine_range n g hg⟩

end

end ThirteenPlanes
