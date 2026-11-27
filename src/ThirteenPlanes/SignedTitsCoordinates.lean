module

public import ThirteenPlanes.WeylBasis
public import ThirteenPlanes.Tits.RealForm

@[expose] public section

set_option backward.privateInPublic true

open scoped BigOperators Matrix
open AlbertLean.Generic.C1Coordinates

namespace ThirteenPlanes

noncomputable section

/-- Assemble a grade from its two Weyl labels and its Tits component. -/
def chargeFrom (v : WeylLabel) (k : ZMod 3) : Charge := ![v.1, v.2, k]

@[simp] theorem chargeFrom_first (v : WeylLabel) (k : ZMod 3) :
    chargeFrom v k 0 = v.1 := rfl

@[simp] theorem chargeFrom_second (v : WeylLabel) (k : ZMod 3) :
    chargeFrom v k 1 = v.2 := rfl

@[simp] theorem chargeFrom_third (v : WeylLabel) (k : ZMod 3) :
    chargeFrom v k 2 = k := rfl

@[simp] theorem chargeFrom_components (x : Charge) :
    chargeFrom (x 0, x 1) (x 2) = x := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem chargeFrom_zero : chargeFrom 0 0 = 0 := by
  funext i
  fin_cases i <;> rfl

theorem chargeFrom_neg (v : WeylLabel) (k : ZMod 3) :
    chargeFrom (-v) (-k) = -chargeFrom v k := by
  funext i
  fin_cases i <;> rfl

theorem chargeFrom_add (v w : WeylLabel) (k l : ZMod 3) :
    chargeFrom (v+w) (k+l) = chargeFrom v k + chargeFrom w l := by
  funext i
  fin_cases i <;> rfl

def chargeComponentEquiv : ZMod 3 × WeylLabel ≃ Charge where
  toFun p := chargeFrom p.2 p.1
  invFun x := (x 2, x 0, x 1)
  left_inv := by rintro ⟨k,v⟩; cases v; rfl
  right_inv := chargeFrom_components

/-- Evaluate one of the three complex matrix coordinates by its charge. -/
def titsComponent (x : FirstTits ℂ) (k : ZMod 3) : Mat3 ℂ := ![x.1, x.2.1, x.2.2] k

theorem titsComponent_injective : Function.Injective
    (fun x : FirstTits ℂ => titsComponent x) := by
  intro x y h
  exact Prod.ext (congrFun h 0) (Prod.ext (congrFun h 1) (congrFun h 2))

private def componentCoefficients (k : ZMod 3) : (Charge → ℂ) →ₗ[ℂ] WeylLabel → ℂ where
  toFun z v := z (chargeFrom v k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def synthesisAt (k : ZMod 3) : (Charge → ℂ) →ₗ[ℂ] Mat3 ℂ :=
  weylSynthesis.comp (componentCoefficients k)

/-- Use the clock-and-shift basis separately in the three Tits components. -/
def gradedTitsCoordinates : (Charge → ℂ) →ₗ[ℂ] FirstTits ℂ :=
  (synthesisAt 0).prod ((synthesisAt 1).prod (synthesisAt 2))

@[simp] theorem titsComponent_gradedTitsCoordinates (z : Charge → ℂ) (k : ZMod 3) :
    titsComponent (gradedTitsCoordinates z) k = weylSynthesis (fun v => z (chargeFrom v k)) := by
  fin_cases k <;> rfl

/-- The 27 Weyl vectors give a complex linear coordinate equivalence. -/
def gradedTitsComplexEquiv : (Charge → ℂ) ≃ₗ[ℂ] FirstTits ℂ := by
  refine LinearEquiv.ofBijective gradedTitsCoordinates ⟨?_, ?_⟩
  · intro z w h
    funext x
    have hc (k : ZMod 3) := congrArg (fun y => titsComponent y k) h
    simp only [titsComponent_gradedTitsCoordinates] at hc
    have hf := congrFun (weylSynthesis_injective (hc (x 2))) (x 0, x 1)
    simpa only [chargeFrom_components] using hf
  · intro x
    let z : Charge → ℂ := fun a => weylBasisEquiv.symm (titsComponent x (a 2)) (a 0, a 1)
    refine ⟨z, titsComponent_injective (funext fun k => ?_)⟩
    change titsComponent (gradedTitsCoordinates z) k = titsComponent x k
    rw [titsComponent_gradedTitsCoordinates]
    have h : (fun v => z (chargeFrom v k)) = weylBasisEquiv.symm (titsComponent x k) := by
      funext v
      simp [z]
    rw [h]
    exact weylBasisEquiv.apply_symm_apply _

@[simp] theorem gradedTitsComplexEquiv_apply (z : Charge → ℂ) :
    gradedTitsComplexEquiv z = gradedTitsCoordinates z := rfl

theorem weylSynthesis_adjoint (z : WeylLabel → ℂ) :
    (weylSynthesis z)ᴴ = weylSynthesis (fun v => star (z (-v))) := by
  change (∑ v, z v • weylMatrix v)ᴴ = ∑ v, star (z (-v)) • weylMatrix v
  rw [Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_smul, weylMatrix_adjoint]
  simpa using Equiv.sum_comp (Equiv.neg WeylLabel) (fun v => star (z (-v)) • weylMatrix v)

theorem titsComponent_compactInvolution (x : FirstTits ℂ) (k : ZMod 3) :
    titsComponent (Tits.compactInvolution x) k = (titsComponent x (-k))ᴴ := by
  fin_cases k <;> rfl

/-- Compact conjugation negates the grade and conjugates its coefficient. -/
theorem compactInvolution_gradedTitsCoordinates (z : Charge → ℂ) :
    Tits.compactInvolution (gradedTitsCoordinates z) =
      gradedTitsCoordinates (fun x => star (z (-x))) := by
  apply titsComponent_injective
  funext k
  simp only [titsComponent_compactInvolution, titsComponent_gradedTitsCoordinates]
  change (weylSynthesis (fun v => z (chargeFrom v (-k))) : WeylMatrixSpace)ᴴ = _
  rw [weylSynthesis_adjoint]
  simp only [chargeFrom_neg]

theorem weylSynthesis_trace (z : WeylLabel → ℂ) :
    Matrix.trace (weylSynthesis z) = 3 * z 0 := by
  change Matrix.trace (∑ v, z v • weylMatrix v) = _
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_smul, weylMatrix_trace, smul_eq_mul, mul_ite, mul_zero]
  simp [mul_comm]

theorem gradedTitsCoordinates_trace (z : Charge → ℂ) :
    trace3 (gradedTitsCoordinates z).1 = 3 * z 0 := by
  change trace3 (titsComponent (gradedTitsCoordinates z) 0) = _
  rw [titsComponent_gradedTitsCoordinates]
  calc
    _ = Matrix.trace (weylSynthesis (fun v => z (chargeFrom v 0))) :=
      Tits.trace3_eq_matrixTrace _
    _ = _ := by rw [weylSynthesis_trace, chargeFrom_zero]

end

end ThirteenPlanes
