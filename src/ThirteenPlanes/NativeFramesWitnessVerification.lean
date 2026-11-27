/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.NativeFramesWitnessAlgebra

/-!
# Soundness of finite exact-coordinate reference checks

Closed computable coefficient propositions transfer to the ORIGINAL native
Frame and trace-pairing equations through the proved evaluation homomorphism.
-/

@[expose] public section

namespace ThirteenPlanes.NativeWitness.ExactVerification

open ExactAlgebra

/-- Only literal coefficient equations, with finite and computable quantifiers. -/
def ExactFrame (p : Fin 3 → Element) : Prop :=
  (∀ i, trace (p i) = rational 1) ∧
  (∀ i, jordan (p i) (p i) = p i) ∧
  (∀ i j, i ≠ j → jordan (p i) (p j) = 0) ∧
  (p 0+p 1+p 2 = 1)

/-- A kernel-checked exact frame is a literal native compact Albert frame. -/
theorem native_frame (p : Fin 3 → Element) (hp : ExactFrame p) :
    Glennie.Frame (fun i => evaluateElement (p i)) := by
  rcases hp with ⟨ht,hm,ho,hs⟩
  constructor
  · intro i
    rw [← evaluate_trace,ht,evaluate_rational]
    norm_num
  · intro i
    rw [← evaluate_jordan,hm]
  · intro i j hij
    rw [← evaluate_jordan,ho i j hij,evaluateElement_zero]
  · rw [← evaluateElement_add,← evaluateElement_add,hs,evaluateElement_one]

/-- Exact coefficient pairing checks evaluate to actual native readouts. -/
theorem native_pairing (x y : Element) (q : ℚ) (h : inner x y = rational q) :
    Glennie.inner (evaluateElement x) (evaluateElement y) = (q : ℝ) := by
  rw [← evaluate_inner,h,evaluate_rational]

end ThirteenPlanes.NativeWitness.ExactVerification
