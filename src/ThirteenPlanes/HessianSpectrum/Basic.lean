module

public import ThirteenPlanes.MinimumHessian
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

@[expose] public section

/-! The coefficient pairing as a bilinear form, and the three Hessian subspaces.

`tensorPairing` is a positive definite symmetric bilinear form on `SymmetricCubic V`. For a cubic
`C` we name the three subspaces of the Hessian decomposition at a floor cubic:
* `rotationSpace C = {C.insert A : A skew-adjoint}` (the image of the infinitesimal action),
* `traceSpace = {τ*u : u ∈ V}` (the image of the trace adjoint),
* `complementSpace C`, the cubics orthogonal to both. -/

open scoped RealInnerProductSpace BigOperators

namespace ThirteenPlanes

noncomputable section

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace SymmetricCubic

/-- The coefficient pairing as a bilinear form. -/
def tpForm : LinearMap.BilinForm ℝ (SymmetricCubic V) :=
  LinearMap.mk₂ ℝ (fun g h => g.tensorPairing h)
    (fun g g' h => tensorPairing_add_left h g g')
    (fun a g h => by rw [tensorPairing_smul_left, smul_eq_mul])
    (fun g h h' => tensorPairing_add_right g h h')
    (fun a g h => by rw [tensorPairing_smul_right, smul_eq_mul])

@[simp] theorem tpForm_apply (g h : SymmetricCubic V) : tpForm g h = g.tensorPairing h := rfl

/-- `⟨h,h⟩` is the sum of the squared coefficients in any orthonormal basis. -/
theorem tensorPairing_self_eq_sum_sq {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)
    (h : SymmetricCubic V) :
    h.tensorPairing h = ∑ i, ∑ j, ∑ k, h.coefficient e i j k ^ 2 := by
  rw [tensorPairing_eq_sum e]; simp only [sq]

theorem tensorPairing_self_nonneg (h : SymmetricCubic V) : 0 ≤ h.tensorPairing h := by
  rw [tensorPairing_self_eq_sum_sq (stdOrthonormalBasis ℝ V)]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The coefficient pairing is positive definite.** -/
theorem tensorPairing_self_eq_zero_iff (h : SymmetricCubic V) : h.tensorPairing h = 0 ↔ h = 0 := by
  constructor
  · exact eq_zero_of_tensorPairing_self h
  · rintro rfl
    rw [tensorPairing_eq_sum (stdOrthonormalBasis ℝ V)]; simp [coefficient]

theorem tensorPairing_self_pos {h : SymmetricCubic V} (hh : h ≠ 0) : 0 < h.tensorPairing h :=
  lt_of_le_of_ne (tensorPairing_self_nonneg h) fun h0 => hh ((tensorPairing_self_eq_zero_iff h).mp h0.symm)

theorem tpForm_isRefl : (tpForm : LinearMap.BilinForm ℝ (SymmetricCubic V)).IsRefl :=
  fun g h hgh => by simpa [tensorPairing_comm] using hgh

theorem tensorPairing_sub_left (k g h : SymmetricCubic V) :
    (g - h).tensorPairing k = g.tensorPairing k - h.tensorPairing k := by
  rw [tensorPairing_comm, tensorPairing_sub_right, tensorPairing_comm k, tensorPairing_comm k]

theorem insert_add (C : SymmetricCubic V) (A B : V →ₗ[ℝ] V) :
    C.insert (A + B) = C.insert A + C.insert B := by
  apply ext; intro x y z
  simp only [apply_insert, apply_add, LinearMap.add_apply, apply_add₁, apply_add₂, apply_add₃]; ring

theorem insert_smul (C : SymmetricCubic V) (a : ℝ) (A : V →ₗ[ℝ] V) :
    C.insert (a • A) = a • C.insert A := by
  apply ext; intro x y z
  simp only [apply_insert, apply_smul, LinearMap.smul_apply, apply_smul₁, apply_smul₂, apply_smul₃]
  ring

end SymmetricCubic

variable (V) in
/-- The skew-adjoint endomorphisms of `V`. -/
def skewEnd : Submodule ℝ (V →ₗ[ℝ] V) where
  carrier := {A | IsSkew A}
  zero_mem' := fun x y => by simp
  add_mem' := fun {A B} hA hB x y => by
    simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hA x y, hB x y]; ring
  smul_mem' := fun a A hA x y => by
    simp only [LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right, hA x y]; ring

theorem mem_skewEnd {A : V →ₗ[ℝ] V} : A ∈ skewEnd V ↔ IsSkew A := Iff.rfl

/-- The infinitesimal action `A ↦ C.insert A` as a linear map. -/
def insertLin (C : SymmetricCubic V) : (V →ₗ[ℝ] V) →ₗ[ℝ] SymmetricCubic V where
  toFun A := C.insert A
  map_add' := C.insert_add
  map_smul' a A := C.insert_smul a A

@[simp] theorem insertLin_apply (C : SymmetricCubic V) (A : V →ₗ[ℝ] V) :
    insertLin C A = C.insert A := rfl

/-- The tangent space of the rotation orbit: `{C.insert A : A skew-adjoint}`. -/
def rotationSpace (C : SymmetricCubic V) : Submodule ℝ (SymmetricCubic V) :=
  (skewEnd V).map (insertLin C)

theorem mem_rotationSpace {C D : SymmetricCubic V} :
    D ∈ rotationSpace C ↔ ∃ A : V →ₗ[ℝ] V, IsSkew A ∧ C.insert A = D := by
  simp [rotationSpace, mem_skewEnd]

theorem traceAdjoint_add (u u' : V) :
    traceAdjoint (u + u') = traceAdjoint u + traceAdjoint u' := by
  apply ext; intro x y z
  simp only [traceAdjoint, apply_add, apply_ofProduct, LinearMap.mk₂_apply, real_inner_smul_left,
    inner_add_left, inner_add_right]
  ring

theorem traceAdjoint_smul (a : ℝ) (u : V) : traceAdjoint (a • u) = a • traceAdjoint u := by
  apply ext; intro x y z
  simp only [traceAdjoint, apply_smul, apply_ofProduct, LinearMap.mk₂_apply, real_inner_smul_left,
    inner_add_left, inner_smul_left]
  simp only [RCLike.conj_to_real]
  ring

/-- The trace adjoint `u ↦ τ*u` as a linear map. -/
def traceAdjointLin : V →ₗ[ℝ] SymmetricCubic V where
  toFun := traceAdjoint
  map_add' := traceAdjoint_add
  map_smul' := traceAdjoint_smul

@[simp] theorem traceAdjointLin_apply (u : V) : traceAdjointLin u = traceAdjoint u := rfl

variable (V) in
/-- The image of the trace adjoint, `{τ*u : u ∈ V}`. -/
def traceSpace : Submodule ℝ (SymmetricCubic V) := LinearMap.range (traceAdjointLin (V := V))

theorem mem_traceSpace {D : SymmetricCubic V} : D ∈ traceSpace V ↔ ∃ u : V, traceAdjoint u = D :=
  Iff.rfl

/-- The cubics orthogonal to every `τ*u` and to every infinitesimal rotation `C.insert A`. -/
def complementSpace (C : SymmetricCubic V) : Submodule ℝ (SymmetricCubic V) where
  carrier := {D | (∀ u : V, D.tensorPairing (traceAdjoint u) = 0) ∧
    ∀ A : V →ₗ[ℝ] V, IsSkew A → D.tensorPairing (C.insert A) = 0}
  zero_mem' := ⟨fun u => by simpa using tensorPairing_smul_left (traceAdjoint u) 0 0,
    fun A _ => by simpa using tensorPairing_smul_left (C.insert A) 0 0⟩
  add_mem' := fun {D D'} hD hD' =>
    ⟨fun u => by rw [tensorPairing_add_left, hD.1 u, hD'.1 u, add_zero],
      fun A hA => by rw [tensorPairing_add_left, hD.2 A hA, hD'.2 A hA, add_zero]⟩
  smul_mem' := fun a D hD =>
    ⟨fun u => by rw [tensorPairing_smul_left, hD.1 u, mul_zero],
      fun A hA => by rw [tensorPairing_smul_left, hD.2 A hA, mul_zero]⟩

theorem complementSpace_eq_orthogonal (C : SymmetricCubic V) :
    complementSpace C = LinearMap.BilinForm.orthogonal tpForm (rotationSpace C ⊔ traceSpace V) := by
  ext D
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, tpForm_apply]
  constructor
  · rintro ⟨hτ, hL⟩ X hX
    obtain ⟨r, hr, t, ht, rfl⟩ := Submodule.mem_sup.mp hX
    obtain ⟨A, hA, rfl⟩ := mem_rotationSpace.mp hr
    obtain ⟨u, rfl⟩ := mem_traceSpace.mp ht
    rw [tensorPairing_add_left, tensorPairing_comm, hL A hA, tensorPairing_comm, hτ u, add_zero]
  · intro h
    refine ⟨fun u => ?_, fun A hA => ?_⟩
    · rw [tensorPairing_comm]
      exact h _ (Submodule.mem_sup_right (mem_traceSpace.mpr ⟨u, rfl⟩))
    · rw [tensorPairing_comm]
      exact h _ (Submodule.mem_sup_left (mem_rotationSpace.mpr ⟨A, hA, rfl⟩))

end

end ThirteenPlanes
