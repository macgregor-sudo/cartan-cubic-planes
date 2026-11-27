module

public import ThirteenPlanes.AlbertGrading.Grading.Phases

@[expose] public section

/-! # the contradiction -/

namespace ThirteenPlanes.AlbertGrading.Grading

open JC

noncomputable section

variable {ρ : TernaryAction}

theorem pointOf_neg {k : Charge} (hk : k ≠ 0) : pointOf (neg_ne_zero.mpr hk) = pointOf hk := by
  have h1 := pointOf_rep hk
  have h2 := pointOf_rep (neg_ne_zero.mpr hk)
  rw [neg_neg] at h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h2.trans (by rw [h1])) (rep_ne_neg _ _)
  · exact rep_injective (h2.trans h1.symm)
  · exact rep_injective (h2.trans h1.symm)
  · exact absurd (h2.trans (by rw [h1, neg_neg])) (rep_ne_neg _ _)

section Main

variable (hρ : IsTernaryGrading ρ) (ψ : SignedPlaneIndex → (ℂ →ₗ[ℝ] NativeTraceless))
  (hψP : ∀ p ζ, ψ p ζ ∈ pointPlane ρ p)
  (hnorm : ∀ ζ : SignedPlaneIndex → ℂ, ‖∑ p, ψ p (ζ p)‖ ^ 2 = ∑ p, ‖ζ p‖ ^ 2)
include hρ hψP hnorm

theorem basisElt_mem {k : Charge} (hk : k ≠ 0) : basisElt (ρ := ρ) ψ k ∈ charSpace ρ k := by
  obtain ⟨θ, n, hn, -, he, -⟩ := basisElt_spec hρ ψ hψP hnorm hk
  rw [he]; exact Submodule.smul_mem _ _ hn

theorem basisElt_ne_zero {k : Charge} (hk : k ≠ 0) : basisElt (ρ := ρ) ψ k ≠ 0 := by
  obtain ⟨θ, n, -, hnn, he, hθ⟩ := basisElt_spec hρ ψ hψP hnorm hk
  rw [he]
  refine smul_ne_zero ?_ (ne_zero_of_normalized hnn)
  intro h; rw [h] at hθ; simp at hθ; norm_num at hθ

theorem basisElt_ip {k : Charge} (hk : k ≠ 0) :
    ip (basisElt (ρ := ρ) ψ k) (conj (basisElt (ρ := ρ) ψ k)) = 2 := by
  obtain ⟨θ, n, -, hnn, he, hθ⟩ := basisElt_spec hρ ψ hψP hnorm hk
  rw [he, conj_smul, ip_smul_left, ip_smul_right, ip_conj_normalized hnn, ← mul_assoc, hθ]
  norm_num

theorem basisElt_cases {k : Charge} (hk : k ≠ 0) :
    (basisElt (ρ := ρ) ψ k = coordElt ψ (pointOf hk) ∧ coordElt ψ (pointOf hk) ∈ charSpace ρ k) ∨
    (basisElt (ρ := ρ) ψ k = conj (coordElt ψ (pointOf hk)) ∧
      coordElt ψ (pointOf hk) ∈ charSpace ρ (-k)) := by
  have hm := basisElt_mem hρ ψ hψP hnorm hk
  unfold basisElt at hm ⊢
  rw [dif_neg hk] at hm ⊢
  split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · rw [if_neg h] at hm
    exact Or.inr ⟨rfl, mem_charSpace_conj_iff.mp hm⟩

theorem basisElt_neg {k : Charge} (hk : k ≠ 0) :
    basisElt (ρ := ρ) ψ (-k) = conj (basisElt (ρ := ρ) ψ k) := by
  have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
  have hne : k ≠ -k := fun h => charge_neg_ne_self hk h.symm
  have hp := pointOf_neg hk
  have h0 := basisElt_ne_zero hρ ψ hψP hnorm hk
  rcases basisElt_cases hρ ψ hψP hnorm hk with ⟨e1, m1⟩ | ⟨e1, m1⟩ <;>
    rcases basisElt_cases hρ ψ hψP hnorm hk' with ⟨e2, m2⟩ | ⟨e2, m2⟩ <;>
    rw [hp] at e2 m2 <;> rw [e1, e2]
  · exact absurd (charSpace_disjoint hne m1 m2) (by rw [← e1]; exact h0)
  · rw [conj_conj]
  · rw [neg_neg] at m2
    exact absurd (charSpace_disjoint hne m2 m1) (fun h => h0 (by rw [e1, h, conj_zero]))

theorem of_psi_basis {k : Charge} (hk : k ≠ 0) :
    ∃ σ : ℂ → ℂ, (∀ ζ, σ (star ζ) = star (σ ζ)) ∧ σ 1 = 1 ∧ (∃ ζ, σ ζ = Complex.I) ∧
      ∀ ζ, of (ψ (pointOf hk) ζ : Glennie.Albert) =
        (1 / 2 : ℂ) • (σ ζ • basisElt (ρ := ρ) ψ k + star (σ ζ) • conj (basisElt (ρ := ρ) ψ k)) := by
  rcases basisElt_cases hρ ψ hψP hnorm hk with ⟨e, -⟩ | ⟨e, -⟩
  · refine ⟨id, fun _ => rfl, rfl, ⟨Complex.I, rfl⟩, fun ζ => ?_⟩
    rw [e, of_psi]; rfl
  · refine ⟨star, fun _ => rfl, star_one ℂ, ⟨-Complex.I, by simp⟩, fun ζ => ?_⟩
    rw [e, of_psi, conj_conj, star_star, add_comm]

/-- The structure constant of the basis has square `1/6`. -/
theorem basis_constant {g h : Charge} (hg : g ≠ 0) (hh : h ≠ 0) (h₁ : g + h ≠ 0) (h₂ : g - h ≠ 0) :
    ∃ K : ℂ, mul (basisElt (ρ := ρ) ψ g) (basisElt (ρ := ρ) ψ h) = K • basisElt (ρ := ρ) ψ (g + h) ∧
      K * star K = 1 / 6 := by
  obtain ⟨θ₁, n₁, hn₁, hnn₁, e₁, hθ₁⟩ := basisElt_spec hρ ψ hψP hnorm hg
  obtain ⟨θ₂, n₂, hn₂, hnn₂, e₂, hθ₂⟩ := basisElt_spec hρ ψ hψP hnorm hh
  obtain ⟨θ₃, n₃, hn₃, hnn₃, e₃, hθ₃⟩ := basisElt_spec hρ ψ hψP hnorm h₁
  obtain ⟨κ, hκ, hκκ⟩ := structure_constant hρ hg hh h₁ h₂ hn₁ hnn₁ hn₂ hnn₂ hn₃ hnn₃
  have hθ₃0 : θ₃ ≠ 0 := by intro h; rw [h] at hθ₃; simp at hθ₃; norm_num at hθ₃
  refine ⟨θ₁ * θ₂ * κ / θ₃, ?_, ?_⟩
  · rw [e₁, e₂, e₃, mul_smul_left, mul_smul_right, hκ, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp
  · have hs : star (θ₁ * θ₂ * κ / θ₃) = star θ₁ * star θ₂ * star κ / star θ₃ := by
      rw [star_div₀, star_mul', star_mul']
    rw [hs, div_mul_div_comm, show θ₁ * θ₂ * κ * (star θ₁ * star θ₂ * star κ) =
      (θ₁ * star θ₁) * (θ₂ * star θ₂) * (κ * star κ) by ring, hθ₁, hθ₂, hκκ, hθ₃]
    norm_num

end Main

end

end ThirteenPlanes.AlbertGrading.Grading
