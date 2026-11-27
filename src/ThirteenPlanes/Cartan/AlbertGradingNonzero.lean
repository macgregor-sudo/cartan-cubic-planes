module

public import ThirteenPlanes.AlbertGrading.Grading.CharacterSpaces
public import ThirteenPlanes.Cartan.DerivationGradingCore

@[expose] public section

set_option backward.privateInPublic true

/-! Products of normalized characters on distinct projective points are nonzero. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading AlbertGrading.Grading.JC

noncomputable section

theorem normalized_opposite_ip {u : JC} (hu : IsNormalized u) : ip u (conj u) = 3 := by
  calc
    _ = ip (mul u (conj u)) one := by rw [ip_mul_assoc, mul_one]
    _ = 3 := by rw [hu.2, ip_one_one]

private theorem eq_zero_of_ip_conj_eq_zero (z : JC) (h : ip z (conj z) = 0) : z = 0 := by
  have H := congrArg Complex.re (ip_conj_self z)
  rw [h, Complex.zero_re, Complex.ofReal_re] at H
  have hr := Glennie.inner_self_nonneg z.re
  have hi := Glennie.inner_self_nonneg z.im
  have hR : Glennie.inner z.re z.re = 0 := by linarith only [H, hr, hi]
  have hI : Glennie.inner z.im z.im = 0 := by linarith only [H, hr, hi]
  exact JC.ext ((Glennie.inner_self_eq_zero _).mp hR) ((Glennie.inner_self_eq_zero _).mp hI)

set_option maxHeartbeats 700000 in
/-- If a product of two normalized character fields on distinct projective points vanished,
the quartic identity would force the conjugate product to vanish as well, contradicting the
same identity on the two opposite pairs. -/
theorem albert_normalized_independent_product {ρ : TernaryAction} (hρ : IsTernaryGrading ρ)
    {g h : Charge} {u v : JC} (hg : g ≠ 0) (hh : h ≠ 0) (hne : h ≠ g) (hopp : h ≠ -g)
    (hu : u ∈ charSpace ρ g) (hv : v ∈ charSpace ρ h) (hun : IsNormalized u) (hvn : IsNormalized v) :
    mul u v ≠ 0 := by
  have hsum : g + h ≠ 0 := fun hz => hopp (eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hz))
  have hdiff : -g + h ≠ 0 := by simpa only [add_comm, sub_eq_add_neg] using sub_ne_zero.mpr hne
  have hdiff' : g + -h ≠ 0 := by simpa only [sub_eq_add_neg] using sub_ne_zero.mpr hne.symm
  have hsum' : -g + -h ≠ 0 := by rw [← neg_add]; exact neg_ne_zero.mpr hsum
  have hnegG : -g ≠ 0 := neg_ne_zero.mpr hg
  have hnegH : -h ≠ 0 := neg_ne_zero.mpr hh
  have hub := conj_mem_charSpace hu
  have hvb := conj_mem_charSpace hv
  have htu := tr_eq_zero_of_mem hρ hg hu
  have htv := tr_eq_zero_of_mem hρ hh hv
  have htub := tr_eq_zero_of_mem hρ hnegG hub
  have htvb := tr_eq_zero_of_mem hρ hnegH hvb
  have hself : ip u u = 0 := ip_eq_zero_of_charSpace hρ hu hu
    (by rw [NormalizedTernaryBasis.charge_double_eq_neg]; exact hnegG)
  have huv : ip u v = 0 := ip_eq_zero_of_charSpace hρ hu hv hsum
  have huv' : ip u (conj v) = 0 := ip_eq_zero_of_charSpace hρ hu hvb hdiff'
  have huv'' : ip (conj u) v = 0 := ip_eq_zero_of_charSpace hρ hub hv hdiff
  have huv''' : ip (conj u) (conj v) = 0 := ip_eq_zero_of_charSpace hρ hub hvb hsum'
  intro hz
  let w := mul (conj u) v
  have hw := mul_mem_charSpace hρ hub hv
  have htw : tr (conj w) = 0 := tr_eq_zero_of_mem hρ (neg_ne_zero.mpr hdiff) (conj_mem_charSpace hw)
  have hq := quartic_eq_zero u u v (conj w) htu htu htv htw
  have hp : ip w (conj w) = 0 := by
    calc
      _ = ip (mul u u) (mul v (conj w)) := by
        rw [hun.1]
        exact ip_mul_assoc (conj u) v (conj w)
      _ = 0 := by
        simpa only [quartic, hz, ip_zero_left, ip_zero_right, hself, huv, zero_mul, mul_zero,
          zero_add, add_zero, zero_div, sub_zero] using hq
  have hw0 : w = 0 := eq_zero_of_ip_conj_eq_zero w hp
  have hbar : mul u (conj v) = 0 := by
    have he := congrArg (fun z : JC => conj z) hw0
    simpa only [w, conj_mul, conj_conj, conj_zero] using he
  have hq' := quartic_eq_zero u (conj u) v (conj v) htu htub htv htvb
  simp only [quartic, hun.2, hvn.2, hz, hbar, huv, huv', huv'', huv''', ip_one_one,
    normalized_opposite_ip hun, normalized_opposite_ip hvn, ip_zero_left, zero_mul, zero_add, add_zero] at hq'
  norm_num at hq'

end

end ThirteenPlanes.Cartan
