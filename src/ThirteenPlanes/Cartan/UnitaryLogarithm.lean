module

public import ThirteenPlanes.Cartan.ComplexDiagonalization
public import ThirteenPlanes.Cartan.UnitaryLogarithmCore

@[expose] public section

/-! Exact traceless skew-Hermitian logarithms of special unitary matrices. -/

namespace ThirteenPlanes.Cartan

open NormedSpace

/-- Every special unitary three-by-three matrix has a traceless skew-Hermitian logarithm. -/
theorem suThree_exists_traceless_skew_log (U : ComplexSpecialUnitary3) :
    ∃ A : complexSkewTracelessMatrices, exp A.val = U.val :=
  suThree_exists_traceless_skew_log_of_pair_diagonalization complexSkew_simultaneousDiagonalization U

end ThirteenPlanes.Cartan
