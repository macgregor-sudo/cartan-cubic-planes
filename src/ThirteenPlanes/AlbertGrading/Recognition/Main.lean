module

public import ThirteenPlanes.AlbertGrading.Recognition.Normalization

@[expose] public section

/-! Recognition and classification of sparse graded systems.

`recognition` identifies a system from the reference quartet and exterior frame.
`sparsest` uses ordered unbiased-pair normalization in the compact first Tits model,
which follows from the octonionic normal form of the unbiased-pair and slot normal forms (i). -/

namespace ThirteenPlanes.AlbertGrading

/-- Recognition of systems with 52 positive shares, from the unbiased-pair and slot normal forms (i) for the octonions. -/
theorem sparsest (h3 : FrameProperties.NormalFormOctonion) : Statements.Sparsest :=
  sparsest_of_pairNormalization (pairNormalization_of_normalForm h3)

end ThirteenPlanes.AlbertGrading
