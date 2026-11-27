module

public import ThirteenPlanes.SphereMoments.Average
public import ThirteenPlanes.SphereMoments.Tensor
public import ThirteenPlanes.SphereMoments.Energy

@[expose] public section

/-!
# Isotropic moments on the unit sphere

* `SphereMoments.Gaussian`: Stein identity and Wick formula for the weight `exp (-‖x‖²)`.
* `SphereMoments.Polar`: polar coordinates for homogeneous functions.
* `SphereMoments.Average`: `sphereAverage`, `sphereVariance`, moments of products of linear forms.
* `SphereMoments.Pairings`, `SphereMoments.Tensor`: averages of quadratic and quartic forms.
* `SphereMoments.Energy`: mean and variance of the field energy of a symmetric cubic.

Everything except `Energy` uses Mathlib only; `Energy` imports `ThirteenPlanes.Cubic`.
-/
