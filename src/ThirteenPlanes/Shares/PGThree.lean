module

public import ThirteenPlanes.Shares.AffineQuartetChart
public import Mathlib.Tactic.DeriveFintype

@[expose] public section

namespace ThirteenPlanes.RoundCubics

/-- Points of PG(2,3) in the usual affine chart with four points at infinity. -/
inductive PGThreePoint
  | affine (x y : ZMod 3)
  | rowInfinity
  | colInfinity
  | slopeInfinity (positive : Bool)
  deriving DecidableEq, Fintype

/-- Lines of PG(2,3) in affine coordinates over the field of three elements. -/
inductive PGThreeLine
  | infinity
  | row (x : ZMod 3)
  | col (y : ZMod 3)
  | slope (positive : Bool) (offset : ZMod 3)
  deriving DecidableEq, Fintype

/-- Incidence in the affine chart and on its line at infinity. -/
def pgThreeIncidence : PGThreePoint → PGThreeLine → Prop
  | .affine _ _, .infinity => False
  | .affine x _, .row a => x = a
  | .affine _ y, .col b => y = b
  | .affine x y, .slope s b => y = quartetSlope s x + b
  | _, .infinity => True
  | .rowInfinity, .row _ => True
  | .colInfinity, .col _ => True
  | .slopeInfinity s, .slope t _ => s = t
  | _, _ => False

instance (p : PGThreePoint) (L : PGThreeLine) : Decidable (pgThreeIncidence p L) := by
  cases p <;> cases L <;> unfold pgThreeIncidence <;> infer_instance

/-- Homogeneous point representatives, with the last available coordinate normalized to one. -/
def PGThreePoint.coords : PGThreePoint → ZMod 3 × ZMod 3 × ZMod 3
  | .affine x y => (x, y, 1)
  | .rowInfinity => (0, 1, 0)
  | .colInfinity => (1, 0, 0)
  | .slopeInfinity s => (1, quartetSlope s 1, 0)

/-- Homogeneous representatives of the line covectors. -/
def PGThreeLine.coords : PGThreeLine → ZMod 3 × ZMod 3 × ZMod 3
  | .infinity => (0, 0, 1)
  | .row a => (1, 0, -a)
  | .col b => (0, 1, -b)
  | .slope s b => (-quartetSlope s 1, 1, -b)

theorem pgThreeIncidence_iff_pairing_zero :
    ∀ p L, pgThreeIncidence p L ↔
      L.coords.1 * p.coords.1 + L.coords.2.1 * p.coords.2.1 + L.coords.2.2 * p.coords.2.2 = 0 := by
  decide

theorem pgThreePoint_coords_represent :
    ∀ x y z : ZMod 3, (x, y, z) ≠ (0, 0, 0) →
      ∃ p : PGThreePoint, ∃ r : ZMod 3, r ≠ 0 ∧
        p.coords = (r * x, r * y, r * z) := by
  decide

theorem pgThreeLine_coords_represent :
    ∀ a b d : ZMod 3, (a, b, d) ≠ (0, 0, 0) →
      ∃ L : PGThreeLine, ∃ r : ZMod 3, r ≠ 0 ∧
        L.coords = (r * a, r * b, r * d) := by
  decide

theorem pgThreePoint_coords_proportional_iff :
    ∀ p q : PGThreePoint, (∃ r : ZMod 3, r ≠ 0 ∧
      p.coords = (r * q.coords.1, r * q.coords.2.1, r * q.coords.2.2)) ↔ p = q := by
  decide

theorem pgThreeLine_coords_proportional_iff :
    ∀ B D : PGThreeLine, (∃ r : ZMod 3, r ≠ 0 ∧
      B.coords = (r * D.coords.1, r * D.coords.2.1, r * D.coords.2.2)) ↔ B = D := by
  decide

theorem pgThreePoint_card : Fintype.card PGThreePoint = 13 := by decide

theorem pgThreeLine_card : Fintype.card PGThreeLine = 13 := by decide

set_option maxRecDepth 10000 in
theorem pgThreeLine_eq_of_incidence :
    ∀ B D : PGThreeLine, (∀ p : PGThreePoint, pgThreeIncidence p B ↔ pgThreeIncidence p D) → B = D := by
  decide

set_option maxRecDepth 10000 in
theorem pgThree_pair_has_line :
    ∀ p q : PGThreePoint, p ≠ q → ∃ L : PGThreeLine, pgThreeIncidence p L ∧ pgThreeIncidence q L := by
  decide

end ThirteenPlanes.RoundCubics
