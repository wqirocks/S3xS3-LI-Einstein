import S3xS3.Trivial.MainTheorem
import S3xS3.Geometry.LeftInvariantGeometry

/-!
# Nontrivial inner isotropy of Einstein metrics on `SU(2) × SU(2)`

This is the public theorem file for the trivial-isotropy branch.  Its imported
modules formalize the graph-coordinate construction, the Ricci-to-Euler
bridge, positivity of the Einstein constant, both strict spectral barriers,
factor interchange with polar decompositions, the common-axis stabilizer, and
the final finite algebraic exclusion.
-/

namespace S3xS3.Trivial

/-- Every left-invariant Einstein metric on `SU(2) × SU(2)` has a nonidentity
inner isometry. -/
theorem einstein_implies_nontrivial_inner_isotropy
    (g : LeftInvariantMetric) :
    Einstein g → HasNontrivialInnerIsotropy g :=
  MainTheorem.einstein_has_nontrivial_inner_isotropy g

/-- The subgroup formulation of the same theorem: `K(g)` is not the trivial
subgroup of `SO(3) × SO(3)`. -/
theorem einstein_implies_innerIsotropy_ne_bot
    (g : LeftInvariantMetric) (hg : Einstein g) :
    innerIsotropy g ≠ ⊥ :=
  (hasNontrivialInnerIsotropy_iff g).mp
    (einstein_implies_nontrivial_inner_isotropy g hg)

end S3xS3.Trivial

namespace S3xS3.Geometry

open MatrixGroupLeftInvariantMetric

noncomputable section

/-- The literal inner-isometry group
`K(g) = Isom(SU(2) × SU(2), g) ∩ Inn(SU(2) × SU(2), g)`, expressed as
a subgroup of the actual range of conjugation in `MulAut MatrixS3xS3`. -/
abbrev K (g : MatrixGroupLeftInvariantMetric) := g.innerIsotropy

/-- **Theorem 1.1 (Automatic inner symmetry), on the concrete matrix group.**

Every left-invariant Einstein metric on Mathlib's matrix
`SU(2) × SU(2)` has nontrivial literal inner isotropy. -/
theorem theorem_1_1_automatic_inner_symmetry
    (g : MatrixGroupLeftInvariantMetric) :
    g.Einstein → K g ≠ ⊥ := by
  intro hg
  have hCoordinateEinstein :
      S3xS3.Einstein g.toCoordinateMetric :=
    (g.einstein_iff_coordinate).mp hg
  have hCoordinateNontrivial :
      S3xS3.HasNontrivialInnerIsotropy g.toCoordinateMetric :=
    S3xS3.Trivial.einstein_implies_nontrivial_inner_isotropy
      g.toCoordinateMetric hCoordinateEinstein
  exact (g.hasNontrivialInnerIsotropy_iff_coordinate).mpr
    hCoordinateNontrivial

end

end S3xS3.Geometry
