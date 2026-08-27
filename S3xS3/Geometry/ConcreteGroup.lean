import S3xS3.Geometry.LieAlgebra

open scoped Matrix

/-!
# The concrete group `SU(2) × SU(2)` and its inner automorphisms

Here `SU(2)` is Mathlib's `2 × 2` complex special-unitary matrix group.
We transport the already explicit quaternion adjoint map through the proved
matrix/quaternion isomorphism and identify its kernel with the center.  We
also identify the literal range of conjugation in `MulAut` with the
`SO(3) × SO(3)` group acting in the coordinate proof.
-/

namespace S3xS3.Geometry

noncomputable section

/-- Mathlib's matrix `SU(2) × SU(2)`. -/
abbrev MatrixS3xS3 := MatrixSU2 × MatrixSU2

/-- The componentwise, explicitly proved group isomorphism from unit
quaternions to matrix `SU(2)`. -/
def quaternionProductEquivMatrixS3xS3 : QuaternionS3xS3 ≃* MatrixS3xS3 :=
  MulEquiv.prodCongr quaternionSU2EquivMatrixSU2 quaternionSU2EquivMatrixSU2

/-- The adjoint homomorphism of the concrete matrix group, transported
through the explicit quaternion/matrix isomorphism. -/
def matrixS3xS3Adjoint : MatrixS3xS3 →* InnerAction :=
  s3xS3Adjoint.comp quaternionProductEquivMatrixS3xS3.symm.toMonoidHom

theorem matrixS3xS3Adjoint_surjective :
    Function.Surjective matrixS3xS3Adjoint := by
  intro a
  obtain ⟨q, hq⟩ := s3xS3Adjoint_surjective a
  refine ⟨quaternionProductEquivMatrixS3xS3 q, ?_⟩
  simpa [matrixS3xS3Adjoint] using hq

/-- A group isomorphism preserves and reflects membership in the center. -/
lemma quaternionProduct_center_iff_matrixProduct_center
    (q : QuaternionS3xS3) :
    q ∈ Subgroup.center QuaternionS3xS3 ↔
      quaternionProductEquivMatrixS3xS3 q ∈
        Subgroup.center MatrixS3xS3 := by
  constructor
  · intro hq
    rw [Subgroup.mem_center_iff]
    intro U
    let r := quaternionProductEquivMatrixS3xS3.symm U
    have hr := Subgroup.mem_center_iff.mp hq r
    simpa [r] using congrArg quaternionProductEquivMatrixS3xS3 hr
  · intro hq
    rw [Subgroup.mem_center_iff]
    intro r
    have hr := Subgroup.mem_center_iff.mp hq
      (quaternionProductEquivMatrixS3xS3 r)
    exact quaternionProductEquivMatrixS3xS3.injective (by simpa using hr)

/-- The kernel of the adjoint representation of the concrete matrix product
is exactly its center. -/
theorem matrixS3xS3_center_eq_adjoint_ker :
    Subgroup.center MatrixS3xS3 = MonoidHom.ker matrixS3xS3Adjoint := by
  ext U
  let q : QuaternionS3xS3 := quaternionProductEquivMatrixS3xS3.symm U
  have hUq : quaternionProductEquivMatrixS3xS3 q = U := by simp [q]
  constructor
  · intro hcenter
    have hqcenter : q ∈ Subgroup.center QuaternionS3xS3 := by
      rw [quaternionProduct_center_iff_matrixProduct_center, hUq]
      exact hcenter
    have hqker : q ∈ MonoidHom.ker s3xS3Adjoint := by
      rw [← s3xS3_center_eq_adjoint_ker]
      exact hqcenter
    rw [MonoidHom.mem_ker] at hqker ⊢
    simpa [matrixS3xS3Adjoint, q] using hqker
  · intro hker
    have hqker : q ∈ MonoidHom.ker s3xS3Adjoint := by
      rw [MonoidHom.mem_ker]
      rw [MonoidHom.mem_ker] at hker
      simpa [matrixS3xS3Adjoint, q] using hker
    have hqcenter : q ∈ Subgroup.center QuaternionS3xS3 := by
      rw [s3xS3_center_eq_adjoint_ker]
      exact hqker
    rw [← hUq, ← quaternionProduct_center_iff_matrixProduct_center]
    exact hqcenter

/-- For every group, the kernel of conjugation is its center. -/
theorem conjugation_ker_eq_center (G : Type*) [Group G] :
    MonoidHom.ker (MulAut.conj : G →* MulAut G) = Subgroup.center G := by
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_center_iff]
    intro r
    have hr := DFunLike.congr_fun hg r
    change g * r * g⁻¹ = r at hr
    exact (mul_inv_eq_iff_eq_mul.mp hr).symm
  · intro hg
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro r
    change g * r * g⁻¹ = r
    have hr := Subgroup.mem_center_iff.mp hg r
    rw [← hr, mul_assoc, mul_inv_cancel, mul_one]

/-- The quotient-by-center presentation of the concrete inner-automorphism
group. -/
abbrev MatrixS3xS3InnQuotient :=
  MatrixS3xS3 ⧸ Subgroup.center MatrixS3xS3

/-- The effective inner action of the matrix group is precisely the block
`SO(3) × SO(3)` action used in the coordinate formalization. -/
def matrixS3xS3InnQuotientEquivInnerAction :
    MatrixS3xS3InnQuotient ≃* InnerAction :=
  (QuotientGroup.quotientMulEquivOfEq matrixS3xS3_center_eq_adjoint_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective matrixS3xS3Adjoint
      matrixS3xS3Adjoint_surjective)

/-- The literal subgroup of `MulAut (SU(2) × SU(2))` consisting of
conjugations. -/
abbrev MatrixS3xS3InnerAutomorphismGroup :=
  MonoidHom.range (MulAut.conj : MatrixS3xS3 →* MulAut MatrixS3xS3)

/-- Conjugation by a specified matrix-group element, regarded as an element
of the literal inner-automorphism group. -/
def matrixS3xS3ConjugationRangeElement (U : MatrixS3xS3) :
    MatrixS3xS3InnerAutomorphismGroup :=
  ⟨MulAut.conj U, ⟨U, rfl⟩⟩

/-- Quotient by the center agrees with the literal range of conjugation. -/
def matrixS3xS3InnQuotientEquivConjugationRange :
    MatrixS3xS3InnQuotient ≃* MatrixS3xS3InnerAutomorphismGroup :=
  (QuotientGroup.quotientMulEquivOfEq
      (conjugation_ker_eq_center MatrixS3xS3).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (MulAut.conj : MatrixS3xS3 →* MulAut MatrixS3xS3))

/-- The literal inner-automorphism group of matrix
`SU(2) × SU(2)` is isomorphic to `SO(3) × SO(3)`. -/
def matrixS3xS3InnerAutomorphismEquivInnerAction :
    MatrixS3xS3InnerAutomorphismGroup ≃* InnerAction :=
  matrixS3xS3InnQuotientEquivConjugationRange.symm.trans
    matrixS3xS3InnQuotientEquivInnerAction

/-- The identification of literal conjugations with `SO(3) × SO(3)`
commutes with the adjoint homomorphism of the concrete matrix group. -/
@[simp] theorem
    matrixS3xS3InnerAutomorphismEquivInnerAction_conjugationRangeElement
    (U : MatrixS3xS3) :
    matrixS3xS3InnerAutomorphismEquivInnerAction
        (matrixS3xS3ConjugationRangeElement U) =
      matrixS3xS3Adjoint U := by
  change (QuotientGroup.quotientKerEquivOfSurjective matrixS3xS3Adjoint
      matrixS3xS3Adjoint_surjective)
    ((QuotientGroup.quotientMulEquivOfEq
        matrixS3xS3_center_eq_adjoint_ker)
      ((QuotientGroup.quotientMulEquivOfEq
          (conjugation_ker_eq_center MatrixS3xS3).symm).symm
        ((QuotientGroup.quotientKerEquivRange
          (MulAut.conj : MatrixS3xS3 →* MulAut MatrixS3xS3)).symm
          (matrixS3xS3ConjugationRangeElement U)))) =
    matrixS3xS3Adjoint U
  have hrange :
      (QuotientGroup.quotientKerEquivRange
          (MulAut.conj : MatrixS3xS3 →* MulAut MatrixS3xS3)).symm
          (matrixS3xS3ConjugationRangeElement U) =
        QuotientGroup.mk U := by
    apply (QuotientGroup.quotientKerEquivRange
      (MulAut.conj : MatrixS3xS3 →* MulAut MatrixS3xS3)).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rfl
  rw [hrange]
  rfl

/-- The derivative of conjugation by a matrix-group element on the transported
quaternionic Lie algebra. -/
def matrixS3xS3ConjugationDerivative (U : MatrixS3xS3)
    (x : QuaternionS3xS3LieAlgebra) : QuaternionS3xS3LieAlgebra :=
  quaternionProductConjugationDerivative
    (quaternionProductEquivMatrixS3xS3.symm U) x

/-- Coordinate equivariance of the derivative of actual matrix-group
conjugation. -/
theorem matrixS3xS3ConjugationDerivative_equivariant
    (U : MatrixS3xS3) (x : LieVec) :
    matrixS3xS3ConjugationDerivative U
      (lieVecEquivQuaternionProduct x) =
    lieVecEquivQuaternionProduct
      (innerMatrix (matrixS3xS3Adjoint U) *ᵥ x) := by
  exact quaternionProductConjugationDerivative_equivariant
    (quaternionProductEquivMatrixS3xS3.symm U) x

end

end S3xS3.Geometry
