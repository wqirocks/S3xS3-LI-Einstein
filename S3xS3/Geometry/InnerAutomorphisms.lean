import S3xS3.Geometry.QuaternionRotation

open scoped Matrix BigOperators

namespace S3xS3.Geometry

open Quaternion

noncomputable section

private def quaternionI : QuaternionSU2 :=
  quaternionSU2OfNormSqOne ⟨0, 1, 0, 0⟩ (by
    simp [Quaternion.normSq_def'])

private def quaternionJ : QuaternionSU2 :=
  quaternionSU2OfNormSqOne ⟨0, 0, 1, 0⟩ (by
    simp [Quaternion.normSq_def'])

/-- The center of the unit-quaternion model of `SU(2)` is precisely the
kernel of its adjoint action on the imaginary quaternions. -/
theorem quaternion_center_eq_adjoint_ker :
    Subgroup.center QuaternionSU2 = MonoidHom.ker quaternionAdjoint := by
  ext q
  constructor
  · intro hq
    have hi := (Subgroup.mem_center_iff.mp hq) quaternionI
    have hj := (Subgroup.mem_center_iff.mp hq) quaternionJ
    have hi' := congrArg Subtype.val hi
    have hj' := congrArg Subtype.val hj
    have hic := congrArg (fun x : ℍ ↦ x.imJ) hi'
    have hid := congrArg (fun x : ℍ ↦ x.imK) hi'
    have hib := congrArg (fun x : ℍ ↦ x.imK) hj'
    simp [quaternionI, quaternionJ, quaternionSU2OfNormSqOne,
      Quaternion.imJ_mul, Quaternion.imK_mul] at hic hid hib
    have hb : (q : ℍ).imI = 0 := by nlinarith
    have hc : (q : ℍ).imJ = 0 := by nlinarith
    have hd : (q : ℍ).imK = 0 := by nlinarith
    have hn := quaternionSU2_normSq q
    rw [Quaternion.normSq_def', hb, hc, hd] at hn
    norm_num at hn
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quaternionAdjoint, quaternionRotationMatrix, hb, hc, hd, hn]
  · intro hq
    rw [MonoidHom.mem_ker] at hq
    have hm := congrArg Subtype.val hq
    have h00 := congrArg (fun A : Mat3 ↦ A 0 0) hm
    have h11 := congrArg (fun A : Mat3 ↦ A 1 1) hm
    simp [quaternionAdjoint, quaternionRotationMatrix] at h00 h11
    have hn := quaternionSU2_normSq q
    rw [Quaternion.normSq_def'] at hn
    have hc : (q : ℍ).imJ = 0 := by
      nlinarith [sq_nonneg (q : ℍ).imJ, sq_nonneg (q : ℍ).imK]
    have hd : (q : ℍ).imK = 0 := by
      nlinarith [sq_nonneg (q : ℍ).imJ, sq_nonneg (q : ℍ).imK]
    have hb : (q : ℍ).imI = 0 := by
      nlinarith [sq_nonneg (q : ℍ).imI]
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    ext <;>
      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, hb, hc, hd] <;>
      ring

/-- The effective inner-automorphism group of the unit-quaternion `SU(2)`
model, presented canonically as `SU(2)` modulo its center. -/
abbrev QuaternionInn := QuaternionSU2 ⧸ Subgroup.center QuaternionSU2

/-- `Inn(SU(2)) ≃ SO(3)`, obtained from the explicit surjective adjoint
homomorphism and its rigorously identified kernel. -/
def quaternionInnEquivSO3 : QuaternionInn ≃* SO3 :=
  (QuotientGroup.quotientMulEquivOfEq quaternion_center_eq_adjoint_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective quaternionAdjoint
      quaternionAdjoint_surjective)

/-- The actual subgroup of multiplicative automorphisms arising by
conjugation. -/
abbrev QuaternionInnerAutomorphismGroup :=
  MonoidHom.range (MulAut.conj : QuaternionSU2 →* MulAut QuaternionSU2)

private theorem conjugation_ker_eq_center :
    MonoidHom.ker (MulAut.conj : QuaternionSU2 →* MulAut QuaternionSU2) =
      Subgroup.center QuaternionSU2 := by
  ext q
  constructor
  · intro hq
    rw [MonoidHom.mem_ker] at hq
    rw [Subgroup.mem_center_iff]
    intro r
    have hr := DFunLike.congr_fun hq r
    change q * r * q⁻¹ = r at hr
    exact (mul_inv_eq_iff_eq_mul.mp hr).symm
  · intro hq
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro r
    change q * r * q⁻¹ = r
    have hr := Subgroup.mem_center_iff.mp hq r
    rw [← hr, mul_assoc, mul_inv_cancel, mul_one]

/-- The quotient-by-center definition of `Inn(SU(2))` agrees with the
literal range of the conjugation homomorphism in `MulAut SU(2)`. -/
def quaternionInnEquivConjugationRange :
    QuaternionInn ≃* QuaternionInnerAutomorphismGroup :=
  (QuotientGroup.quotientMulEquivOfEq conjugation_ker_eq_center.symm).trans
    (QuotientGroup.quotientKerEquivRange
      (MulAut.conj : QuaternionSU2 →* MulAut QuaternionSU2))

/-- The literal group of inner automorphisms of the concrete `SU(2)` model
is isomorphic to `SO(3)`. -/
def quaternionInnerAutomorphismEquivSO3 :
    QuaternionInnerAutomorphismGroup ≃* SO3 :=
  quaternionInnEquivConjugationRange.symm.trans quaternionInnEquivSO3

/-! ## The product group -/

/-- Concrete group model of `SU(2) × SU(2)`. -/
abbrev QuaternionS3xS3 := QuaternionSU2 × QuaternionSU2

/-- The product adjoint homomorphism. -/
def s3xS3Adjoint : QuaternionS3xS3 →* InnerAction where
  toFun q := (quaternionAdjoint q.1, quaternionAdjoint q.2)
  map_one' := by simp
  map_mul' q r := by simp

theorem s3xS3Adjoint_surjective : Function.Surjective s3xS3Adjoint := by
  rintro ⟨U, V⟩
  obtain ⟨q, hq⟩ := quaternionAdjoint_surjective U
  obtain ⟨r, hr⟩ := quaternionAdjoint_surjective V
  exact ⟨(q, r), by simp [s3xS3Adjoint, hq, hr]⟩

theorem s3xS3_center_eq_adjoint_ker :
    Subgroup.center QuaternionS3xS3 = MonoidHom.ker s3xS3Adjoint := by
  rw [Subgroup.center_prod, quaternion_center_eq_adjoint_ker]
  ext q
  change (q.1 ∈ MonoidHom.ker quaternionAdjoint ∧
    q.2 ∈ MonoidHom.ker quaternionAdjoint) ↔
      q ∈ MonoidHom.ker s3xS3Adjoint
  simp [s3xS3Adjoint]

/-- Effective inner automorphisms of the concrete product group. -/
abbrev S3xS3Inn := QuaternionS3xS3 ⧸ Subgroup.center QuaternionS3xS3

/-- The fully proved product identification
`Inn(SU(2) × SU(2)) ≃ SO(3) × SO(3)`. -/
def s3xS3InnEquivInnerAction : S3xS3Inn ≃* InnerAction :=
  (QuotientGroup.quotientMulEquivOfEq s3xS3_center_eq_adjoint_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective s3xS3Adjoint
      s3xS3Adjoint_surjective)

end

end S3xS3.Geometry
