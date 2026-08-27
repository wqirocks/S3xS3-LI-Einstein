import S3xS3.Geometry.SU2Matrix

/-!
# The Lie algebra and adjoint-action coordinate bridge

The Lie algebra of the unit-quaternion model is the imaginary-quaternion
subspace with commutator bracket.  The explicit factor `1/2` below proves
that the fixed coordinate bracket in `S3xS3.Core` is exactly this bracket.
The last theorem verifies that quaternion conjugation has derivative equal to
the block `SO(3) × SO(3)` action used by the coordinate proofs.
-/

open scoped Matrix BigOperators

namespace S3xS3.Geometry

open Quaternion

noncomputable section

/-- The traceless/skew-adjoint quaternionic Lie algebra of the unit sphere. -/
def imaginaryQuaternions : Submodule ℝ ℍ where
  carrier := {q | q.re = 0}
  zero_mem' := by simp
  add_mem' := by intro q r hq hr; simpa using congrArg₂ (.+.) hq hr
  smul_mem' := by
    intro c q hq
    change c * q.re = 0
    rw [hq, mul_zero]

abbrev QuaternionSu2LieAlgebra := imaginaryQuaternions

def pureQuaternion (v : Vec3) : ℍ := ⟨0, v 0, v 1, v 2⟩

@[simp] lemma pureQuaternion_re (v : Vec3) : (pureQuaternion v).re = 0 := rfl
@[simp] lemma pureQuaternion_imI (v : Vec3) : (pureQuaternion v).imI = v 0 := rfl
@[simp] lemma pureQuaternion_imJ (v : Vec3) : (pureQuaternion v).imJ = v 1 := rfl
@[simp] lemma pureQuaternion_imK (v : Vec3) : (pureQuaternion v).imK = v 2 := rfl

/-- The normalization by `1/2` makes the quaternion commutator correspond
exactly, rather than only up to scale, to the cross product. -/
def vec3EquivQuaternionLie : Vec3 ≃ₗ[ℝ] QuaternionSu2LieAlgebra where
  toFun v := ⟨(1 / 2 : ℝ) • pureQuaternion v, by simp [imaginaryQuaternions]⟩
  invFun q := ![2 * (q : ℍ).imI, 2 * (q : ℍ).imJ, 2 * (q : ℍ).imK]
  map_add' v w := by
    apply Subtype.ext
    apply Quaternion.ext <;> simp [pureQuaternion] <;> ring
  map_smul' c v := by
    apply Subtype.ext
    apply Quaternion.ext <;> simp [pureQuaternion] <;> ring
  left_inv v := by
    funext i
    fin_cases i <;> simp [pureQuaternion]
  right_inv q := by
    apply Subtype.ext
    apply Quaternion.ext
    · simp [pureQuaternion]
      exact q.property.symm
    · simp [pureQuaternion]
    · simp [pureQuaternion]
    · simp [pureQuaternion]

/-- Quaternion commutator, closed on the imaginary subspace. -/
def quaternionLieBracket
    (x y : QuaternionSu2LieAlgebra) : QuaternionSu2LieAlgebra :=
  ⟨(x : ℍ) * (y : ℍ) - (y : ℍ) * (x : ℍ), by
    change (((x : ℍ) * (y : ℍ) - (y : ℍ) * (x : ℍ)) : ℍ).re = 0
    simp [Quaternion.re_mul]
    ring⟩

theorem vec3EquivQuaternionLie_bracket (u v : Vec3) :
    quaternionLieBracket (vec3EquivQuaternionLie u)
      (vec3EquivQuaternionLie v) = vec3EquivQuaternionLie (u ⨯₃ v) := by
  apply Subtype.ext
  apply Quaternion.ext
  · simp [quaternionLieBracket, vec3EquivQuaternionLie, pureQuaternion,
      Quaternion.re_mul]
    ring
  · simp [quaternionLieBracket, vec3EquivQuaternionLie, pureQuaternion,
      Quaternion.imI_mul, cross_apply] ; ring
  · simp [quaternionLieBracket, vec3EquivQuaternionLie, pureQuaternion,
      Quaternion.imJ_mul, cross_apply] ; ring
  · simp [quaternionLieBracket, vec3EquivQuaternionLie, pureQuaternion,
      Quaternion.imK_mul, cross_apply] ; ring

abbrev QuaternionS3xS3LieAlgebra :=
  QuaternionSu2LieAlgebra × QuaternionSu2LieAlgebra

def lieVecEquivQuaternionProduct :
    LieVec ≃ₗ[ℝ] QuaternionS3xS3LieAlgebra where
  toFun x :=
    (vec3EquivQuaternionLie (fun i ↦ x (Sum.inl i)),
     vec3EquivQuaternionLie (fun i ↦ x (Sum.inr i)))
  invFun x := Sum.elim (vec3EquivQuaternionLie.symm x.1)
    (vec3EquivQuaternionLie.symm x.2)
  map_add' x y := by
    apply Prod.ext
    · exact vec3EquivQuaternionLie.map_add _ _
    · exact vec3EquivQuaternionLie.map_add _ _
  map_smul' c x := by
    apply Prod.ext
    · exact vec3EquivQuaternionLie.map_smul c _
    · exact vec3EquivQuaternionLie.map_smul c _
  left_inv x := by
    funext i
    cases i with
    | inl i => simp
    | inr i => simp
  right_inv x := by ext <;> simp

def quaternionProductBracket (x y : QuaternionS3xS3LieAlgebra) :
    QuaternionS3xS3LieAlgebra :=
  (quaternionLieBracket x.1 y.1, quaternionLieBracket x.2 y.2)

theorem lieVecEquivQuaternionProduct_bracket (x y : LieVec) :
    quaternionProductBracket (lieVecEquivQuaternionProduct x)
      (lieVecEquivQuaternionProduct y) =
        lieVecEquivQuaternionProduct (S3xS3.bracket x y) := by
  apply Prod.ext
  · exact vec3EquivQuaternionLie_bracket _ _
  · exact vec3EquivQuaternionLie_bracket _ _

lemma pureQuaternion_rotation (q : ℍ) (v : Vec3) :
    q * pureQuaternion v * star q =
      pureQuaternion (quaternionRotationMatrix q *ᵥ v) := by
  apply Quaternion.ext
  · simp [pureQuaternion, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
    ring
  · simp [pureQuaternion, quaternionRotationMatrix, Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail,
      Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
    ring
  · simp [pureQuaternion, quaternionRotationMatrix, Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail,
      Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
    ring
  · simp [pureQuaternion, quaternionRotationMatrix, Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail,
      Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
    ring

def quaternionConjugationDerivative (q : QuaternionSU2)
    (x : QuaternionSu2LieAlgebra) : QuaternionSu2LieAlgebra :=
  ⟨(q : ℍ) * (x : ℍ) * star (q : ℍ), by
    change ((q : ℍ) * (x : ℍ) * star (q : ℍ)).re = 0
    have hx := x.property
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] at ⊢
    rw [hx]
    ring⟩

theorem quaternionConjugationDerivative_equivariant
    (q : QuaternionSU2) (v : Vec3) :
    quaternionConjugationDerivative q (vec3EquivQuaternionLie v) =
      vec3EquivQuaternionLie
        (((quaternionAdjoint q : SO3) : Mat3) *ᵥ v) := by
  apply Subtype.ext
  change (q : ℍ) * ((1 / 2 : ℝ) • pureQuaternion v) * star (q : ℍ) =
    (1 / 2 : ℝ) • pureQuaternion (quaternionRotationMatrix q *ᵥ v)
  have h := congrArg (fun z : ℍ ↦ (1 / 2 : ℝ) • z)
    (pureQuaternion_rotation (q : ℍ) v)
  simpa [Algebra.smul_mul_assoc, Algebra.mul_smul_comm] using h

def quaternionProductConjugationDerivative (q : QuaternionS3xS3)
    (x : QuaternionS3xS3LieAlgebra) : QuaternionS3xS3LieAlgebra :=
  (quaternionConjugationDerivative q.1 x.1,
   quaternionConjugationDerivative q.2 x.2)

theorem quaternionProductConjugationDerivative_equivariant
    (q : QuaternionS3xS3) (x : LieVec) :
    quaternionProductConjugationDerivative q
      (lieVecEquivQuaternionProduct x) =
    lieVecEquivQuaternionProduct
      (innerMatrix (s3xS3Adjoint q) *ᵥ x) := by
  apply Prod.ext
  · change quaternionConjugationDerivative q.1
      (vec3EquivQuaternionLie (fun i ↦ x (Sum.inl i))) = _
    rw [quaternionConjugationDerivative_equivariant]
    apply Subtype.ext
    apply Quaternion.ext <;>
      simp [lieVecEquivQuaternionProduct, vec3EquivQuaternionLie,
        innerMatrix, s3xS3Adjoint, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type]
  · change quaternionConjugationDerivative q.2
      (vec3EquivQuaternionLie (fun i ↦ x (Sum.inr i))) = _
    rw [quaternionConjugationDerivative_equivariant]
    apply Subtype.ext
    apply Quaternion.ext <;>
      simp [lieVecEquivQuaternionProduct, vec3EquivQuaternionLie,
        innerMatrix, s3xS3Adjoint, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type]

end

end S3xS3.Geometry
