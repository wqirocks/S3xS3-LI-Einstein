import S3xS3.Geometry.ConcreteGroup

/-!
# The standard matrix Lie algebra of `SU(2) × SU(2)`

This removes the last representational ambiguity in the bridge.  The Lie
algebra is defined literally as traceless skew-Hermitian `2 × 2` matrices,
its bracket is the matrix commutator, and explicit linear equivalences prove
that it agrees with both imaginary quaternions and the six real coordinates.
-/

open scoped Matrix BigOperators ComplexConjugate

namespace S3xS3.Geometry

open Quaternion

noncomputable section

abbrev CMat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The standard traceless skew-Hermitian matrix model of `su(2)`. -/
def matrixSu2LieSubmodule : Submodule ℝ CMat2 where
  carrier := {X | star X = -X ∧ X.trace = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨hXstar, hXtr⟩ ⟨hYstar, hYtr⟩
    constructor
    · rw [star_add, hXstar, hYstar, neg_add]
    · rw [Matrix.trace_add, hXtr, hYtr, add_zero]
  smul_mem' := by
    rintro c X ⟨hXstar, hXtr⟩
    constructor
    · ext i j
      simp
      have h := congrArg (fun M : CMat2 ↦ M i j) hXstar
      simpa [Matrix.conjTranspose_apply] using congrArg (fun z : ℂ ↦ c * z) h
    · rw [Matrix.trace_smul, hXtr, smul_zero]

abbrev MatrixSu2LieAlgebra := matrixSu2LieSubmodule

def quaternionLieToMatrix :
    QuaternionSu2LieAlgebra →ₗ[ℝ] MatrixSu2LieAlgebra where
  toFun q := ⟨quaternionMatrix q, by
    have hq : (q : ℍ).re = 0 := q.property
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        apply Complex.ext <;>
        simp [quaternionMatrix, hq]
    · apply Complex.ext <;>
        simp [Matrix.trace, quaternionMatrix, Fin.sum_univ_succ, hq]⟩
  map_add' q r := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [quaternionMatrix] <;>
      ring
  map_smul' c q := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [quaternionMatrix]

theorem quaternionLieToMatrix_injective :
    Function.Injective quaternionLieToMatrix := by
  intro q r h
  have hm := congrArg Subtype.val h
  have h00 := congrArg (fun M : CMat2 ↦ M 0 0) hm
  have h01 := congrArg (fun M : CMat2 ↦ M 0 1) hm
  apply Subtype.ext
  apply Quaternion.ext
  · exact q.property.trans r.property.symm
  · exact (by simpa [quaternionLieToMatrix, quaternionMatrix] using
      congrArg Complex.im h00)
  · exact (by simpa [quaternionLieToMatrix, quaternionMatrix] using
      congrArg Complex.re h01)
  · exact (by simpa [quaternionLieToMatrix, quaternionMatrix] using
      congrArg Complex.im h01)

def quaternionLieOfMatrix (X : MatrixSu2LieAlgebra) :
    QuaternionSu2LieAlgebra :=
  ⟨⟨0, (X : CMat2) 0 0 |>.im, (X : CMat2) 0 1 |>.re,
      (X : CMat2) 0 1 |>.im⟩, rfl⟩

lemma quaternionMatrix_quaternionLieOfMatrix (X : MatrixSu2LieAlgebra) :
    quaternionMatrix (quaternionLieOfMatrix X) = X := by
  let M : CMat2 := X
  have hstar : star M = -M := X.property.1
  have htrace : M.trace = 0 := X.property.2
  have h00c := congrArg (fun A : CMat2 ↦ A 0 0) hstar
  have h00re := congrArg Complex.re h00c
  have h00 : (M 0 0).re = 0 := by
    simp at h00re
    linarith
  have h10c := congrArg (fun A : CMat2 ↦ A 1 0) hstar
  have h10 : M 1 0 = -star (M 0 1) := by
    have h10neg : -star (M 0 1) = M 1 0 := by
      simpa [Matrix.conjTranspose_apply] using congrArg Neg.neg h10c
    exact h10neg.symm
  have h11 : M 1 1 = -M 0 0 := by
    simp [Matrix.trace, Fin.sum_univ_succ] at htrace
    exact eq_neg_of_add_eq_zero_right htrace
  ext i j
  fin_cases i <;> fin_cases j
  · change (⟨0, (M 0 0).im⟩ : ℂ) = M 0 0
    apply Complex.ext <;> simp [h00]
  · change (⟨(M 0 1).re, (M 0 1).im⟩ : ℂ) = M 0 1
    apply Complex.ext <;> simp
  · change (⟨-(M 0 1).re, (M 0 1).im⟩ : ℂ) = M 1 0
    rw [h10]
    apply Complex.ext <;> simp
  · change (⟨0, -(M 0 0).im⟩ : ℂ) = M 1 1
    rw [h11]
    apply Complex.ext <;> simp [h00]

theorem quaternionLieToMatrix_surjective :
    Function.Surjective quaternionLieToMatrix := by
  intro X
  refine ⟨quaternionLieOfMatrix X, ?_⟩
  apply Subtype.ext
  exact quaternionMatrix_quaternionLieOfMatrix X

def quaternionLieEquivMatrixLie :
    QuaternionSu2LieAlgebra ≃ₗ[ℝ] MatrixSu2LieAlgebra :=
  LinearEquiv.ofBijective quaternionLieToMatrix
    ⟨quaternionLieToMatrix_injective, quaternionLieToMatrix_surjective⟩

@[simp] lemma quaternionLieEquivMatrixLie_coe
    (x : QuaternionSu2LieAlgebra) :
    ((quaternionLieEquivMatrixLie x : MatrixSu2LieAlgebra) : CMat2) =
      quaternionMatrix x := rfl

def matrixSu2LieBracket (X Y : MatrixSu2LieAlgebra) :
    MatrixSu2LieAlgebra :=
  ⟨(X : CMat2) * (Y : CMat2) - (Y : CMat2) * (X : CMat2), by
    constructor
    · rw [star_sub, star_mul, star_mul, X.property.1, Y.property.1]
      noncomm_ring
    · rw [Matrix.trace_sub, Matrix.trace_mul_comm]
      ring⟩

lemma quaternionMatrix_sub (q r : ℍ) :
    quaternionMatrix (q - r) = quaternionMatrix q - quaternionMatrix r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [quaternionMatrix] <;>
    ring

theorem quaternionLieEquivMatrixLie_bracket
    (x y : QuaternionSu2LieAlgebra) :
    matrixSu2LieBracket (quaternionLieEquivMatrixLie x)
      (quaternionLieEquivMatrixLie y) =
        quaternionLieEquivMatrixLie (quaternionLieBracket x y) := by
  apply Subtype.ext
  simp only [matrixSu2LieBracket, quaternionLieBracket,
    quaternionLieEquivMatrixLie_coe]
  change quaternionMatrix x * quaternionMatrix y - quaternionMatrix y * quaternionMatrix x =
    quaternionMatrix ((x : ℍ) * (y : ℍ) - (y : ℍ) * (x : ℍ))
  rw [quaternionMatrix_sub, quaternionMatrix_mul, quaternionMatrix_mul]

abbrev MatrixS3xS3LieAlgebra := MatrixSu2LieAlgebra × MatrixSu2LieAlgebra

def quaternionProductLieEquivMatrixProductLie :
    QuaternionS3xS3LieAlgebra ≃ₗ[ℝ] MatrixS3xS3LieAlgebra :=
  LinearEquiv.prodCongr quaternionLieEquivMatrixLie quaternionLieEquivMatrixLie

def lieVecEquivMatrixProduct : LieVec ≃ₗ[ℝ] MatrixS3xS3LieAlgebra :=
  lieVecEquivQuaternionProduct.trans quaternionProductLieEquivMatrixProductLie

def matrixProductLieBracket (X Y : MatrixS3xS3LieAlgebra) :
    MatrixS3xS3LieAlgebra :=
  (matrixSu2LieBracket X.1 Y.1, matrixSu2LieBracket X.2 Y.2)

theorem lieVecEquivMatrixProduct_bracket (x y : LieVec) :
    matrixProductLieBracket (lieVecEquivMatrixProduct x)
      (lieVecEquivMatrixProduct y) =
        lieVecEquivMatrixProduct (S3xS3.bracket x y) := by
  have h := congrArg quaternionProductLieEquivMatrixProductLie
    (lieVecEquivQuaternionProduct_bracket x y)
  simpa [lieVecEquivMatrixProduct, matrixProductLieBracket,
    quaternionProductLieEquivMatrixProductLie,
    quaternionProductBracket, quaternionLieEquivMatrixLie_bracket] using h

/-! ## Differential of matrix conjugation -/

theorem quaternionLieEquivMatrixLie_conjugation
    (q : QuaternionSU2) (x : QuaternionSu2LieAlgebra) :
    ((quaternionLieEquivMatrixLie
        (quaternionConjugationDerivative q x) : MatrixSu2LieAlgebra) : CMat2) =
      ((quaternionSU2EquivMatrixSU2 q : MatrixSU2) : CMat2) *
        ((quaternionLieEquivMatrixLie x : MatrixSu2LieAlgebra) : CMat2) *
          star ((quaternionSU2EquivMatrixSU2 q : MatrixSU2) : CMat2) := by
  change quaternionMatrix ((q : ℍ) * (x : ℍ) * star (q : ℍ)) =
    quaternionMatrix q * quaternionMatrix x * star (quaternionMatrix q)
  rw [quaternionMatrix_mul, quaternionMatrix_mul, quaternionMatrix_star]

/-- Differential of conjugation by an element of the actual matrix product,
defined on the literal traceless skew-Hermitian matrix Lie algebra. -/
def matrixProductConjugationDerivativeLie (U : MatrixS3xS3)
    (X : MatrixS3xS3LieAlgebra) : MatrixS3xS3LieAlgebra :=
  quaternionProductLieEquivMatrixProductLie
    (quaternionProductConjugationDerivative
      (quaternionProductEquivMatrixS3xS3.symm U)
      (quaternionProductLieEquivMatrixProductLie.symm X))

/-- The transported definition above is literally matrix conjugation in the
first factor. -/
theorem matrixProductConjugationDerivativeLie_fst
    (U : MatrixS3xS3) (X : MatrixS3xS3LieAlgebra) :
    ((matrixProductConjugationDerivativeLie U X).1 : CMat2) =
      (U.1 : CMat2) * (X.1 : CMat2) * star (U.1 : CMat2) := by
  let q := quaternionProductEquivMatrixS3xS3.symm U
  let x := quaternionProductLieEquivMatrixProductLie.symm X
  have hU : quaternionProductEquivMatrixS3xS3 q = U := by simp [q]
  have hX : quaternionProductLieEquivMatrixProductLie x = X := by simp [x]
  have hU1 := congrArg Prod.fst hU
  have hX1 := congrArg Prod.fst hX
  change quaternionSU2EquivMatrixSU2 q.1 = U.1 at hU1
  change quaternionLieEquivMatrixLie x.1 = X.1 at hX1
  change ((quaternionLieEquivMatrixLie
      (quaternionConjugationDerivative q.1 x.1) : MatrixSu2LieAlgebra) : CMat2) = _
  rw [quaternionLieEquivMatrixLie_conjugation]
  rw [hU1, hX1]

/-- The same literal matrix-conjugation formula in the second factor. -/
theorem matrixProductConjugationDerivativeLie_snd
    (U : MatrixS3xS3) (X : MatrixS3xS3LieAlgebra) :
    ((matrixProductConjugationDerivativeLie U X).2 : CMat2) =
      (U.2 : CMat2) * (X.2 : CMat2) * star (U.2 : CMat2) := by
  let q := quaternionProductEquivMatrixS3xS3.symm U
  let x := quaternionProductLieEquivMatrixProductLie.symm X
  have hU : quaternionProductEquivMatrixS3xS3 q = U := by simp [q]
  have hX : quaternionProductLieEquivMatrixProductLie x = X := by simp [x]
  have hU2 := congrArg Prod.snd hU
  have hX2 := congrArg Prod.snd hX
  change quaternionSU2EquivMatrixSU2 q.2 = U.2 at hU2
  change quaternionLieEquivMatrixLie x.2 = X.2 at hX2
  change ((quaternionLieEquivMatrixLie
      (quaternionConjugationDerivative q.2 x.2) : MatrixSu2LieAlgebra) : CMat2) = _
  rw [quaternionLieEquivMatrixLie_conjugation]
  rw [hU2, hX2]

/-- The derivative of literal matrix conjugation is exactly the block
`SO(3) × SO(3)` action used by the coordinate proofs. -/
theorem matrixProductConjugationDerivativeLie_equivariant
    (U : MatrixS3xS3) (x : LieVec) :
    matrixProductConjugationDerivativeLie U (lieVecEquivMatrixProduct x) =
      lieVecEquivMatrixProduct
        (innerMatrix (matrixS3xS3Adjoint U) *ᵥ x) := by
  let q := quaternionProductEquivMatrixS3xS3.symm U
  have h := congrArg quaternionProductLieEquivMatrixProductLie
    (quaternionProductConjugationDerivative_equivariant q x)
  simpa [matrixProductConjugationDerivativeLie, lieVecEquivMatrixProduct,
    matrixS3xS3Adjoint, q] using h

end

end S3xS3.Geometry
