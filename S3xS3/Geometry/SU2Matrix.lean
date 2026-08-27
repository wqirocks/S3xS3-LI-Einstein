import S3xS3.Geometry.InnerAutomorphisms

/-!
# The unit-quaternion and matrix models of `SU(2)`

This file gives an explicit group isomorphism between the unit quaternions and
Mathlib's `2 × 2` complex special-unitary group.  In particular, the use of
unit quaternions in the geometric bridge is not an unproved identification of
two Lie groups.
-/

open scoped Matrix ComplexConjugate

namespace S3xS3.Geometry

open Quaternion

noncomputable section

abbrev MatrixSU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

def quaternionMatrix (q : ℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩;
     ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

@[simp] lemma quaternionMatrix_one : quaternionMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;> simp [quaternionMatrix]

lemma quaternionMatrix_mul (q r : ℍ) :
    quaternionMatrix (q * r) = quaternionMatrix q * quaternionMatrix r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [quaternionMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    ring

lemma quaternionMatrix_star (q : ℍ) :
    quaternionMatrix (star q) = star (quaternionMatrix q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [quaternionMatrix]

lemma quaternionMatrix_det (q : ℍ) :
    (quaternionMatrix q).det = ((Quaternion.normSq q : ℝ) : ℂ) := by
  have hre (x : ℝ) : ((x : ℂ) ^ 2).re = x ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have him (x : ℝ) : ((x : ℂ) ^ 2).im = 0 := by
    simp [pow_two, Complex.mul_im]
  rw [Matrix.det_fin_two]
  apply Complex.ext <;>
    simp [quaternionMatrix, Quaternion.normSq_def', hre, him] <;>
    ring

lemma quaternionMatrix_mul_star (q : ℍ) :
    quaternionMatrix q * star (quaternionMatrix q) =
      ((Quaternion.normSq q : ℝ) : ℂ) • 1 := by
  have hre (x : ℝ) : ((x : ℂ) ^ 2).re = x ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have him (x : ℝ) : ((x : ℂ) ^ 2).im = 0 := by
    simp [pow_two, Complex.mul_im]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [quaternionMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Quaternion.normSq_def', hre, him] <;>
    ring

def quaternionToMatrixSU2 : QuaternionSU2 →* MatrixSU2 where
  toFun q := ⟨quaternionMatrix q, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff, quaternionMatrix_mul_star,
        quaternionSU2_normSq]
      simp
    · rw [quaternionMatrix_det, quaternionSU2_normSq]
      simp⟩
  map_one' := by
    apply Subtype.ext
    exact quaternionMatrix_one
  map_mul' q r := by
    apply Subtype.ext
    exact quaternionMatrix_mul q r

theorem quaternionToMatrixSU2_injective :
    Function.Injective quaternionToMatrixSU2 := by
  intro q r h
  have hm := congrArg Subtype.val h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 0 0) hm
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 0 1) hm
  apply Subtype.ext
  apply Quaternion.ext <;>
    simp [quaternionToMatrixSU2, quaternionMatrix] at h00 h01 ⊢
  · exact h00.1
  · exact h00.2
  · exact h01.1
  · exact h01.2

lemma matrixSU2_adjugate_eq_star (U : MatrixSU2) :
    (U : Matrix (Fin 2) (Fin 2) ℂ).adjugate = star (U : Matrix (Fin 2) (Fin 2) ℂ) := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := U
  have hmem := Matrix.mem_specialUnitaryGroup_iff.mp U.property
  have hunit : M * star M = 1 := Matrix.mem_unitaryGroup_iff.mp hmem.1
  have hdet : M.det = 1 := hmem.2
  calc
    M.adjugate = M.adjugate * 1 := by simp
    _ = M.adjugate * (M * star M) := by rw [hunit]
    _ = (M.adjugate * M) * star M := by rw [Matrix.mul_assoc]
    _ = (M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * star M := by
      rw [Matrix.adjugate_mul]
    _ = star M := by rw [hdet]; simp

lemma matrixSU2_entry_11 (U : MatrixSU2) :
    (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
      star ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  have h := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 0 0)
    (matrixSU2_adjugate_eq_star U)
  simpa [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] using h

lemma matrixSU2_entry_10 (U : MatrixSU2) :
    (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      -star ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
  have h := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 1 0)
    (matrixSU2_adjugate_eq_star U)
  simpa [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] using
    congrArg Neg.neg h

def quaternionOfMatrixSU2 (U : MatrixSU2) : ℍ :=
  ⟨((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re,
   ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im,
   ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re,
   ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im⟩

lemma quaternionMatrix_quaternionOfMatrixSU2 (U : MatrixSU2) :
    quaternionMatrix (quaternionOfMatrixSU2 U) = U := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := U
  have h11 : M 1 1 = star (M 0 0) := matrixSU2_entry_11 U
  have h10 : M 1 0 = -star (M 0 1) := matrixSU2_entry_10 U
  ext i j
  fin_cases i <;> fin_cases j
  · change (⟨(M 0 0).re, (M 0 0).im⟩ : ℂ) = M 0 0
    apply Complex.ext <;> simp
  · change (⟨(M 0 1).re, (M 0 1).im⟩ : ℂ) = M 0 1
    apply Complex.ext <;> simp
  · change (⟨-(M 0 1).re, (M 0 1).im⟩ : ℂ) = M 1 0
    rw [h10]
    apply Complex.ext <;>
      simp
  · change (⟨(M 0 0).re, -(M 0 0).im⟩ : ℂ) = M 1 1
    rw [h11]
    apply Complex.ext <;>
      simp

lemma quaternionOfMatrixSU2_normSq (U : MatrixSU2) :
    Quaternion.normSq (quaternionOfMatrixSU2 U) = 1 := by
  have hdet := quaternionMatrix_det (quaternionOfMatrixSU2 U)
  rw [quaternionMatrix_quaternionOfMatrixSU2] at hdet
  have hUdet := (Matrix.mem_specialUnitaryGroup_iff.mp U.property).2
  rw [hUdet] at hdet
  have hre := congrArg Complex.re hdet
  simpa using hre.symm

theorem quaternionToMatrixSU2_surjective :
    Function.Surjective quaternionToMatrixSU2 := by
  intro U
  let q : QuaternionSU2 := quaternionSU2OfNormSqOne
    (quaternionOfMatrixSU2 U) (quaternionOfMatrixSU2_normSq U)
  refine ⟨q, ?_⟩
  apply Subtype.ext
  exact quaternionMatrix_quaternionOfMatrixSU2 U

def quaternionSU2EquivMatrixSU2 : QuaternionSU2 ≃* MatrixSU2 :=
  MulEquiv.ofBijective quaternionToMatrixSU2
    ⟨quaternionToMatrixSU2_injective, quaternionToMatrixSU2_surjective⟩

@[simp] lemma quaternionSU2EquivMatrixSU2_coe (q : QuaternionSU2) :
    ((quaternionSU2EquivMatrixSU2 q : MatrixSU2) :
      Matrix (Fin 2) (Fin 2) ℂ) = quaternionMatrix q := rfl

end

end S3xS3.Geometry
