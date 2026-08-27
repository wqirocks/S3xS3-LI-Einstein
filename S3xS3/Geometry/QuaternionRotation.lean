import S3xS3.Core

open scoped Matrix BigOperators

namespace S3xS3.Geometry

open Quaternion

noncomputable section

/-- The unit quaternions, used as the concrete group model of `SU(2)`. -/
abbrev QuaternionSU2 := unitary ℍ

/-- A quaternion of norm-square one is a unit quaternion. -/
noncomputable def quaternionSU2OfNormSqOne (q : ℍ) (hq : Quaternion.normSq q = 1) :
    QuaternionSU2 :=
  ⟨q, by
    constructor
    · rw [Quaternion.star_mul_self, hq]
      norm_num
    · rw [Quaternion.self_mul_star, hq]
      norm_num⟩

lemma quaternionSU2_normSq (q : QuaternionSU2) :
    Quaternion.normSq (q : ℍ) = 1 := by
  have h := q.property.2
  rw [Quaternion.self_mul_star] at h
  have hre := congrArg (fun x : ℍ ↦ x.re) h
  simpa using hre

/-- Euler--Rodrigues matrix of quaternion conjugation on the imaginary
quaternions.  This homogeneous formula is useful before imposing unit norm. -/
def quaternionRotationMatrix (q : ℍ) : Mat3 :=
  !![q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2,
      2 * (q.imI * q.imJ - q.re * q.imK),
      2 * (q.imI * q.imK + q.re * q.imJ);
     2 * (q.imI * q.imJ + q.re * q.imK),
      q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2,
      2 * (q.imJ * q.imK - q.re * q.imI);
     2 * (q.imI * q.imK - q.re * q.imJ),
      2 * (q.imJ * q.imK + q.re * q.imI),
      q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2]

@[simp]
lemma quaternionRotationMatrix_one :
    quaternionRotationMatrix (1 : ℍ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRotationMatrix]

lemma quaternionRotationMatrix_mul (q r : ℍ) :
    quaternionRotationMatrix (q * r) =
      quaternionRotationMatrix q * quaternionRotationMatrix r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRotationMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    ring

lemma quaternionRotationMatrix_mul_transpose (q : ℍ) :
    quaternionRotationMatrix q * (quaternionRotationMatrix q)ᵀ =
      (Quaternion.normSq q) ^ 2 • (1 : Mat3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRotationMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Quaternion.normSq_def'] <;>
    ring

lemma quaternionRotationMatrix_det (q : ℍ) :
    (quaternionRotationMatrix q).det = (Quaternion.normSq q) ^ 3 := by
  simp [quaternionRotationMatrix, Matrix.det_fin_three,
    Quaternion.normSq_def']
  ring

/-- The adjoint double-cover homomorphism from unit quaternions to `SO(3)`. -/
def quaternionAdjoint : QuaternionSU2 →* SO3 where
  toFun q := ⟨quaternionRotationMatrix q, by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    · rw [Matrix.mem_orthogonalGroup_iff,
        quaternionRotationMatrix_mul_transpose, quaternionSU2_normSq]
      simp
    · rw [quaternionRotationMatrix_det, quaternionSU2_normSq]
      norm_num⟩
  map_one' := by
    apply Subtype.ext
    exact quaternionRotationMatrix_one
  map_mul' q r := by
    apply Subtype.ext
    exact quaternionRotationMatrix_mul q r

@[simp]
lemma quaternionAdjoint_coe (q : QuaternionSU2) :
    ((quaternionAdjoint q : SO3) : Mat3) = quaternionRotationMatrix q := rfl

/-! ## Algebraic surjectivity certificate -/

abbrev I4 := Fin 4
abbrev Mat4 := Matrix I4 I4 ℝ

/-- The rank-one quaternion Gram matrix associated with a rotation matrix.
For a rotation represented by `q = a + bi + cj + dk`, this is exactly
`![a,b,c,d] * ![a,b,c,d]ᵀ`. -/
def quaternionGram (R : Mat3) : Mat4 :=
  !![(1 + R 0 0 + R 1 1 + R 2 2) / 4,
      (R 2 1 - R 1 2) / 4,
      (R 0 2 - R 2 0) / 4,
      (R 1 0 - R 0 1) / 4;
     (R 2 1 - R 1 2) / 4,
      (1 + R 0 0 - R 1 1 - R 2 2) / 4,
      (R 0 1 + R 1 0) / 4,
      (R 0 2 + R 2 0) / 4;
     (R 0 2 - R 2 0) / 4,
      (R 0 1 + R 1 0) / 4,
      (1 - R 0 0 + R 1 1 - R 2 2) / 4,
      (R 1 2 + R 2 1) / 4;
     (R 1 0 - R 0 1) / 4,
      (R 0 2 + R 2 0) / 4,
      (R 1 2 + R 2 1) / 4,
      (1 - R 0 0 - R 1 1 + R 2 2) / 4]

lemma quaternionGram_symmetric (R : Mat3) :
    (quaternionGram R)ᵀ = quaternionGram R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionGram]

lemma quaternionGram_diagonal_sum (R : Mat3) :
    ∑ i, quaternionGram R i i = 1 := by
  simp [quaternionGram, Fin.sum_univ_succ]
  ring

/-- Ordered-index form of the vanishing-minor certificate. -/
private lemma quaternionGram_rankOne_ordered (R : SO3) (i j k : I4)
    (hij : i.val ≤ j.val) :
    quaternionGram R i j * quaternionGram R k k =
      quaternionGram R i k * quaternionGram R j k := by
  let A : Mat3 := R
  have hc := cofactor3_eq_of_mem_SO3 R
  change cofactor3 A = A at hc
  have hc00 : A 1 1 * A 2 2 - A 1 2 * A 2 1 = A 0 0 := by
    simpa [cofactor3] using congrArg (fun A : Mat3 ↦ A 0 0) hc
  have hc01 : A 1 2 * A 2 0 - A 1 0 * A 2 2 = A 0 1 := by
    simpa [cofactor3] using congrArg (fun A : Mat3 ↦ A 0 1) hc
  have hc02 : A 1 0 * A 2 1 - A 1 1 * A 2 0 = A 0 2 := by
    simpa [cofactor3] using congrArg (fun A : Mat3 ↦ A 0 2) hc
  have hc10 : A 0 2 * A 2 1 - A 0 1 * A 2 2 = A 1 0 := by
    simpa [cofactor3] using congrArg (fun A : Mat3 ↦ A 1 0) hc
  have hc11 : A 0 0 * A 2 2 - A 0 2 * A 2 0 = A 1 1 := by
    simpa [cofactor3] using congrArg (fun A : Mat3 ↦ A 1 1) hc
  have hc12 : A 0 1 * A 2 0 - A 0 0 * A 2 1 = A 1 2 := by
    simpa [cofactor3] using congrArg (fun A : Mat3 ↦ A 1 2) hc
  have hc20 : A 0 1 * A 1 2 - A 0 2 * A 1 1 = A 2 0 := by
    simpa [cofactor3] using congrArg (fun A : Mat3 ↦ A 2 0) hc
  have hc21 : A 0 2 * A 1 0 - A 0 0 * A 1 2 = A 2 1 := by
    simpa [cofactor3] using congrArg (fun A : Mat3 ↦ A 2 1) hc
  have hc22 : A 0 0 * A 1 1 - A 0 1 * A 1 0 = A 2 2 := by
    simpa [cofactor3] using congrArg (fun A : Mat3 ↦ A 2 2) hc
  have hrr : A * Aᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1
  have hr00 : A 0 0 ^ 2 + A 0 1 ^ 2 + A 0 2 ^ 2 = 1 := by
    have h := congrArg (fun A : Mat3 ↦ A 0 0) hrr
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  have hr11 : A 1 0 ^ 2 + A 1 1 ^ 2 + A 1 2 ^ 2 = 1 := by
    have h := congrArg (fun A : Mat3 ↦ A 1 1) hrr
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  have hr22 : A 2 0 ^ 2 + A 2 1 ^ 2 + A 2 2 ^ 2 = 1 := by
    have h := congrArg (fun A : Mat3 ↦ A 2 2) hrr
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  have hr01 : A 0 0 * A 1 0 + A 0 1 * A 1 1 + A 0 2 * A 1 2 = 0 := by
    have h := congrArg (fun A : Mat3 ↦ A 0 1) hrr
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  have hr02 : A 0 0 * A 2 0 + A 0 1 * A 2 1 + A 0 2 * A 2 2 = 0 := by
    have h := congrArg (fun A : Mat3 ↦ A 0 2) hrr
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  have hr12 : A 1 0 * A 2 0 + A 1 1 * A 2 1 + A 1 2 * A 2 2 = 0 := by
    have h := congrArg (fun A : Mat3 ↦ A 1 2) hrr
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  have htt : Aᵀ * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1
  have ht00 : A 0 0 ^ 2 + A 1 0 ^ 2 + A 2 0 ^ 2 = 1 := by
    have h := congrArg (fun A : Mat3 ↦ A 0 0) htt
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  have ht11 : A 0 1 ^ 2 + A 1 1 ^ 2 + A 2 1 ^ 2 = 1 := by
    have h := congrArg (fun A : Mat3 ↦ A 1 1) htt
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  have ht22 : A 0 2 ^ 2 + A 1 2 ^ 2 + A 2 2 ^ 2 = 1 := by
    have h := congrArg (fun A : Mat3 ↦ A 2 2) htt
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  have ht01 : A 0 0 * A 0 1 + A 1 0 * A 1 1 + A 2 0 * A 2 1 = 0 := by
    have h := congrArg (fun A : Mat3 ↦ A 0 1) htt
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  have ht02 : A 0 0 * A 0 2 + A 1 0 * A 1 2 + A 2 0 * A 2 2 = 0 := by
    have h := congrArg (fun A : Mat3 ↦ A 0 2) htt
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  have ht12 : A 0 1 * A 0 2 + A 1 1 * A 1 2 + A 2 1 * A 2 2 = 0 := by
    have h := congrArg (fun A : Mat3 ↦ A 1 2) htt
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at h
    nlinarith only [h]
  change quaternionGram A i j * quaternionGram A k k =
    quaternionGram A i k * quaternionGram A j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals simp [quaternionGram] at hij ⊢
  all_goals ring_nf
  next =>
    linear_combination (-1 / 8 : ℝ) * hc00 + (-1 / 16 : ℝ) * hr11 +
      (-1 / 16 : ℝ) * hr22 + (1 / 16 : ℝ) * ht00
  next =>
    linear_combination (-1 / 8 : ℝ) * hc11 + (-1 / 16 : ℝ) * hr00 +
      (-1 / 16 : ℝ) * hr22 + (1 / 16 : ℝ) * ht11
  next =>
    linear_combination (-1 / 8 : ℝ) * hc22 + (1 / 16 : ℝ) * hr22 +
      (-1 / 16 : ℝ) * ht00 + (-1 / 16 : ℝ) * ht11
  next =>
    linear_combination (1 / 16 : ℝ) * hc12 + (-1 / 16 : ℝ) * hc21 +
      (1 / 16 : ℝ) * hr12 + (-1 / 16 : ℝ) * ht12
  next =>
    linear_combination (1 / 16 : ℝ) * hc12 + (-1 / 16 : ℝ) * hc21 +
      (-1 / 16 : ℝ) * hr12 + (1 / 16 : ℝ) * ht12
  next =>
    linear_combination (-1 / 16 : ℝ) * hc02 + (1 / 16 : ℝ) * hc20 +
      (-1 / 16 : ℝ) * hr02 + (1 / 16 : ℝ) * ht02
  next =>
    linear_combination (-1 / 16 : ℝ) * hc02 + (1 / 16 : ℝ) * hc20 +
      (1 / 16 : ℝ) * hr02 + (-1 / 16 : ℝ) * ht02
  next =>
    linear_combination (1 / 16 : ℝ) * hc01 + (-1 / 16 : ℝ) * hc10 +
      (1 / 16 : ℝ) * hr01 + (-1 / 16 : ℝ) * ht01
  next =>
    linear_combination (1 / 16 : ℝ) * hc01 + (-1 / 16 : ℝ) * hc10 +
      (-1 / 16 : ℝ) * hr01 + (1 / 16 : ℝ) * ht01
  next =>
    linear_combination (-1 / 8 : ℝ) * hc00 + (-1 / 16 : ℝ) * hr11 +
      (-1 / 16 : ℝ) * hr22 + (1 / 16 : ℝ) * ht00
  next =>
    linear_combination (1 / 8 : ℝ) * hc22 + (1 / 16 : ℝ) * hr22 +
      (-1 / 16 : ℝ) * ht00 + (-1 / 16 : ℝ) * ht11
  next =>
    linear_combination (1 / 8 : ℝ) * hc11 + (-1 / 16 : ℝ) * hr00 +
      (-1 / 16 : ℝ) * hr22 + (1 / 16 : ℝ) * ht11
  next =>
    linear_combination (-1 / 16 : ℝ) * hc01 + (-1 / 16 : ℝ) * hc10 +
      (1 / 16 : ℝ) * hr01 + (1 / 16 : ℝ) * ht01
  next =>
    linear_combination (-1 / 16 : ℝ) * hc01 + (-1 / 16 : ℝ) * hc10 +
      (-1 / 16 : ℝ) * hr01 + (-1 / 16 : ℝ) * ht01
  next =>
    linear_combination (-1 / 16 : ℝ) * hc02 + (-1 / 16 : ℝ) * hc20 +
      (1 / 16 : ℝ) * hr02 + (1 / 16 : ℝ) * ht02
  next =>
    linear_combination (-1 / 16 : ℝ) * hc02 + (-1 / 16 : ℝ) * hc20 +
      (-1 / 16 : ℝ) * hr02 + (-1 / 16 : ℝ) * ht02
  next =>
    linear_combination (-1 / 8 : ℝ) * hc11 + (-1 / 16 : ℝ) * hr00 +
      (-1 / 16 : ℝ) * hr22 + (1 / 16 : ℝ) * ht11
  next =>
    linear_combination (1 / 8 : ℝ) * hc22 + (1 / 16 : ℝ) * hr22 +
      (-1 / 16 : ℝ) * ht00 + (-1 / 16 : ℝ) * ht11
  next =>
    linear_combination (1 / 8 : ℝ) * hc00 + (-1 / 16 : ℝ) * hr11 +
      (-1 / 16 : ℝ) * hr22 + (1 / 16 : ℝ) * ht00
  next =>
    linear_combination (-1 / 16 : ℝ) * hc12 + (-1 / 16 : ℝ) * hc21 +
      (1 / 16 : ℝ) * hr12 + (1 / 16 : ℝ) * ht12
  next =>
    linear_combination (-1 / 16 : ℝ) * hc12 + (-1 / 16 : ℝ) * hc21 +
      (-1 / 16 : ℝ) * hr12 + (-1 / 16 : ℝ) * ht12
  next =>
    linear_combination (-1 / 8 : ℝ) * hc22 + (1 / 16 : ℝ) * hr22 +
      (-1 / 16 : ℝ) * ht00 + (-1 / 16 : ℝ) * ht11
  next =>
    linear_combination (1 / 8 : ℝ) * hc11 + (-1 / 16 : ℝ) * hr00 +
      (-1 / 16 : ℝ) * hr22 + (1 / 16 : ℝ) * ht11
  next =>
    linear_combination (1 / 8 : ℝ) * hc00 + (-1 / 16 : ℝ) * hr11 +
      (-1 / 16 : ℝ) * hr22 + (1 / 16 : ℝ) * ht00

lemma quaternionGram_apply_comm (R : Mat3) (i j : I4) :
    quaternionGram R i j = quaternionGram R j i := by
  fin_cases i <;> fin_cases j <;> simp [quaternionGram]

/-- All `2 × 2` minors of the quaternion Gram matrix of a rotation vanish.
This is the polynomial heart of the surjectivity of the quaternion double cover. -/
lemma quaternionGram_rankOne (R : SO3) (i j k : I4) :
    quaternionGram R i j * quaternionGram R k k =
      quaternionGram R i k * quaternionGram R j k := by
  by_cases hij : i.val ≤ j.val
  · exact quaternionGram_rankOne_ordered R i j k hij
  · have hji : j.val ≤ i.val := Nat.le_of_not_ge hij
    have h := quaternionGram_rankOne_ordered R j i k hji
    rw [quaternionGram_apply_comm R j i] at h
    simpa [mul_comm] using h

lemma exists_quaternionGram_diagonal_pos (R : SO3) :
    ∃ k : I4, 0 < quaternionGram R k k := by
  by_contra h
  push Not at h
  have h0 := h (0 : I4)
  have h1 := h (1 : I4)
  have h2 := h (2 : I4)
  have h3 := h (3 : I4)
  have hs := quaternionGram_diagonal_sum (R : Mat3)
  simp [Fin.sum_univ_succ] at hs
  nlinarith

/-- Every orientation-preserving orthogonal `3 × 3` matrix is quaternionic
conjugation.  The proof constructs a unit quaternion from a positive diagonal
entry of `quaternionGram` and uses the vanishing-minor certificate above. -/
theorem quaternionAdjoint_surjective : Function.Surjective quaternionAdjoint := by
  intro R
  obtain ⟨k, hk⟩ := exists_quaternionGram_diagonal_pos R
  let K : Mat4 := quaternionGram R
  let s : ℝ := √(K k k)
  have hspos : 0 < s := by
    exact Real.sqrt_pos.2 hk
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hs2 : s ^ 2 = K k k := by
    exact Real.sq_sqrt (le_of_lt hk)
  let v : I4 → ℝ := fun i ↦ K i k / s
  have hv_outer (i j : I4) : v i * v j = K i j := by
    have hrank := quaternionGram_rankOne R i j k
    change K i j * K k k = K i k * K j k at hrank
    dsimp only [v]
    rw [div_mul_div_comm, ← pow_two, hs2, div_eq_iff (ne_of_gt hk)]
    simpa [mul_comm] using hrank.symm
  let q : ℍ := ⟨v 0, v 1, v 2, v 3⟩
  have hqnorm : Quaternion.normSq q = 1 := by
    have h0 := hv_outer (0 : I4) 0
    have h1 := hv_outer (1 : I4) 1
    have h2 := hv_outer (2 : I4) 2
    have h3 := hv_outer (3 : I4) 3
    have hsum : K 0 0 + K 1 1 + K 2 2 + K 3 3 = 1 := by
      simpa [K, Fin.sum_univ_succ, add_assoc] using
        quaternionGram_diagonal_sum (R : Mat3)
    simp only [Quaternion.normSq_def', q]
    nlinarith [h0, h1, h2, h3]
  let uq : QuaternionSU2 := quaternionSU2OfNormSqOne q hqnorm
  refine ⟨uq, Subtype.ext ?_⟩
  change quaternionRotationMatrix q = (R : Mat3)
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [quaternionRotationMatrix, q]
  all_goals simp_rw [pow_two, hv_outer]
  all_goals simp [K, quaternionGram]
  all_goals ring

end

end S3xS3.Geometry
