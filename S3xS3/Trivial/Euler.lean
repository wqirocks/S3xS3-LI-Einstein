import S3xS3.Trivial.Graph
import S3xS3.Trivial.SupportExclusion

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.Euler

open S3xS3.Trivial.Graph

def frob (A B : Mat3) : ℝ := ∑ i, ∑ j, A i j * B i j

def frobNormSq (A : Mat3) : ℝ := frob A A

@[simp] lemma real_smul_apply (c : ℝ) (A : Mat3) (i j : I3) :
    (c • A) i j = c * A i j := rfl

def dcof (A H : Mat3) : Mat3 :=
  !![H 1 1 * A 2 2 + A 1 1 * H 2 2 - H 1 2 * A 2 1 - A 1 2 * H 2 1,
     H 1 2 * A 2 0 + A 1 2 * H 2 0 - H 1 0 * A 2 2 - A 1 0 * H 2 2,
     H 1 0 * A 2 1 + A 1 0 * H 2 1 - H 1 1 * A 2 0 - A 1 1 * H 2 0;
     H 0 2 * A 2 1 + A 0 2 * H 2 1 - H 0 1 * A 2 2 - A 0 1 * H 2 2,
     H 0 0 * A 2 2 + A 0 0 * H 2 2 - H 0 2 * A 2 0 - A 0 2 * H 2 0,
     H 0 1 * A 2 0 + A 0 1 * H 2 0 - H 0 0 * A 2 1 - A 0 0 * H 2 1;
     H 0 1 * A 1 2 + A 0 1 * H 1 2 - H 0 2 * A 1 1 - A 0 2 * H 1 1,
     H 0 2 * A 1 0 + A 0 2 * H 1 0 - H 0 0 * A 1 2 - A 0 0 * H 1 2,
     H 0 0 * A 1 1 + A 0 0 * H 1 1 - H 0 1 * A 1 0 - A 0 1 * H 1 0]

def lop (P : Mat3) : Mat3 :=
  P.trace • (P.trace • (1 : Mat3)) - (2 : ℝ) • (P * P) -
    (2 : ℝ) • cofactor3 P

-- Equivalent to the manuscript's `tr(P^2) I - P^2 - 2 cof(P)`.
def lop' (P : Mat3) : Mat3 :=
  (P * P).trace • (1 : Mat3) - P * P - (2 : ℝ) • cofactor3 P

def kop (H : Mat3) : Mat3 :=
  cofactor3 H - (2 : ℝ) • (H.trace • (1 : Mat3)) + (4 : ℝ) • H

def residual (P Q M : Mat3) : Mat3 := cofactor3 M * P - Q * M

structure EulerData where
  P : Mat3
  Q : Mat3
  M : Mat3
  kappa : ℝ
  P_pos : P.PosDef
  Q_pos : Q.PosDef
  kappa_pos : 0 < kappa
  gradP :
    P.trace • (1 : Mat3) - (2 : ℝ) • P -
        (Mᵀ * M).trace • P +
        (1 / 2 : ℝ) • (Mᵀ * M * P + P * (Mᵀ * M)) +
        dcof P (Mᵀ * M) -
        (1 / 2 : ℝ) •
          ((cofactor3 M)ᵀ * residual P Q M +
            ((cofactor3 M)ᵀ * residual P Q M)ᵀ) =
      kappa • P⁻¹
  gradQ :
    Q.trace • (1 : Mat3) - (2 : ℝ) • Q +
        (1 / 2 : ℝ) •
          (residual P Q M * Mᵀ + M * (residual P Q M)ᵀ) =
      kappa • Q⁻¹
  gradM :
    -(M * lop' P) - dcof M (residual P Q M * P) +
        Q * residual P Q M = 0

lemma frob_eq_trace (A B : Mat3) : frob A B = (Aᵀ * B).trace := by
  simp [frob, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

lemma frob_symm (A B : Mat3) : frob A B = frob B A := by
  simp [frob, Fin.sum_univ_succ]
  ring

lemma frob_add_left (A B C : Mat3) : frob (A + B) C = frob A C + frob B C := by
  simp [frob, Fin.sum_univ_succ]
  ring

lemma frob_sub_left (A B C : Mat3) : frob (A - B) C = frob A C - frob B C := by
  simp [frob, Fin.sum_univ_succ]
  ring

lemma frob_neg_left (A B : Mat3) : frob (-A) B = -frob A B := by
  simp [frob, Fin.sum_univ_succ]
  ring

lemma frob_smul_left (c : ℝ) (A B : Mat3) : frob (c • A) B = c * frob A B := by
  simp [frob, Fin.sum_univ_succ]
  ring

lemma frob_mul_left (A B C : Mat3) :
    frob (A * B) C = frob B (Aᵀ * C) := by
  simp [frob, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

lemma frob_mul_right (A B C : Mat3) :
    frob A (B * C) = frob (A * Cᵀ) B := by
  simp [frob, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

lemma frob_zero_left (A : Mat3) : frob 0 A = 0 := by simp [frob]

lemma frob_eq_zero_of_eq_zero {A : Mat3} (hA : A = 0) (B : Mat3) : frob A B = 0 := by
  rw [hA, frob_zero_left]

lemma dcof_self_adjoint (A H K : Mat3) :
    frob (dcof A H) K = frob H (dcof A K) := by
  simp [frob, dcof, Fin.sum_univ_succ]
  ring

lemma dcof_self (A : Mat3) : dcof A A = (2 : ℝ) • cofactor3 A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dcof, cofactor3] <;> ring

lemma dcof_mul_transpose (A H : Mat3) :
    dcof A H * Aᵀ =
      frob (cofactor3 A) H • (1 : Mat3) - cofactor3 A * Hᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dcof, cofactor3, frob, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> ring

lemma dcof_transpose (A H : Mat3) :
    dcof Aᵀ Hᵀ = (dcof A H)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dcof] <;> ring

lemma dcof_isHermitian {A H : Mat3} (hA : A.IsHermitian)
    (hH : H.IsHermitian) : (dcof A H).IsHermitian := by
  have hAt : Aᵀ = A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hHt : Hᵀ = H := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.eq
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
    ← dcof_transpose, hAt, hHt]

lemma residual_expand (d : EulerData) :
    residual d.P d.Q d.M = cofactor3 d.M * d.P - d.Q * d.M := rfl

lemma cofactor3_eq_det_smul_inv {A : Mat3} (hA : A.PosDef) :
    cofactor3 A = A.det • A⁻¹ := by
  have hAu : IsUnit A := hA.isUnit
  have hAtu : IsUnit Aᵀ := (Matrix.isUnit_transpose A).2 hAu
  have hAdetu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAu
  apply hAtu.mul_right_cancel
  rw [cofactor3_mul_transpose]
  have hAt : Aᵀ = A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  rw [hAt]
  calc
    A.det • (1 : Mat3) = A.det • (A⁻¹ * A) := by
      rw [A.nonsing_inv_mul hAdetu]
    _ = (A.det • A⁻¹) * A := by rw [Matrix.smul_mul]

lemma cofactor3_posDef {A : Mat3} (hA : A.PosDef) : (cofactor3 A).PosDef := by
  rw [cofactor3_eq_det_smul_inv hA]
  exact hA.inv.smul hA.det_pos

noncomputable def rhoP (d : EulerData) : ℝ := 2 * d.kappa / d.P.det
noncomputable def rhoQ (d : EulerData) : ℝ := 2 * d.kappa / d.Q.det

lemma rhoP_pos (d : EulerData) : 0 < rhoP d := by
  exact div_pos (mul_pos two_pos d.kappa_pos) d.P_pos.det_pos

lemma rhoQ_pos (d : EulerData) : 0 < rhoQ d := by
  exact div_pos (mul_pos two_pos d.kappa_pos) d.Q_pos.det_pos

lemma cofactor3_rhoQ_smul (d : EulerData) :
    cofactor3 (rhoQ d • d.Q) = (rhoQ d) ^ 2 • cofactor3 d.Q :=
  cofactor3_smul _ _

lemma q_kop_identity (d : EulerData) :
    kop (rhoQ d • d.Q) = rhoQ d •
      (residual d.P d.Q d.M * d.Mᵀ +
        d.M * (residual d.P d.Q d.M)ᵀ) := by
  let R := residual d.P d.Q d.M
  have hgrad := d.gradQ
  have hcof := cofactor3_eq_det_smul_inv d.Q_pos
  let S : Mat3 := R * d.Mᵀ + d.M * Rᵀ
  have hS : S = (2 * d.kappa) • d.Q⁻¹ -
      (2 * d.Q.trace) • (1 : Mat3) + (4 : ℝ) • d.Q := by
    ext i j
    have hij := congrFun (congrFun hgrad i) j
    simp only [S, R, Matrix.add_apply, Matrix.sub_apply, real_smul_apply,
      Matrix.one_apply] at hij ⊢
    linear_combination 2 * hij
  rw [kop, cofactor3_rhoQ_smul]
  rw [hcof]
  change (rhoQ d) ^ 2 • (d.Q.det • d.Q⁻¹) -
      (2 : ℝ) • ((rhoQ d • d.Q).trace • (1 : Mat3)) +
      (4 : ℝ) • (rhoQ d • d.Q) = rhoQ d • S
  rw [hS]
  have hdet : d.Q.det ≠ 0 := ne_of_gt d.Q_pos.det_pos
  have hscalar : (rhoQ d) ^ 2 * d.Q.det = rhoQ d * (2 * d.kappa) := by
    dsimp [rhoQ]
    field_simp [hdet]
  have hfirst : (rhoQ d) ^ 2 • (d.Q.det • d.Q⁻¹) =
      rhoQ d • ((2 * d.kappa) • d.Q⁻¹) := by
    rw [smul_smul, smul_smul, hscalar]
  rw [hfirst, Matrix.trace_smul]
  module

def alpha (d : EulerData) : ℝ :=
  frob (residual d.P d.Q d.M) (cofactor3 d.M * d.P)

def ell (d : EulerData) : ℝ := ((d.Mᵀ * d.M) * lop' d.P).trace

def beta (d : EulerData) : ℝ :=
  frob (residual d.P d.Q d.M) (d.Q * d.M)

def radialXsq (d : EulerData) : ℝ :=
  frobNormSq (cofactor3 d.M * d.P)

def radialYsq (d : EulerData) : ℝ :=
  frobNormSq (d.Q * d.M)

def radialPair (d : EulerData) : ℝ :=
  frob (cofactor3 d.M * d.P) (d.Q * d.M)

noncomputable def radialX (d : EulerData) : ℝ := Real.sqrt (radialXsq d)

noncomputable def radialY (d : EulerData) : ℝ := Real.sqrt (radialYsq d)

lemma frobNormSq_nonneg (A : Mat3) : 0 ≤ frobNormSq A := by
  simp only [frobNormSq, frob]
  exact Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _

lemma frobNormSq_eq_zero_iff (A : Mat3) : frobNormSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [frobNormSq, frob, Fin.sum_univ_succ] at h ⊢ <;> nlinarith
  · rintro rfl
    simp [frobNormSq, frob]

lemma radialX_sq (d : EulerData) : (radialX d) ^ 2 = radialXsq d := by
  exact Real.sq_sqrt (frobNormSq_nonneg _)

lemma radialY_sq (d : EulerData) : (radialY d) ^ 2 = radialYsq d := by
  exact Real.sq_sqrt (frobNormSq_nonneg _)

lemma radialX_nonneg (d : EulerData) : 0 ≤ radialX d := Real.sqrt_nonneg _

lemma radialY_nonneg (d : EulerData) : 0 ≤ radialY d := Real.sqrt_nonneg _

lemma radial_cauchy (d : EulerData) :
    radialPair d ≤ radialX d * radialY d := by
  let A := cofactor3 d.M * d.P
  let B := d.Q * d.M
  have h := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (I3 × I3))
    (fun ij ↦ A ij.1 ij.2) (fun ij ↦ B ij.1 ij.2)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_prod_type] at h
  change frob A B ≤ Real.sqrt (frobNormSq A) * Real.sqrt (frobNormSq B)
  simpa [frob, frobNormSq, radialPair, radialX, radialY, A, B,
    pow_two] using h

lemma alpha_eq_radial (d : EulerData) :
    alpha d = radialXsq d - radialPair d := by
  simp [alpha, radialXsq, radialPair, residual, frobNormSq, frob,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

lemma beta_eq_radial (d : EulerData) :
    beta d = radialPair d - radialYsq d := by
  simp [beta, radialYsq, radialPair, residual, frobNormSq, frob,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

lemma lop'_isHermitian {P : Mat3} (hP : P.IsHermitian) :
    (lop' P).IsHermitian := by
  have hPt : Pᵀ = P := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.eq
  have hcoft : (cofactor3 P)ᵀ = cofactor3 P := by
    rw [← cofactor3_transpose, hPt]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [lop', Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_mul, hPt, hcoft]

lemma frob_M_lop_M_eq_ell (d : EulerData) :
    frob (d.M * lop' d.P) d.M = ell d := by
  rw [frob_eq_trace]
  have hLt : (lop' d.P)ᵀ = lop' d.P := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (lop'_isHermitian d.P_pos.isHermitian).eq
  rw [Matrix.transpose_mul, hLt]
  change (lop' d.P * d.Mᵀ * d.M).trace = ((d.Mᵀ * d.M) * lop' d.P).trace
  calc
    (lop' d.P * d.Mᵀ * d.M).trace =
        (d.M * lop' d.P * d.Mᵀ).trace :=
      Matrix.trace_mul_cycle (lop' d.P) d.Mᵀ d.M
    _ = (d.Mᵀ * d.M * lop' d.P).trace :=
      Matrix.trace_mul_cycle d.M (lop' d.P) d.Mᵀ

lemma frob_dcof_radial_eq (d : EulerData) :
    frob (dcof d.M (residual d.P d.Q d.M * d.P)) d.M = 2 * alpha d := by
  rw [dcof_self_adjoint, dcof_self]
  have hPt : d.Pᵀ = d.P := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using d.P_pos.isHermitian.eq
  calc
    frob (residual d.P d.Q d.M * d.P) ((2 : ℝ) • cofactor3 d.M) =
        frob ((2 : ℝ) • cofactor3 d.M)
          (residual d.P d.Q d.M * d.P) := frob_symm _ _
    _ = 2 * frob (cofactor3 d.M)
          (residual d.P d.Q d.M * d.P) := frob_smul_left _ _ _
    _ = 2 * frob (residual d.P d.Q d.M)
          (cofactor3 d.M * d.P) := by
      rw [frob_mul_right, hPt, frob_symm]
    _ = 2 * alpha d := rfl

lemma frob_QR_M_eq_beta (d : EulerData) :
    frob (d.Q * residual d.P d.Q d.M) d.M = beta d := by
  rw [frob_mul_left]
  have hQt : d.Qᵀ = d.Q := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using d.Q_pos.isHermitian.eq
  rw [hQt]
  rfl

lemma radial_balance (d : EulerData) : ell d + 2 * alpha d - beta d = 0 := by
  have h := congrArg (fun X : Mat3 ↦ frob X d.M) d.gradM
  rw [frob_zero_left, frob_add_left, frob_sub_left,
    frob_neg_left, frob_M_lop_M_eq_ell, frob_dcof_radial_eq,
    frob_QR_M_eq_beta] at h
  linarith

lemma radial_pair_identity (d : EulerData) :
    3 * radialPair d = 2 * radialX d ^ 2 + radialY d ^ 2 + ell d := by
  rw [radialX_sq, radialY_sq]
  have h := radial_balance d
  rw [alpha_eq_radial, beta_eq_radial] at h
  linarith

lemma cofactor_mul_P_ne_zero (d : EulerData) (hC : cofactor3 d.M ≠ 0) :
    cofactor3 d.M * d.P ≠ 0 := by
  intro hCP
  apply hC
  have hPdet : IsUnit d.P.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt d.P_pos.det_pos)
  calc
    cofactor3 d.M = cofactor3 d.M * 1 := by simp
    _ = cofactor3 d.M * (d.P * d.P⁻¹) := by
      rw [d.P.mul_nonsing_inv hPdet]
    _ = (cofactor3 d.M * d.P) * d.P⁻¹ := by noncomm_ring
    _ = 0 := by rw [hCP]; simp

lemma radialX_pos_of_cofactor_ne_zero (d : EulerData)
    (hC : cofactor3 d.M ≠ 0) : 0 < radialX d := by
  apply Real.sqrt_pos.2
  have hnonneg := frobNormSq_nonneg (cofactor3 d.M * d.P)
  have hne : radialXsq d ≠ 0 := by
    intro hz
    apply cofactor_mul_P_ne_zero d hC
    exact (frobNormSq_eq_zero_iff _).mp hz
  change 0 < radialXsq d
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

lemma radial_alpha_strict_of_cofactor_ne_zero (d : EulerData)
    (hC : cofactor3 d.M ≠ 0) (hell : 0 < ell d) :
    alpha d < -ell d := by
  apply S3xS3.Trivial.radial_alpha_strict hell
    (radialX_pos_of_cofactor_ne_zero d hC)
  · exact radial_pair_identity d
  · exact radial_cauchy d
  · rw [alpha_eq_radial, radialX_sq]

def lopDiag (p : I3 → ℝ) : I3 → ℝ :=
  ![(p 1 - p 2) ^ 2, (p 2 - p 0) ^ 2, (p 0 - p 1) ^ 2]

lemma lop'_diagonal (p : I3 → ℝ) :
    lop' (Matrix.diagonal p) = Matrix.diagonal (lopDiag p) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lop', lopDiag, cofactor3, Matrix.trace, Fin.sum_univ_succ] <;> ring

lemma lop'_conjugate_so3 (P : Mat3) (U : SO3) :
    lop' ((U : Mat3)ᵀ * P * U) =
      (U : Mat3)ᵀ * lop' P * U := by
  let T : Mat3 := U
  have hTT : T * Tᵀ = 1 := so3_mul_transpose U
  have hTtT : Tᵀ * T = 1 := so3_transpose_mul U
  have hsq : (Tᵀ * P * T) * (Tᵀ * P * T) = Tᵀ * (P * P) * T := by
    calc
      (Tᵀ * P * T) * (Tᵀ * P * T) =
          Tᵀ * P * (T * Tᵀ) * P * T := by noncomm_ring
      _ = Tᵀ * (P * P) * T := by rw [hTT]; simp; noncomm_ring
  have htrace : (Tᵀ * (P * P) * T).trace = (P * P).trace := by
    calc
      (Tᵀ * (P * P) * T).trace = (T * Tᵀ * (P * P)).trace :=
        Matrix.trace_mul_cycle Tᵀ (P * P) T
      _ = (P * P).trace := by rw [hTT]; simp
  have hcof : cofactor3 (Tᵀ * P * T) = Tᵀ * cofactor3 P * T := by
    exact cofactor3_so3_conjugate U P
  rw [lop', lop', hsq, htrace, hcof]
  have hone : Tᵀ * (1 : Mat3) * T = 1 := by
    rw [Matrix.mul_one, hTtT]
  calc
    (P * P).trace • (1 : Mat3) - Tᵀ * (P * P) * T -
          (2 : ℝ) • (Tᵀ * cofactor3 P * T) =
        Tᵀ * ((P * P).trace • (1 : Mat3)) * T -
          Tᵀ * (P * P) * T -
          Tᵀ * ((2 : ℝ) • cofactor3 P) * T := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, hone]
    _ = Tᵀ * ((P * P).trace • (1 : Mat3) - P * P -
          (2 : ℝ) • cofactor3 P) * T := by noncomm_ring

lemma lopDiag_nonneg (p : I3 → ℝ) (i : I3) : 0 ≤ lopDiag p i := by
  fin_cases i <;> simp only [lopDiag] <;> exact sq_nonneg _

lemma lop'_posSemidef {P : Mat3} (hP : P.PosDef) :
    (lop' P).PosSemidef := by
  obtain ⟨U, p, hp, hdiagP⟩ := diagonalize_posDef_three hP
  have hdiagL : (U : Mat3)ᵀ * lop' P * U = Matrix.diagonal (lopDiag p) := by
    rw [← lop'_conjugate_so3, hdiagP, lop'_diagonal]
  have hdiagPSD : (Matrix.diagonal (lopDiag p)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (lopDiag_nonneg p)
  have hrepr : lop' P = (U : Mat3) * Matrix.diagonal (lopDiag p) * (U : Mat3)ᵀ := by
    rw [← hdiagL]
    symm
    calc
      (U : Mat3) * ((U : Mat3)ᵀ * lop' P * U) * (U : Mat3)ᵀ =
          ((U : Mat3) * (U : Mat3)ᵀ) * lop' P *
            ((U : Mat3) * (U : Mat3)ᵀ) := by noncomm_ring
      _ = lop' P := by rw [so3_mul_transpose]; simp
  rw [hrepr]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hdiagPSD.mul_mul_conjTranspose_same (U : Mat3)

lemma masterPositive_posSemidef (d : EulerData) :
    (d.M * lop' d.P * d.Mᵀ).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (lop'_posSemidef d.P_pos).mul_mul_conjTranspose_same d.M

lemma masterPositive_trace (d : EulerData) :
    (d.M * lop' d.P * d.Mᵀ).trace = ell d := by
  exact Matrix.trace_mul_cycle d.M (lop' d.P) d.Mᵀ

lemma ell_nonneg (d : EulerData) : 0 ≤ ell d := by
  rw [← masterPositive_trace]
  exact (masterPositive_posSemidef d).trace_nonneg

lemma trace_smul_one_sub_posSemidef_three {A : Mat3}
    (hA : A.PosSemidef) :
    (A.trace • (1 : Mat3) - A).PosSemidef := by
  let U : Mat3 := hA.isHermitian.eigenvectorUnitary
  let s : I3 → ℝ := hA.isHermitian.eigenvalues
  have hs : ∀ i, 0 ≤ s i := hA.eigenvalues_nonneg
  have hUtU : Uᵀ * U = 1 := by
    change (hA.isHermitian.eigenvectorUnitary : Mat3)ᵀ *
      hA.isHermitian.eigenvectorUnitary = 1
    simpa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hUUt : U * Uᵀ = 1 := by
    change (hA.isHermitian.eigenvectorUnitary : Mat3) *
      (hA.isHermitian.eigenvectorUnitary : Mat3)ᵀ = 1
    simpa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hA.isHermitian.eigenvectorUnitary
  have hspect : A = U * Matrix.diagonal s * Uᵀ := by
    simpa [U, s, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.isHermitian.spectral_theorem
  have htrace : A.trace = s 0 + s 1 + s 2 := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    simp [s, Fin.sum_univ_succ]
    ring
  let r : I3 → ℝ := fun i ↦ A.trace - s i
  have hr : ∀ i, 0 ≤ r i := by
    intro i
    fin_cases i <;> simp [r] <;> rw [htrace] <;>
      nlinarith [hs 0, hs 1, hs 2]
  have hdiag : Matrix.diagonal r =
      A.trace • (1 : Mat3) - Matrix.diagonal s := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [r]
    · simp [Matrix.diagonal, hij]
  have hrepr : A.trace • (1 : Mat3) - A =
      U * Matrix.diagonal r * Uᵀ := by
    calc
      A.trace • (1 : Mat3) - A =
          A.trace • (1 : Mat3) - U * Matrix.diagonal s * Uᵀ := by rw [hspect]
      _ =
          A.trace • (U * Uᵀ) - U * Matrix.diagonal s * Uᵀ := by rw [hUUt]
      _ = U * (A.trace • (1 : Mat3) - Matrix.diagonal s) * Uᵀ := by
        symm
        calc
          U * (A.trace • (1 : Mat3) - Matrix.diagonal s) * Uᵀ =
              U * (A.trace • (1 : Mat3)) * Uᵀ -
                U * Matrix.diagonal s * Uᵀ := by noncomm_ring
          _ = A.trace • (U * (1 : Mat3) * Uᵀ) -
                U * Matrix.diagonal s * Uᵀ := by
            rw [Matrix.mul_smul, Matrix.smul_mul]
          _ = A.trace • (U * Uᵀ) - U * Matrix.diagonal s * Uᵀ := by simp
      _ = U * Matrix.diagonal r * Uᵀ := by rw [hdiag]
  rw [hrepr]
  have hd : (Matrix.diagonal r).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr hr
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same U

lemma quad3_eq_dotProduct (A : Mat3) (v : Vec3) :
    S3xS3.Trivial.quad3 A v = v ⬝ᵥ (A *ᵥ v) := by
  simp only [S3xS3.Trivial.quad3, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma normSq3_eq_dotProduct (v : Vec3) :
    S3xS3.Trivial.normSq3 v = v ⬝ᵥ v := by
  simp [S3xS3.Trivial.normSq3, dotProduct, pow_two]

lemma normSq3_pos {v : Vec3} (hv : v ≠ 0) :
    0 < S3xS3.Trivial.normSq3 v := by
  have hnonneg : 0 ≤ S3xS3.Trivial.normSq3 v := by
    simp [S3xS3.Trivial.normSq3]
    positivity
  apply lt_of_le_of_ne hnonneg
  intro hz
  apply hv
  funext i
  fin_cases i <;>
    simp [S3xS3.Trivial.normSq3, Fin.sum_univ_succ] at hz ⊢ <;> nlinarith

lemma quad3_trace_bound {A : Mat3} (hA : A.PosSemidef) (v : Vec3) :
    S3xS3.Trivial.quad3 A v ≤
      A.trace * S3xS3.Trivial.normSq3 v := by
  have h := (trace_smul_one_sub_posSemidef_three hA).dotProduct_mulVec_nonneg v
  have h' : 0 ≤ v ⬝ᵥ ((A.trace • (1 : Mat3) - A) *ᵥ v) := by
    simpa using h
  have hid : v ⬝ᵥ ((A.trace • (1 : Mat3) - A) *ᵥ v) =
      A.trace * S3xS3.Trivial.normSq3 v -
        S3xS3.Trivial.quad3 A v := by
    simp [S3xS3.Trivial.quad3, S3xS3.Trivial.normSq3,
      Matrix.mulVec, dotProduct, Matrix.trace, Fin.sum_univ_succ]
    ring
  rw [hid] at h'
  nlinarith

lemma selfTranspose_quad_nonneg (R : Mat3) (v : Vec3) :
    0 ≤ S3xS3.Trivial.quad3 (R * Rᵀ) v := by
  have hpsd : (R * Rᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose R
  rw [quad3_eq_dotProduct]
  exact hpsd.dotProduct_mulVec_nonneg v

lemma quad3_master_rhs_neg (d : EulerData)
    (halpha : alpha d < -ell d) {v : Vec3} (hv : v ≠ 0) :
    S3xS3.Trivial.quad3
      (d.M * lop' d.P * d.Mᵀ + alpha d • (1 : Mat3) -
        residual d.P d.Q d.M * (residual d.P d.Q d.M)ᵀ) v < 0 := by
  have hbound := quad3_trace_bound (masterPositive_posSemidef d) v
  rw [masterPositive_trace] at hbound
  have hres := selfTranspose_quad_nonneg (residual d.P d.Q d.M) v
  have hvpos := normSq3_pos hv
  have hid : S3xS3.Trivial.quad3
      (d.M * lop' d.P * d.Mᵀ + alpha d • (1 : Mat3) -
        residual d.P d.Q d.M * (residual d.P d.Q d.M)ᵀ) v =
      S3xS3.Trivial.quad3 (d.M * lop' d.P * d.Mᵀ) v +
        alpha d * S3xS3.Trivial.normSq3 v -
          S3xS3.Trivial.quad3
            (residual d.P d.Q d.M * (residual d.P d.Q d.M)ᵀ) v := by
    simp [S3xS3.Trivial.quad3, S3xS3.Trivial.normSq3,
      Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  rw [hid]
  nlinarith

lemma quad3_smul (c : ℝ) (A : Mat3) (v : Vec3) :
    S3xS3.Trivial.quad3 (c • A) v =
      c * S3xS3.Trivial.quad3 A v := by
  simp [S3xS3.Trivial.quad3, Fin.sum_univ_succ]
  ring

def kopDiag (h : I3 → ℝ) : I3 → ℝ :=
  ![h 1 * h 2 - 2 * h 1 - 2 * h 2 + 2 * h 0,
    h 0 * h 2 - 2 * h 0 - 2 * h 2 + 2 * h 1,
    h 0 * h 1 - 2 * h 0 - 2 * h 1 + 2 * h 2]

lemma kop_diagonal (h : I3 → ℝ) :
    kop (Matrix.diagonal h) = Matrix.diagonal (kopDiag h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kop, kopDiag, cofactor3, Matrix.trace, Fin.sum_univ_succ] <;> ring

lemma kop_conjugate_so3 (H : Mat3) (U : SO3) :
    kop ((U : Mat3)ᵀ * H * U) =
      (U : Mat3)ᵀ * kop H * U := by
  let T : Mat3 := U
  have hTtT : Tᵀ * T = 1 := so3_transpose_mul U
  have hTT : T * Tᵀ = 1 := so3_mul_transpose U
  have htrace : (Tᵀ * H * T).trace = H.trace := by
    calc
      (Tᵀ * H * T).trace = (T * Tᵀ * H).trace :=
        Matrix.trace_mul_cycle Tᵀ H T
      _ = H.trace := by rw [hTT]; simp
  have hcof : cofactor3 (Tᵀ * H * T) = Tᵀ * cofactor3 H * T :=
    cofactor3_so3_conjugate U H
  rw [kop, kop, htrace, hcof]
  have hone : Tᵀ * (1 : Mat3) * T = 1 := by rw [Matrix.mul_one, hTtT]
  calc
    Tᵀ * cofactor3 H * T -
          (2 : ℝ) • (H.trace • (1 : Mat3)) +
          (4 : ℝ) • (Tᵀ * H * T) =
        Tᵀ * cofactor3 H * T -
          Tᵀ * ((2 : ℝ) • (H.trace • (1 : Mat3))) * T +
          Tᵀ * ((4 : ℝ) • H) * T := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hone]
    _ = Tᵀ * (cofactor3 H -
          (2 : ℝ) • (H.trace • (1 : Mat3)) + (4 : ℝ) • H) * T := by
      noncomm_ring

def basis3 (i : I3) : Vec3 := fun j ↦ if j = i then 1 else 0

lemma basis3_ne_zero (i : I3) : basis3 i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [basis3] at hi

lemma so3_mulVec_basis_ne_zero (U : SO3) (i : I3) :
    (U : Mat3) *ᵥ basis3 i ≠ 0 := by
  intro h
  have hh := congrArg (fun v : Vec3 ↦ (U : Mat3)ᵀ *ᵥ v) h
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero, so3_transpose_mul,
    Matrix.one_mulVec] at hh
  exact basis3_ne_zero i hh

lemma quad3_conjugate (A U : Mat3) (v : Vec3) :
    S3xS3.Trivial.quad3 (Uᵀ * A * U) v =
      S3xS3.Trivial.quad3 A (U *ᵥ v) := by
  simp [S3xS3.Trivial.quad3, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring

lemma quad3_diagonal_basis (a : I3 → ℝ) (i : I3) :
    S3xS3.Trivial.quad3 (Matrix.diagonal a) (basis3 i) = a i := by
  fin_cases i <;>
    simp [S3xS3.Trivial.quad3, basis3]

lemma neg_kop_posDef_of_q_mul_kop_neg {Q : Mat3} (hQ : Q.PosDef)
    {rho : ℝ} (_hrho : 0 < rho)
    (hneg : ∀ v : Vec3, v ≠ 0 →
      S3xS3.Trivial.quad3 (Q * kop (rho • Q)) v < 0) :
    (-kop (rho • Q)).PosDef := by
  obtain ⟨U, q, hq, hdiagQ⟩ := diagonalize_posDef_three hQ
  let h : I3 → ℝ := fun i ↦ rho * q i
  let k : I3 → ℝ := kopDiag h
  have hdiagH : (U : Mat3)ᵀ * (rho • Q) * U = Matrix.diagonal h := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hdiagQ]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [h]
    · simp [Matrix.diagonal, hij]
  have hdiagK : (U : Mat3)ᵀ * kop (rho • Q) * U = Matrix.diagonal k := by
    rw [← kop_conjugate_so3, hdiagH, kop_diagonal]
  have hdiagQK : (U : Mat3)ᵀ * (Q * kop (rho • Q)) * U =
      Matrix.diagonal q * Matrix.diagonal k := by
    calc
      (U : Mat3)ᵀ * (Q * kop (rho • Q)) * U =
          ((U : Mat3)ᵀ * Q * U) *
            ((U : Mat3)ᵀ * kop (rho • Q) * U) := by
        calc
          _ = (U : Mat3)ᵀ * Q *
              ((U : Mat3) * (U : Mat3)ᵀ) * kop (rho • Q) * U := by
            rw [so3_mul_transpose]; simp; noncomm_ring
          _ = _ := by noncomm_ring
      _ = _ := by rw [hdiagQ, hdiagK]
  have hk : ∀ i, k i < 0 := by
    intro i
    have hi := hneg ((U : Mat3) *ᵥ basis3 i)
      (so3_mulVec_basis_ne_zero U i)
    rw [← quad3_conjugate (Q * kop (rho • Q)) (U : Mat3) (basis3 i),
      hdiagQK, Matrix.diagonal_mul_diagonal, quad3_diagonal_basis] at hi
    have hqi := hq i
    nlinarith
  have hdiagPos : (-Matrix.diagonal k).PosDef := by
    rw [Matrix.diagonal_neg]
    exact Matrix.posDef_diagonal_iff.mpr fun i ↦ by
      have := hk i
      simp
      linarith
  have hrepr : -kop (rho • Q) =
      (U : Mat3) * (-Matrix.diagonal k) * (U : Mat3)ᵀ := by
    have hKrepr : kop (rho • Q) =
        (U : Mat3) * Matrix.diagonal k * (U : Mat3)ᵀ := by
      symm
      rw [← hdiagK]
      calc
        (U : Mat3) * ((U : Mat3)ᵀ * kop (rho • Q) * U) * (U : Mat3)ᵀ =
            ((U : Mat3) * (U : Mat3)ᵀ) * kop (rho • Q) *
              ((U : Mat3) * (U : Mat3)ᵀ) := by noncomm_ring
        _ = kop (rho • Q) := by rw [so3_mul_transpose]; simp
    rw [hKrepr]
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  rw [hrepr]
  have hUunit : IsUnit (U : Mat3) :=
    IsUnit.of_mul_eq_one (U : Mat3)ᵀ (so3_mul_transpose U)
  have hinj : Function.Injective (fun v ↦ Matrix.vecMul v (U : Mat3)) :=
    Matrix.vecMul_injective_iff_isUnit.mpr hUunit
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hdiagPos.mul_mul_conjTranspose_same hinj

lemma threshold_four_two_others {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hat : a ≤ t) (hbt : b ≤ t)
    (ht : 4 ≤ t) :
    0 < a * b - 2 * a - 2 * b + 2 * t := by
  by_cases hab : a ≤ b
  · exact S3xS3.Trivial.threshold_four_scalar ha hab hbt ht
  · have hba : b ≤ a := le_of_not_ge hab
    have h := S3xS3.Trivial.threshold_four_scalar hb hba hat ht
    nlinarith

lemma strictBelowFour_of_neg_kop {H : Mat3} (hH : H.PosDef)
    (hnegK : (-kop H).PosDef) : S3xS3.Trivial.StrictBelowFour H := by
  obtain ⟨U, h, hh, hdiagH⟩ := diagonalize_posDef_three hH
  let k : I3 → ℝ := kopDiag h
  have hdiagK : (U : Mat3)ᵀ * kop H * U = Matrix.diagonal k := by
    rw [← kop_conjugate_so3, hdiagH, kop_diagonal]
  have hUunit : IsUnit (U : Mat3) :=
    IsUnit.of_mul_eq_one (U : Mat3)ᵀ (so3_mul_transpose U)
  have hUinj : Function.Injective (U : Mat3).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hUunit
  have hconjNeg : ((U : Mat3)ᵀ * (-kop H) * U).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hnegK.conjTranspose_mul_mul_same hUinj
  have hdiagNeg : (-Matrix.diagonal k).PosDef := by
    have heq : (U : Mat3)ᵀ * (-kop H) * U = -Matrix.diagonal k := by
      rw [← hdiagK]
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_succ]
      ring
    rw [← heq]
    exact hconjNeg
  have hk : ∀ i, k i < 0 := by
    have hd : (Matrix.diagonal (fun i ↦ -k i)).PosDef := by
      simpa [Matrix.diagonal_neg] using hdiagNeg
    have hp := Matrix.posDef_diagonal_iff.mp hd
    intro i
    have hi := hp i
    exact neg_pos.mp hi
  have hall : h 0 < 4 ∧ h 1 < 4 ∧ h 2 < 4 := by
    by_cases h01 : h 0 ≤ h 1
    · by_cases h12 : h 1 ≤ h 2
      · have ht : h 2 < 4 := by
          by_contra hn
          have hp := threshold_four_two_others (hh 0) (hh 1)
            (h01.trans h12) h12 (le_of_not_gt hn)
          have hkn := hk 2
          simp [k, kopDiag] at hkn
          nlinarith
        exact ⟨lt_of_le_of_lt (h01.trans h12) ht,
          lt_of_le_of_lt h12 ht, ht⟩
      · have h21 : h 2 ≤ h 1 := le_of_not_ge h12
        have ht : h 1 < 4 := by
          by_contra hn
          have hp := threshold_four_two_others (hh 0) (hh 2)
            h01 h21 (le_of_not_gt hn)
          have hkn := hk 1
          simp [k, kopDiag] at hkn
          nlinarith
        exact ⟨lt_of_le_of_lt h01 ht, ht, lt_of_le_of_lt h21 ht⟩
    · have h10 : h 1 ≤ h 0 := le_of_not_ge h01
      by_cases h20 : h 2 ≤ h 0
      · have ht : h 0 < 4 := by
          by_contra hn
          have hp := threshold_four_two_others (hh 1) (hh 2)
            h10 h20 (le_of_not_gt hn)
          have hkn := hk 0
          simp [k, kopDiag] at hkn
          nlinarith
        exact ⟨ht, lt_of_le_of_lt h10 ht, lt_of_le_of_lt h20 ht⟩
      · have h02 : h 0 ≤ h 2 := le_of_not_ge h20
        have h12' : h 1 ≤ h 2 := h10.trans h02
        have ht : h 2 < 4 := by
          by_contra hn
          have hp := threshold_four_two_others (hh 0) (hh 1)
            h02 h12' (le_of_not_gt hn)
          have hkn := hk 2
          simp [k, kopDiag] at hkn
          nlinarith
        exact ⟨lt_of_le_of_lt h02 ht, lt_of_le_of_lt h12' ht, ht⟩
  let r : I3 → ℝ := fun i ↦ 4 - h i
  have hr : ∀ i, 0 < r i := by
    intro i
    fin_cases i <;> simp [r] <;> linarith [hall.1, hall.2.1, hall.2.2]
  have hdiagPos : (Matrix.diagonal r).PosDef :=
    Matrix.posDef_diagonal_iff.mpr hr
  have hHrepr : H =
      (U : Mat3) * Matrix.diagonal h * (U : Mat3)ᵀ := by
    symm
    rw [← hdiagH]
    calc
      (U : Mat3) * ((U : Mat3)ᵀ * H * U) * (U : Mat3)ᵀ =
          ((U : Mat3) * (U : Mat3)ᵀ) * H *
            ((U : Mat3) * (U : Mat3)ᵀ) := by noncomm_ring
      _ = H := by rw [so3_mul_transpose]; simp
  have hdiffrepr : (4 : ℝ) • (1 : Mat3) - H =
      (U : Mat3) * Matrix.diagonal r * (U : Mat3)ᵀ := by
    have hdiagR : Matrix.diagonal r =
        (4 : ℝ) • (1 : Mat3) - Matrix.diagonal h := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [r]
      · simp [Matrix.diagonal, hij]
    calc
      (4 : ℝ) • (1 : Mat3) - H =
          (4 : ℝ) • (1 : Mat3) -
            (U : Mat3) * Matrix.diagonal h * (U : Mat3)ᵀ := by rw [hHrepr]
      _ = (4 : ℝ) • ((U : Mat3) * (U : Mat3)ᵀ) -
            (U : Mat3) * Matrix.diagonal h * (U : Mat3)ᵀ := by
        rw [so3_mul_transpose]
      _ = (U : Mat3) * ((4 : ℝ) • (1 : Mat3) -
            Matrix.diagonal h) * (U : Mat3)ᵀ := by
        symm
        calc
          (U : Mat3) * ((4 : ℝ) • (1 : Mat3) - Matrix.diagonal h) *
                (U : Mat3)ᵀ =
              (U : Mat3) * ((4 : ℝ) • (1 : Mat3)) * (U : Mat3)ᵀ -
                (U : Mat3) * Matrix.diagonal h * (U : Mat3)ᵀ := by
                  noncomm_ring
          _ = (4 : ℝ) • ((U : Mat3) * (1 : Mat3) * (U : Mat3)ᵀ) -
                (U : Mat3) * Matrix.diagonal h * (U : Mat3)ᵀ := by
                  rw [Matrix.mul_smul, Matrix.smul_mul]
          _ = (4 : ℝ) • ((U : Mat3) * (U : Mat3)ᵀ) -
                (U : Mat3) * Matrix.diagonal h * (U : Mat3)ᵀ := by simp
      _ = (U : Mat3) * Matrix.diagonal r * (U : Mat3)ᵀ := by rw [hdiagR]
  have hdiffPos : ((4 : ℝ) • (1 : Mat3) - H).PosDef := by
    rw [hdiffrepr]
    have hvecInj : Function.Injective
        (fun v ↦ Matrix.vecMul v (U : Mat3)) :=
      Matrix.vecMul_injective_iff_isUnit.mpr hUunit
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hdiagPos.mul_mul_conjTranspose_same hvecInj
  intro v hv
  have hquad := hdiffPos.dotProduct_mulVec_pos hv
  have hquad' : 0 < v ⬝ᵥ (((4 : ℝ) • (1 : Mat3) - H) *ᵥ v) := by
    simpa using hquad
  have hid : v ⬝ᵥ (((4 : ℝ) • (1 : Mat3) - H) *ᵥ v) =
      4 * S3xS3.Trivial.normSq3 v - S3xS3.Trivial.quad3 H v := by
    simp [S3xS3.Trivial.quad3, S3xS3.Trivial.normSq3,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  rw [hid] at hquad'
  linarith

lemma left_mul_posDef_ne_zero {Q M : Mat3} (hQ : Q.PosDef) (hM : M ≠ 0) :
    Q * M ≠ 0 := by
  intro hQM
  apply hM
  have hQdet : IsUnit Q.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hQ.det_pos)
  calc
    M = 1 * M := by simp
    _ = (Q⁻¹ * Q) * M := by rw [Q.nonsing_inv_mul hQdet]
    _ = Q⁻¹ * (Q * M) := by noncomm_ring
    _ = 0 := by rw [hQM]; simp

lemma no_eulerData_cofactor_zero_nonzero (d : EulerData)
    (hC : cofactor3 d.M = 0) (hM : d.M ≠ 0) : False := by
  have hA : alpha d = 0 := by
    simp [alpha, hC, frob]
  have hB : beta d = -radialYsq d := by
    rw [beta_eq_radial]
    have hpair : radialPair d = 0 := by simp [radialPair, hC, frob]
    rw [hpair]
    ring
  have hYne : radialYsq d ≠ 0 := by
    intro hY
    have hzero := (frobNormSq_eq_zero_iff (d.Q * d.M)).mp hY
    exact left_mul_posDef_ne_zero d.Q_pos hM hzero
  have hYpos : 0 < radialYsq d :=
    lt_of_le_of_ne (frobNormSq_nonneg _) (Ne.symm hYne)
  have hb := radial_balance d
  have he := ell_nonneg d
  rw [hA, hB] at hb
  linarith

lemma cofactor3_mul_eq_zero_of_det_zero {M : Mat3} (hdet : M.det = 0) :
    cofactor3 M * Mᵀ = 0 := by
  rw [cofactor3_mul_transpose, hdet]
  simp

lemma mul_cofactor3_transpose_eq_zero {M : Mat3} (hdet : M.det = 0) :
    M * (cofactor3 M)ᵀ = 0 := by
  have h := congrArg Matrix.transpose (cofactor3_mul_eq_zero_of_det_zero hdet)
  simpa [Matrix.transpose_mul] using h

lemma weighted_gram_column_zero {N : Mat3} {w : I3 → ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hzero : N * Matrix.diagonal w * Nᵀ = 0)
    (i : I3) (hi : 0 < w i) : (fun r ↦ N r i) = 0 := by
  funext r
  by_contra hentry
  have hterm : 0 < w i * (N r i) ^ 2 :=
    mul_pos hi (sq_pos_of_ne_zero hentry)
  have hrr := congrFun (congrFun hzero r) r
  fin_cases i <;> fin_cases r <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at hi hterm hrr ⊢ <;>
    nlinarith [hw 0, hw 1, hw 2,
      sq_nonneg (N 0 0), sq_nonneg (N 0 1), sq_nonneg (N 0 2),
      sq_nonneg (N 1 0), sq_nonneg (N 1 1), sq_nonneg (N 1 2),
      sq_nonneg (N 2 0), sq_nonneg (N 2 1), sq_nonneg (N 2 2),
      mul_nonneg (hw 0) (sq_nonneg (N 0 0)),
      mul_nonneg (hw 1) (sq_nonneg (N 0 1)),
      mul_nonneg (hw 2) (sq_nonneg (N 0 2)),
      mul_nonneg (hw 0) (sq_nonneg (N 1 0)),
      mul_nonneg (hw 1) (sq_nonneg (N 1 1)),
      mul_nonneg (hw 2) (sq_nonneg (N 1 2)),
      mul_nonneg (hw 0) (sq_nonneg (N 2 0)),
      mul_nonneg (hw 1) (sq_nonneg (N 2 1)),
      mul_nonneg (hw 2) (sq_nonneg (N 2 2))]

lemma cofactor3_zero_of_columns01 {N : Mat3}
    (h0 : (fun r ↦ N r 0) = 0) (h1 : (fun r ↦ N r 1) = 0) :
    cofactor3 N = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactor3, congrFun h0, congrFun h1]

lemma cofactor3_zero_of_columns02 {N : Mat3}
    (h0 : (fun r ↦ N r 0) = 0) (h2 : (fun r ↦ N r 2) = 0) :
    cofactor3 N = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactor3, congrFun h0, congrFun h2]

lemma cofactor3_zero_of_columns12 {N : Mat3}
    (h1 : (fun r ↦ N r 1) = 0) (h2 : (fun r ↦ N r 2) = 0) :
    cofactor3 N = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactor3, congrFun h1, congrFun h2]

lemma cofactor_mul_so3_ne_zero {M : Mat3} (U : SO3)
    (hC : cofactor3 M ≠ 0) : cofactor3 (M * (U : Mat3)) ≠ 0 := by
  rw [cofactor3_mul, cofactor3_eq_of_mem_SO3]
  intro h
  apply hC
  calc
    cofactor3 M = cofactor3 M * (1 : Mat3) := by simp
    _ = cofactor3 M * ((U : Mat3) * (U : Mat3)ᵀ) := by
      rw [so3_mul_transpose]
    _ = (cofactor3 M * (U : Mat3)) * (U : Mat3)ᵀ := by noncomm_ring
    _ = 0 := by rw [h]; simp

lemma ell_zero_cofactor_ne_det_zero_scalar_P (d : EulerData)
    (hC : cofactor3 d.M ≠ 0) (_hdet : d.M.det = 0)
    (hell : ell d = 0) :
    ∃ p : ℝ, 0 < p ∧ d.P = p • (1 : Mat3) := by
  have hH0trace : (d.M * lop' d.P * d.Mᵀ).trace = 0 := by
    rw [masterPositive_trace, hell]
  have hH0 : d.M * lop' d.P * d.Mᵀ = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff (masterPositive_posSemidef d)).mp hH0trace
  obtain ⟨U, p, hp, hdiagP⟩ := diagonalize_posDef_three d.P_pos
  let w : I3 → ℝ := lopDiag p
  let N : Mat3 := d.M * (U : Mat3)
  have hw : ∀ i, 0 ≤ w i := lopDiag_nonneg p
  have hdiagL : (U : Mat3)ᵀ * lop' d.P * U = Matrix.diagonal w := by
    rw [← lop'_conjugate_so3, hdiagP, lop'_diagonal]
  have hLrepr : lop' d.P =
      (U : Mat3) * Matrix.diagonal w * (U : Mat3)ᵀ := by
    symm
    rw [← hdiagL]
    calc
      (U : Mat3) * ((U : Mat3)ᵀ * lop' d.P * U) * (U : Mat3)ᵀ =
          ((U : Mat3) * (U : Mat3)ᵀ) * lop' d.P *
            ((U : Mat3) * (U : Mat3)ᵀ) := by noncomm_ring
      _ = lop' d.P := by rw [so3_mul_transpose]; simp
  have hNzero : N * Matrix.diagonal w * Nᵀ = 0 := by
    change (d.M * (U : Mat3)) * Matrix.diagonal w *
      (d.M * (U : Mat3))ᵀ = 0
    rw [Matrix.transpose_mul]
    calc
      (d.M * (U : Mat3)) * Matrix.diagonal w *
            ((U : Mat3)ᵀ * d.Mᵀ) =
          d.M * ((U : Mat3) * Matrix.diagonal w * (U : Mat3)ᵀ) *
            d.Mᵀ := by noncomm_ring
      _ = d.M * lop' d.P * d.Mᵀ := by rw [← hLrepr]
      _ = 0 := hH0
  have hcofN : cofactor3 N ≠ 0 :=
    cofactor_mul_so3_ne_zero (M := d.M) U hC
  have h01 : p 0 = p 1 := by
    by_contra hne
    have hw2 : 0 < w 2 := by
      simp [w, lopDiag]
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    have hc2 := weighted_gram_column_zero hw hNzero 2 hw2
    by_cases heq : p 1 = p 2
    · have hw1 : 0 < w 1 := by
        simp [w, lopDiag]
        apply sq_pos_of_ne_zero
        apply sub_ne_zero.mpr
        intro h20
        apply hne
        linarith
      have hc1 := weighted_gram_column_zero hw hNzero 1 hw1
      exact hcofN (cofactor3_zero_of_columns12 hc1 hc2)
    · have hw0 : 0 < w 0 := by
        simp [w, lopDiag]
        exact sq_pos_of_ne_zero (sub_ne_zero.mpr heq)
      have hc0 := weighted_gram_column_zero hw hNzero 0 hw0
      exact hcofN (cofactor3_zero_of_columns02 hc0 hc2)
  have h12 : p 1 = p 2 := by
    by_contra hne
    have hw0 : 0 < w 0 := by
      simp [w, lopDiag]
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    have hw1 : 0 < w 1 := by
      simp [w, lopDiag]
      apply sq_pos_of_ne_zero
      apply sub_ne_zero.mpr
      intro h20
      apply hne
      linarith
    have hc0 := weighted_gram_column_zero hw hNzero 0 hw0
    have hc1 := weighted_gram_column_zero hw hNzero 1 hw1
    exact hcofN (cofactor3_zero_of_columns01 hc0 hc1)
  refine ⟨p 0, hp 0, ?_⟩
  have hdiagScalar : Matrix.diagonal p = p 0 • (1 : Mat3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h12]
  have hPrepr : d.P =
      (U : Mat3) * Matrix.diagonal p * (U : Mat3)ᵀ := by
    symm
    rw [← hdiagP]
    calc
      (U : Mat3) * ((U : Mat3)ᵀ * d.P * U) * (U : Mat3)ᵀ =
          ((U : Mat3) * (U : Mat3)ᵀ) * d.P *
            ((U : Mat3) * (U : Mat3)ᵀ) := by noncomm_ring
      _ = d.P := by rw [so3_mul_transpose]; simp
  rw [hPrepr, hdiagScalar]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    so3_mul_transpose]

lemma frob_cofactorP_QM_zero_of_scalar_P_det_zero (d : EulerData)
    {p : ℝ} (hP : d.P = p • (1 : Mat3)) (hdet : d.M.det = 0) :
    radialPair d = 0 := by
  have hMC := mul_cofactor3_transpose_eq_zero hdet
  rw [radialPair, hP]
  rw [Matrix.mul_smul, Matrix.mul_one]
  rw [frob_eq_trace, Matrix.transpose_smul]
  rw [Matrix.smul_mul, Matrix.trace_smul, ← Matrix.mul_assoc,
    Matrix.trace_mul_cycle, hMC]
  simp

lemma master_unscaled (d : EulerData) :
    d.Q * (residual d.P d.Q d.M * d.Mᵀ +
        d.M * (residual d.P d.Q d.M)ᵀ) =
      d.M * lop' d.P * d.Mᵀ + alpha d • (1 : Mat3) -
        residual d.P d.Q d.M * (residual d.P d.Q d.M)ᵀ := by
  let R := residual d.P d.Q d.M
  let C := cofactor3 d.M
  change d.Q * (R * d.Mᵀ + d.M * Rᵀ) =
    d.M * lop' d.P * d.Mᵀ + alpha d • (1 : Mat3) - R * Rᵀ
  have hPt : d.Pᵀ = d.P := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using d.P_pos.isHermitian.eq
  have hM := d.gradM
  have hbase : d.Q * R = d.M * lop' d.P + dcof d.M (R * d.P) := by
    change -(d.M * lop' d.P) - dcof d.M (R * d.P) + d.Q * R = 0 at hM
    have := hM
    ext i j
    have hij := congrFun (congrFun this i) j
    simp at hij ⊢
    linarith
  have hright := congrArg (fun X : Mat3 ↦ X * d.Mᵀ) hbase
  have hdcof := dcof_mul_transpose d.M (R * d.P)
  change dcof d.M (R * d.P) * d.Mᵀ =
      frob C (R * d.P) • (1 : Mat3) - C * (R * d.P)ᵀ at hdcof
  have halpha : frob C (R * d.P) = alpha d := by
    rw [alpha]
    change frob C (R * d.P) = frob R (C * d.P)
    rw [frob_symm, frob_mul_right, hPt]
  have hCP : C * d.P = R + d.Q * d.M := by
    change C * d.P = C * d.P - d.Q * d.M + d.Q * d.M
    abel
  rw [add_mul, hdcof, halpha, Matrix.transpose_mul, hPt] at hright
  change d.Q * R * d.Mᵀ =
      d.M * lop' d.P * d.Mᵀ +
        (alpha d • (1 : Mat3) - C * (d.P * Rᵀ)) at hright
  calc
    d.Q * (R * d.Mᵀ + d.M * Rᵀ) =
        d.Q * R * d.Mᵀ + d.Q * d.M * Rᵀ := by noncomm_ring
    _ = d.M * lop' d.P * d.Mᵀ + alpha d • (1 : Mat3) -
        C * d.P * Rᵀ + d.Q * d.M * Rᵀ := by
      rw [hright]
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_succ]
      ring
    _ = d.M * lop' d.P * d.Mᵀ + alpha d • (1 : Mat3) - R * Rᵀ := by
      rw [hCP]
      noncomm_ring

lemma master_identity (d : EulerData) :
    (1 / rhoQ d) • (d.Q * kop (rhoQ d • d.Q)) =
      d.M * lop' d.P * d.Mᵀ + alpha d • (1 : Mat3) -
        residual d.P d.Q d.M * (residual d.P d.Q d.M)ᵀ := by
  rw [q_kop_identity]
  have hrho : rhoQ d ≠ 0 := ne_of_gt (rhoQ_pos d)
  rw [Matrix.mul_smul, smul_smul]
  change ((1 / rhoQ d) * rhoQ d) •
      (d.Q * (residual d.P d.Q d.M * d.Mᵀ +
        d.M * (residual d.P d.Q d.M)ᵀ)) = _
  rw [one_div_mul_cancel hrho, one_smul]
  exact master_unscaled d

lemma q_mul_kop_quad_neg (d : EulerData) (hC : cofactor3 d.M ≠ 0)
    (hell : 0 < ell d) {v : Vec3} (hv : v ≠ 0) :
    S3xS3.Trivial.quad3 (d.Q * kop (rhoQ d • d.Q)) v < 0 := by
  have halpha := radial_alpha_strict_of_cofactor_ne_zero d hC hell
  have hrhs := quad3_master_rhs_neg d halpha hv
  have heq := congrArg (fun A : Mat3 ↦ S3xS3.Trivial.quad3 A v)
    (master_identity d)
  rw [quad3_smul] at heq
  have hrho := rhoQ_pos d
  have hinv : 0 < 1 / rhoQ d := one_div_pos.mpr hrho
  nlinarith

lemma first_barrier (d : EulerData) (hC : cofactor3 d.M ≠ 0)
    (hell : 0 < ell d) :
    S3xS3.Trivial.StrictBelowFour (rhoQ d • d.Q) := by
  have hneg : (-kop (rhoQ d • d.Q)).PosDef :=
    neg_kop_posDef_of_q_mul_kop_neg d.Q_pos (rhoQ_pos d)
      (fun v hv ↦ q_mul_kop_quad_neg d hC hell hv)
  exact strictBelowFour_of_neg_kop (d.Q_pos.smul (rhoQ_pos d)) hneg

lemma quad3_transpose (A : Mat3) (v : Vec3) :
    S3xS3.Trivial.quad3 Aᵀ v = S3xS3.Trivial.quad3 A v := by
  simp [S3xS3.Trivial.quad3, Fin.sum_univ_succ]
  ring

lemma quad3_mul_eq_zero_of_right_mulVec_zero (A B : Mat3) (v : Vec3)
    (hB : B *ᵥ v = 0) : S3xS3.Trivial.quad3 (A * B) v = 0 := by
  rw [quad3_eq_dotProduct, ← Matrix.mulVec_mulVec, hB]
  simp

lemma quad3_add (A B : Mat3) (v : Vec3) :
    S3xS3.Trivial.quad3 (A + B) v =
      S3xS3.Trivial.quad3 A v + S3xS3.Trivial.quad3 B v := by
  simp [S3xS3.Trivial.quad3, Fin.sum_univ_succ]
  ring

lemma no_eulerData_singular_cofactor_ne (d : EulerData)
    (hC : cofactor3 d.M ≠ 0) (hdet : d.M.det = 0) : False := by
  have he := ell_nonneg d
  by_cases hell : ell d = 0
  · obtain ⟨p, hp, hP⟩ :=
      ell_zero_cofactor_ne_det_zero_scalar_P d hC hdet hell
    have hpair := frob_cofactorP_QM_zero_of_scalar_P_det_zero d hP hdet
    have hA : alpha d = radialXsq d := by
      rw [alpha_eq_radial, hpair]
      ring
    have hB : beta d = -radialYsq d := by
      rw [beta_eq_radial, hpair]
      ring
    have hXne : radialXsq d ≠ 0 := by
      intro hx
      exact cofactor_mul_P_ne_zero d hC ((frobNormSq_eq_zero_iff _).mp hx)
    have hXpos : 0 < radialXsq d :=
      lt_of_le_of_ne (frobNormSq_nonneg _) (Ne.symm hXne)
    have hYnon := frobNormSq_nonneg (d.Q * d.M)
    change 0 ≤ radialYsq d at hYnon
    have hb := radial_balance d
    rw [hell, hA, hB] at hb
    ring_nf at hb
    linarith
  · have hellpos : 0 < ell d := lt_of_le_of_ne he (Ne.symm hell)
    have hnegK : (-kop (rhoQ d • d.Q)).PosDef :=
      neg_kop_posDef_of_q_mul_kop_neg d.Q_pos (rhoQ_pos d)
        (fun v hv ↦ q_mul_kop_quad_neg d hC hellpos hv)
    have hMtu : ¬ IsUnit d.Mᵀ := by
      intro hu
      have hdu := (Matrix.isUnit_iff_isUnit_det d.Mᵀ).mp hu
      have hdetu : IsUnit d.M.det := by simpa using hdu
      exact (isUnit_iff_ne_zero.mp hdetu) hdet
    have hker : ∃ v : Vec3, v ≠ 0 ∧ d.Mᵀ *ᵥ v = 0 := by
      have hninj : ¬ Function.Injective d.Mᵀ.mulVec := by
        intro hinj
        exact hMtu (Matrix.mulVec_injective_iff_isUnit.mp hinj)
      obtain ⟨v, w, himage, hne⟩ := Function.not_injective_iff.mp hninj
      let z := v - w
      refine ⟨z, sub_ne_zero.mpr hne, ?_⟩
      change d.Mᵀ *ᵥ (v - w) = 0
      rw [Matrix.mulVec_sub, himage, sub_self]
    obtain ⟨v, hv, hMv⟩ := hker
    let R := residual d.P d.Q d.M
    have hfirst : S3xS3.Trivial.quad3 (R * d.Mᵀ) v = 0 :=
      quad3_mul_eq_zero_of_right_mulVec_zero R d.Mᵀ v hMv
    have hsecond : S3xS3.Trivial.quad3 (d.M * Rᵀ) v = 0 := by
      calc
        S3xS3.Trivial.quad3 (d.M * Rᵀ) v =
            S3xS3.Trivial.quad3 (R * d.Mᵀ)ᵀ v := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose]
        _ = S3xS3.Trivial.quad3 (R * d.Mᵀ) v :=
          quad3_transpose (R * d.Mᵀ) v
        _ = 0 := hfirst
    have hright : S3xS3.Trivial.quad3 (R * d.Mᵀ + d.M * Rᵀ) v = 0 := by
      rw [quad3_add, hfirst, hsecond, add_zero]
    have hKidentity := q_kop_identity d
    have heq := congrArg (fun A : Mat3 ↦ S3xS3.Trivial.quad3 A v) hKidentity
    rw [quad3_smul] at heq
    change S3xS3.Trivial.quad3 (kop (rhoQ d • d.Q)) v =
      rhoQ d * S3xS3.Trivial.quad3 (R * d.Mᵀ + d.M * Rᵀ) v at heq
    rw [hright] at heq
    have hquadZero : S3xS3.Trivial.quad3 (kop (rhoQ d • d.Q)) v = 0 := by
      linarith
    have hstrict := hnegK.dotProduct_mulVec_pos hv
    have hstrict' : S3xS3.Trivial.quad3 (-kop (rhoQ d • d.Q)) v > 0 := by
      rw [quad3_eq_dotProduct]
      simpa using hstrict
    have hnegquad : S3xS3.Trivial.quad3 (-kop (rhoQ d • d.Q)) v =
        -S3xS3.Trivial.quad3 (kop (rhoQ d • d.Q)) v := by
      simp [S3xS3.Trivial.quad3, Fin.sum_univ_succ]
      ring
    rw [hnegquad, hquadZero] at hstrict'
    linarith

lemma scalarMatrix_inv_offdiag (p : ℝ) {i j : I3} (hij : i ≠ j) :
    (p • (1 : Mat3))⁻¹ i j = 0 := by
  have heq : p • (1 : Mat3) = Matrix.diagonal (fun _ : I3 ↦ p) := by
    ext r s
    by_cases hrs : r = s
    · subst s
      simp
    · simp [Matrix.diagonal, hrs]
  rw [heq, Matrix.inv_diagonal]
  simp [Matrix.diagonal, hij]

lemma inverse_offdiag_of_scalar {P : Mat3} (_hPpos : P.PosDef)
    {p : ℝ} (hP : P = p • (1 : Mat3)) {i j : I3} (hij : i ≠ j) :
    P⁻¹ i j = 0 := by
  rw [hP]
  exact scalarMatrix_inv_offdiag p hij

lemma scalarP_diagonalM_offQ0 (d : EulerData) {p : ℝ} {m : I3 → ℝ}
    (hP : d.P = p • (1 : Mat3)) (hM : d.M = Matrix.diagonal m) :
    m 0 * (m 1 ^ 2 + m 2 ^ 2) * d.Q 1 2 = 0 := by
  have hij := congrFun (congrFun d.gradP 1) 2
  rw [hP, hM] at hij
  have hrhs : (d.kappa • (p • (1 : Mat3))⁻¹) 1 2 = 0 := by
    rw [real_smul_apply, scalarMatrix_inv_offdiag p (by decide)]
    ring
  rw [hrhs] at hij
  have hsym : d.Q 2 1 = d.Q 1 2 := by
    have hq := congrFun (congrFun d.Q_pos.isHermitian.eq 1) 2
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hq
  simp [residual, dcof, cofactor3, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ] at hij
  rw [hsym] at hij
  ring_nf at hij ⊢
  linarith

lemma scalarP_diagonalM_offQ1 (d : EulerData) {p : ℝ} {m : I3 → ℝ}
    (hP : d.P = p • (1 : Mat3)) (hM : d.M = Matrix.diagonal m) :
    m 1 * (m 0 ^ 2 + m 2 ^ 2) * d.Q 0 2 = 0 := by
  have hij := congrFun (congrFun d.gradP 0) 2
  rw [hP, hM] at hij
  have hrhs : (d.kappa • (p • (1 : Mat3))⁻¹) 0 2 = 0 := by
    rw [real_smul_apply, scalarMatrix_inv_offdiag p (by decide)]
    ring
  rw [hrhs] at hij
  have hsym : d.Q 2 0 = d.Q 0 2 := by
    have hq := congrFun (congrFun d.Q_pos.isHermitian.eq 0) 2
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hq
  simp [residual, dcof, cofactor3, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ] at hij
  rw [hsym] at hij
  ring_nf at hij ⊢
  linarith

lemma scalarP_diagonalM_offQ2 (d : EulerData) {p : ℝ} {m : I3 → ℝ}
    (hP : d.P = p • (1 : Mat3)) (hM : d.M = Matrix.diagonal m) :
    m 2 * (m 0 ^ 2 + m 1 ^ 2) * d.Q 0 1 = 0 := by
  have hij := congrFun (congrFun d.gradP 0) 1
  rw [hP, hM] at hij
  have hrhs : (d.kappa • (p • (1 : Mat3))⁻¹) 0 1 = 0 := by
    rw [real_smul_apply, scalarMatrix_inv_offdiag p (by decide)]
    ring
  rw [hrhs] at hij
  have hsym : d.Q 1 0 = d.Q 0 1 := by
    have hq := congrFun (congrFun d.Q_pos.isHermitian.eq 0) 1
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hq
  simp [residual, dcof, cofactor3, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ] at hij
  rw [hsym] at hij
  ring_nf at hij ⊢
  linarith

lemma scalarP_diagonalM_Q_diagonal (d : EulerData) {p : ℝ} {m : I3 → ℝ}
    (hP : d.P = p • (1 : Mat3)) (hM : d.M = Matrix.diagonal m)
    (hm : ∀ i, m i ≠ 0) :
    d.Q = Matrix.diagonal (fun i ↦ d.Q i i) := by
  have h0eq := scalarP_diagonalM_offQ0 d hP hM
  have h1eq := scalarP_diagonalM_offQ1 d hP hM
  have h2eq := scalarP_diagonalM_offQ2 d hP hM
  have hs0 : 0 < m 1 ^ 2 + m 2 ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (hm 1), sq_pos_of_ne_zero (hm 2)]
  have hs1 : 0 < m 0 ^ 2 + m 2 ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (hm 0), sq_pos_of_ne_zero (hm 2)]
  have hs2 : 0 < m 0 ^ 2 + m 1 ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (hm 0), sq_pos_of_ne_zero (hm 1)]
  have hy0 : d.Q 1 2 = 0 := by
    rcases mul_eq_zero.mp h0eq with hcoef | hy
    · rcases mul_eq_zero.mp hcoef with hm0 | hsum
      · exact (hm 0 hm0).elim
      · exact (ne_of_gt hs0 hsum).elim
    · exact hy
  have hy1 : d.Q 0 2 = 0 := by
    rcases mul_eq_zero.mp h1eq with hcoef | hy
    · rcases mul_eq_zero.mp hcoef with hm1 | hsum
      · exact (hm 1 hm1).elim
      · exact (ne_of_gt hs1 hsum).elim
    · exact hy
  have hy2 : d.Q 0 1 = 0 := by
    rcases mul_eq_zero.mp h2eq with hcoef | hy
    · rcases mul_eq_zero.mp hcoef with hm2 | hsum
      · exact (hm 2 hm2).elim
      · exact (ne_of_gt hs2 hsum).elim
    · exact hy
  have hQt : d.Qᵀ = d.Q := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using d.Q_pos.isHermitian.eq
  have hy0' : d.Q 2 1 = 0 := by
    have := congrFun (congrFun hQt 1) 2
    simpa [hy0] using this
  have hy1' : d.Q 2 0 = 0 := by
    have := congrFun (congrFun hQt 0) 2
    simpa [hy1] using this
  have hy2' : d.Q 1 0 = 0 := by
    have := congrFun (congrFun hQt 0) 1
    simpa [hy2] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hy0, hy1, hy2, hy0', hy1', hy2']

lemma lop'_eq_zero_scalar_P {P : Mat3} (hP : P.PosDef)
    (hL : lop' P = 0) : ∃ p : ℝ, 0 < p ∧ P = p • (1 : Mat3) := by
  obtain ⟨U, p, hp, hdiagP⟩ := diagonalize_posDef_three hP
  have hdiagL : Matrix.diagonal (lopDiag p) = 0 := by
    rw [← lop'_diagonal, ← hdiagP, lop'_conjugate_so3, hL]
    simp
  have h0 := congrFun (congrFun hdiagL 0) 0
  have h1 := congrFun (congrFun hdiagL 1) 1
  have h2 := congrFun (congrFun hdiagL 2) 2
  simp [lopDiag] at h0 h1 h2
  have h01 : p 0 = p 1 := by nlinarith
  have h12 : p 1 = p 2 := by nlinarith
  have hdiagScalar : Matrix.diagonal p = p 0 • (1 : Mat3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h12]
  have hPrepr : P = (U : Mat3) * Matrix.diagonal p * (U : Mat3)ᵀ := by
    symm
    rw [← hdiagP]
    calc
      (U : Mat3) * ((U : Mat3)ᵀ * P * U) * (U : Mat3)ᵀ =
          ((U : Mat3) * (U : Mat3)ᵀ) * P *
            ((U : Mat3) * (U : Mat3)ᵀ) := by noncomm_ring
      _ = P := by rw [so3_mul_transpose]; simp
  refine ⟨p 0, hp 0, ?_⟩
  rw [hPrepr, hdiagScalar, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, so3_mul_transpose]

lemma ell_zero_invertible_lop_zero (d : EulerData) (hdet : d.M.det ≠ 0)
    (hell : ell d = 0) : lop' d.P = 0 := by
  have htrace : (d.M * lop' d.P * d.Mᵀ).trace = 0 := by
    rw [masterPositive_trace, hell]
  have hH : d.M * lop' d.P * d.Mᵀ = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff (masterPositive_posSemidef d)).mp htrace
  have hMdet : IsUnit d.M.det := isUnit_iff_ne_zero.mpr hdet
  have hMtDet : IsUnit d.Mᵀ.det := by simpa using hMdet
  calc
    lop' d.P = (d.M⁻¹ * d.M) * lop' d.P * (d.Mᵀ * d.Mᵀ⁻¹) := by
      rw [d.M.nonsing_inv_mul hMdet, d.Mᵀ.mul_nonsing_inv hMtDet]
      simp
    _ = d.M⁻¹ * (d.M * lop' d.P * d.Mᵀ) * d.Mᵀ⁻¹ := by noncomm_ring
    _ = 0 := by rw [hH]; simp

lemma full_ell_zero_diagonal_Q (d : EulerData) {m : I3 → ℝ}
    (hM : d.M = Matrix.diagonal m) (hm : ∀ i, m i ≠ 0)
    (hell : ell d = 0) :
    ∃ p : ℝ, 0 < p ∧ d.P = p • (1 : Mat3) ∧
      d.Q = Matrix.diagonal (fun i ↦ d.Q i i) := by
  have hdet : d.M.det ≠ 0 := by
    rw [hM, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ, hm]
  obtain ⟨p, hp, hP⟩ :=
    lop'_eq_zero_scalar_P d.P_pos (ell_zero_invertible_lop_zero d hdet hell)
  exact ⟨p, hp, hP, scalarP_diagonalM_Q_diagonal d hP hM hm⟩

end S3xS3.Trivial.Euler
