import S3xS3.Trivial.Normalize

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.FullRank

open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge
open S3xS3.Trivial.Normalize
open S3xS3.Trivial.Support

def diagOf (A : Mat3) : I3 → ℝ := fun i ↦ A i i

def edgeOf (A : Mat3) : I3 → ℝ := ![A 1 2, A 0 2, A 0 1]

lemma symm3_diagOf_edgeOf {A : Mat3} (hA : A.IsHermitian) :
    symm3 (diagOf A) (edgeOf A) = A := by
  have h01 : A 1 0 = A 0 1 := by
    have h := congrFun (congrFun hA.eq 0) 1
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have h02 : A 2 0 = A 0 2 := by
    have h := congrFun (congrFun hA.eq 0) 2
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have h12 : A 2 1 = A 1 2 := by
    have h := congrFun (congrFun hA.eq 1) 2
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symm3, diagOf, edgeOf, h01, h02, h12]

lemma normalized_gradP_rhs (d : EulerData) (hnorm : rhoP d = 1)
    (i j : I3) :
    (d.kappa • d.P⁻¹) i j = (1 / 2 : ℝ) * cofactor3 d.P i j := by
  have hdet0 : d.P.det ≠ 0 := ne_of_gt d.P_pos.det_pos
  have hk : 2 * d.kappa = d.P.det := by
    rw [rhoP] at hnorm
    exact (div_eq_one_iff_eq hdet0).mp hnorm
  have hcof := congrFun (congrFun (cofactor3_eq_det_smul_inv d.P_pos) i) j
  simp only [real_smul_apply] at hcof ⊢
  rw [hcof, ← hk]
  ring

lemma gradQ_rhs_cofactor (d : EulerData) (i j : I3) :
    (d.kappa • d.Q⁻¹) i j =
      (rhoQ d / 2) * cofactor3 d.Q i j := by
  have hdet0 : d.Q.det ≠ 0 := ne_of_gt d.Q_pos.det_pos
  have hcof := congrFun (congrFun (cofactor3_eq_det_smul_inv d.Q_pos) i) j
  simp only [real_smul_apply] at hcof ⊢
  rw [hcof, rhoQ]
  field_simp [hdet0]

lemma offP_equation (d : EulerData) (m : I3 → ℝ)
    (hM : d.M = Matrix.diagonal m) (hnorm : rhoP d = 1) (i : I3) :
    -bCoeff m i * deltaCoeff m i * edgeOf d.P i +
        m i * sCoeff m i * edgeOf d.Q i =
      edgeCof (symm3 (diagOf d.P) (edgeOf d.P)) i := by
  have hPt : d.Pᵀ = d.P := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      d.P_pos.isHermitian.eq
  have hQt : d.Qᵀ = d.Q := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      d.Q_pos.isHermitian.eq
  have hP10 : d.P 1 0 = d.P 0 1 := by
    have h := congrFun (congrFun hPt 0) 1
    simpa using h
  have hP20 : d.P 2 0 = d.P 0 2 := by
    have h := congrFun (congrFun hPt 0) 2
    simpa using h
  have hP21 : d.P 2 1 = d.P 1 2 := by
    have h := congrFun (congrFun hPt 1) 2
    simpa using h
  have hQ10 : d.Q 1 0 = d.Q 0 1 := by
    have h := congrFun (congrFun hQt 0) 1
    simpa using h
  have hQ20 : d.Q 2 0 = d.Q 0 2 := by
    have h := congrFun (congrFun hQt 0) 2
    simpa using h
  have hQ21 : d.Q 2 1 = d.Q 1 2 := by
    have h := congrFun (congrFun hQt 1) 2
    simpa using h
  fin_cases i
  · have h := congrFun (congrFun d.gradP 1) 2
    rw [normalized_gradP_rhs d hnorm 1 2] at h
    rw [hM] at h
    simp [Euler.residual, dcof, cofactor3, Matrix.trace,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      bCoeff, aCoeff, sCoeff, cofEdge0, cofEdge1, cofEdge2,
      deltaCoeff, edgeOf, edgeCof, symm3, diagOf, jIndex, kIndex,
      hP10, hP20, hP21, hQ21] at h ⊢
    nlinarith
  · have h := congrFun (congrFun d.gradP 0) 2
    rw [normalized_gradP_rhs d hnorm 0 2] at h
    rw [hM] at h
    simp [Euler.residual, dcof, cofactor3, Matrix.trace,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      bCoeff, aCoeff, sCoeff, cofEdge0, cofEdge1, cofEdge2,
      deltaCoeff, edgeOf, edgeCof, symm3, diagOf, jIndex, kIndex,
      hP10, hP20, hP21, hQ10, hQ20] at h ⊢
    nlinarith
  · have h := congrFun (congrFun d.gradP 0) 1
    rw [normalized_gradP_rhs d hnorm 0 1] at h
    rw [hM] at h
    simp [Euler.residual, dcof, cofactor3, Matrix.trace,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      bCoeff, aCoeff, sCoeff, cofEdge0, cofEdge1, cofEdge2,
      deltaCoeff, edgeOf, edgeCof, symm3, diagOf, jIndex, kIndex,
      hP10, hP20, hP21, hQ10] at h ⊢
    nlinarith

lemma offQ_equation (d : EulerData) (m : I3 → ℝ)
    (hM : d.M = Matrix.diagonal m) (i : I3) :
    m i * sCoeff m i * edgeOf d.P i -
        deltaCoeff m i * edgeOf d.Q i =
      rhoQ d * edgeCof (symm3 (diagOf d.Q) (edgeOf d.Q)) i := by
  have hPt : d.Pᵀ = d.P := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      d.P_pos.isHermitian.eq
  have hQt : d.Qᵀ = d.Q := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      d.Q_pos.isHermitian.eq
  have hP10 : d.P 1 0 = d.P 0 1 := by
    have h := congrFun (congrFun hPt 0) 1
    simpa using h
  have hP20 : d.P 2 0 = d.P 0 2 := by
    have h := congrFun (congrFun hPt 0) 2
    simpa using h
  have hP21 : d.P 2 1 = d.P 1 2 := by
    have h := congrFun (congrFun hPt 1) 2
    simpa using h
  have hQ10 : d.Q 1 0 = d.Q 0 1 := by
    have h := congrFun (congrFun hQt 0) 1
    simpa using h
  have hQ20 : d.Q 2 0 = d.Q 0 2 := by
    have h := congrFun (congrFun hQt 0) 2
    simpa using h
  have hQ21 : d.Q 2 1 = d.Q 1 2 := by
    have h := congrFun (congrFun hQt 1) 2
    simpa using h
  fin_cases i
  · have h := congrFun (congrFun d.gradQ 1) 2
    rw [gradQ_rhs_cofactor d 1 2] at h
    rw [hM] at h
    simp [Euler.residual, cofactor3, Matrix.trace,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      sCoeff, aCoeff, cofEdge0, cofEdge1, cofEdge2,
      deltaCoeff, edgeOf, edgeCof, symm3, diagOf, jIndex, kIndex,
      hP10, hP20, hP21, hQ10, hQ20, hQ21] at h ⊢
    nlinarith
  · have h := congrFun (congrFun d.gradQ 0) 2
    rw [gradQ_rhs_cofactor d 0 2] at h
    rw [hM] at h
    simp [Euler.residual, cofactor3, Matrix.trace,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      sCoeff, aCoeff, cofEdge0, cofEdge1, cofEdge2,
      deltaCoeff, edgeOf, edgeCof, symm3, diagOf, jIndex, kIndex,
      hP20, hP21, hQ10, hQ20, hQ21] at h ⊢
    nlinarith
  · have h := congrFun (congrFun d.gradQ 0) 1
    rw [gradQ_rhs_cofactor d 0 1] at h
    rw [hM] at h
    simp [Euler.residual, cofactor3, Matrix.trace,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      sCoeff, aCoeff, cofEdge0, cofEdge1, cofEdge2,
      deltaCoeff, edgeOf, edgeCof, symm3, diagOf, jIndex, kIndex,
      hP10, hQ10, hQ20, hQ21] at h ⊢
    nlinarith

lemma quad3_basis3 (A : Mat3) (i : I3) :
    S3xS3.Trivial.quad3 A (basis3 i) = A i i := by
  fin_cases i <;>
    simp [S3xS3.Trivial.quad3, basis3]

lemma normSq3_basis3 (i : I3) :
    S3xS3.Trivial.normSq3 (basis3 i) = 1 := by
  fin_cases i <;>
    simp [S3xS3.Trivial.normSq3, basis3]

lemma strictBelowFour_diagonal_entry {A : Mat3}
    (hA : S3xS3.Trivial.StrictBelowFour A) (i : I3) : A i i < 4 := by
  have h := hA (basis3 i) (basis3_ne_zero i)
  rw [quad3_basis3, normSq3_basis3] at h
  norm_num at h ⊢
  exact h

lemma edgeResidual_smul (A : Mat3) {c : ℝ} (hc : c ≠ 0) (i : I3) :
    edgeResidual (c • A) i = c * edgeResidual A i := by
  fin_cases i <;>
    simp [edgeResidual, residual0, residual1, residual2,
      off0, off1, off2]
  all_goals field_simp [hc]

lemma firstBarrier_diag (d : EulerData)
    (hfirst : S3xS3.Trivial.StrictBelowFour (rhoQ d • d.Q))
    (i : I3) : rhoQ d * diagOf d.Q i < 4 := by
  have h := strictBelowFour_diagonal_entry hfirst i
  simpa [diagOf] using h

lemma firstBarrier_residual (d : EulerData)
    (hfirst : S3xS3.Trivial.StrictBelowFour (rhoQ d • d.Q))
    (hy : AllNonzero (edgeOf d.Q)) :
    TwoOfThree (fun i ↦ rhoQ d *
      edgeResidual (symm3 (diagOf d.Q) (edgeOf d.Q)) i < 4) := by
  have hrho : rhoQ d ≠ 0 := ne_of_gt (rhoQ_pos d)
  have hQrepr := symm3_diagOf_edgeOf d.Q_pos.isHermitian
  have hsym : (rhoQ d • d.Q).IsHermitian :=
    (d.Q_pos.smul (rhoQ_pos d)).isHermitian
  have h0 : off0 (rhoQ d • d.Q) ≠ 0 := by
    simpa [off0, edgeOf] using mul_ne_zero hrho (hy 0)
  have h1 : off1 (rhoQ d • d.Q) ≠ 0 := by
    simpa [off1, edgeOf] using mul_ne_zero hrho (hy 1)
  have h2 : off2 (rhoQ d • d.Q) ≠ 0 := by
    simpa [off2, edgeOf] using mul_ne_zero hrho (hy 2)
  have htwo := S3xS3.Trivial.two_residuals_lt_four hsym hfirst h0 h1 h2
  have hres : ∀ i, edgeResidual (rhoQ d • d.Q) i =
      rhoQ d * edgeResidual (symm3 (diagOf d.Q) (edgeOf d.Q)) i := by
    intro i
    rw [edgeResidual_smul d.Q hrho i, hQrepr]
  change (edgeResidual (rhoQ d • d.Q) 0 < 4 ∧
      edgeResidual (rhoQ d • d.Q) 1 < 4) ∨
    (edgeResidual (rhoQ d • d.Q) 0 < 4 ∧
      edgeResidual (rhoQ d • d.Q) 2 < 4) ∨
    (edgeResidual (rhoQ d • d.Q) 1 < 4 ∧
      edgeResidual (rhoQ d • d.Q) 2 < 4) at htwo
  rw [hres 0, hres 1, hres 2] at htwo
  simpa [TwoOfThree] using htwo

noncomputable def bRoot (m : I3 → ℝ) (i : I3) : ℝ :=
  Real.sqrt (bCoeff m i)

noncomputable def invBRoot (m : I3 → ℝ) : Mat3 :=
  Matrix.diagonal (fun i ↦ (bRoot m i)⁻¹)

noncomputable def secondMatrix (m : I3 → ℝ) (P : Mat3) : Mat3 :=
  invBRoot m * P * invBRoot m

lemma bCoeff_pos_of_m_ne (m : I3 → ℝ) (i : I3) :
    0 < bCoeff m i := by
  simp [bCoeff, aCoeff]
  nlinarith [sq_nonneg (m i)]

lemma bRoot_pos (m : I3 → ℝ) (i : I3) : 0 < bRoot m i := by
  exact Real.sqrt_pos.2 (bCoeff_pos_of_m_ne m i)

lemma bRoot_sq (m : I3 → ℝ) (i : I3) :
    bRoot m i ^ 2 = bCoeff m i := by
  exact Real.sq_sqrt (bCoeff_pos_of_m_ne m i).le

lemma secondMatrix_apply (m : I3 → ℝ) (P : Mat3) (i j : I3) :
    secondMatrix m P i j = (bRoot m i)⁻¹ * P i j * (bRoot m j)⁻¹ := by
  fin_cases i <;> fin_cases j <;>
    simp [secondMatrix, invBRoot, Matrix.mul_apply, Fin.sum_univ_succ]

lemma secondMatrix_diag (m : I3 → ℝ) (P : Mat3) (i : I3) :
    secondMatrix m P i i = P i i / bCoeff m i := by
  rw [secondMatrix_apply]
  have hr := bRoot_sq m i
  have hr0 : bRoot m i ≠ 0 := ne_of_gt (bRoot_pos m i)
  rw [← hr]
  field_simp [hr0]

lemma secondMatrix_edge_ne (m : I3 → ℝ) (P : Mat3) (i : I3)
    (h : edgeOf P i ≠ 0) : edgeOf (secondMatrix m P) i ≠ 0 := by
  fin_cases i
  · change P 1 2 ≠ 0 at h
    change secondMatrix m P 1 2 ≠ 0
    rw [secondMatrix_apply]
    exact mul_ne_zero (mul_ne_zero
      (inv_ne_zero (ne_of_gt (bRoot_pos m 1))) h)
      (inv_ne_zero (ne_of_gt (bRoot_pos m 2)))
  · change P 0 2 ≠ 0 at h
    change secondMatrix m P 0 2 ≠ 0
    rw [secondMatrix_apply]
    exact mul_ne_zero (mul_ne_zero
      (inv_ne_zero (ne_of_gt (bRoot_pos m 0))) h)
      (inv_ne_zero (ne_of_gt (bRoot_pos m 2)))
  · change P 0 1 ≠ 0 at h
    change secondMatrix m P 0 1 ≠ 0
    rw [secondMatrix_apply]
    exact mul_ne_zero (mul_ne_zero
      (inv_ne_zero (ne_of_gt (bRoot_pos m 0))) h)
      (inv_ne_zero (ne_of_gt (bRoot_pos m 1)))

lemma secondMatrix_residual (m : I3 → ℝ) (P : Mat3) (i : I3) :
    edgeResidual (secondMatrix m P) i =
      edgeResidual P i / bCoeff m i := by
  have hr0 : bRoot m 0 ≠ 0 := ne_of_gt (bRoot_pos m 0)
  have hr1 : bRoot m 1 ≠ 0 := ne_of_gt (bRoot_pos m 1)
  have hr2 : bRoot m 2 ≠ 0 := ne_of_gt (bRoot_pos m 2)
  have hb0 : bCoeff m 0 ≠ 0 := ne_of_gt (bCoeff_pos_of_m_ne m 0)
  have hb1 : bCoeff m 1 ≠ 0 := ne_of_gt (bCoeff_pos_of_m_ne m 1)
  have hb2 : bCoeff m 2 ≠ 0 := ne_of_gt (bCoeff_pos_of_m_ne m 2)
  have hs0 := bRoot_sq m 0
  have hs1 := bRoot_sq m 1
  have hs2 := bRoot_sq m 2
  fin_cases i
  · simp [edgeResidual, residual0, off0, off1, off2,
      secondMatrix_apply]
    rw [← hs0]
    field_simp [hr0, hr1, hr2]
  · simp [edgeResidual, residual1, off0, off1, off2,
      secondMatrix_apply]
    rw [← hs1]
    field_simp [hr0, hr1, hr2]
  · simp [edgeResidual, residual2, off0, off1, off2,
      secondMatrix_apply]
    rw [← hs2]
    field_simp [hr0, hr1, hr2]

lemma secondMatrix_isHermitian {P : Mat3} (hP : P.IsHermitian)
    (m : I3 → ℝ) : (secondMatrix m P).IsHermitian := by
  have hPt : Pᵀ = P := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.eq
  have hBt : (invBRoot m)ᵀ = invBRoot m := by
    simp [invBRoot]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
    secondMatrix, Matrix.transpose_mul, Matrix.transpose_mul, hPt, hBt]
  noncomm_ring

lemma secondBarrier_diag (d : EulerData) (m : I3 → ℝ)
    (hsecond : S3xS3.Trivial.StrictBelowFour (secondMatrix m d.P))
    (i : I3) : diagOf d.P i / bCoeff m i < 4 := by
  have h := strictBelowFour_diagonal_entry hsecond i
  rw [secondMatrix_diag] at h
  simpa [diagOf] using h

lemma secondBarrier_residual (d : EulerData) (m : I3 → ℝ)
    (hsecond : S3xS3.Trivial.StrictBelowFour (secondMatrix m d.P))
    (hx : AllNonzero (edgeOf d.P)) :
    TwoOfThree (fun i ↦
      edgeResidual (symm3 (diagOf d.P) (edgeOf d.P)) i /
        bCoeff m i < 4) := by
  have hPrepr := symm3_diagOf_edgeOf d.P_pos.isHermitian
  have hsym := secondMatrix_isHermitian d.P_pos.isHermitian m
  have h0 : off0 (secondMatrix m d.P) ≠ 0 := by
    simpa [off0, edgeOf] using secondMatrix_edge_ne m d.P 0 (hx 0)
  have h1 : off1 (secondMatrix m d.P) ≠ 0 := by
    simpa [off1, edgeOf] using secondMatrix_edge_ne m d.P 1 (hx 1)
  have h2 : off2 (secondMatrix m d.P) ≠ 0 := by
    simpa [off2, edgeOf] using secondMatrix_edge_ne m d.P 2 (hx 2)
  have htwo := S3xS3.Trivial.two_residuals_lt_four hsym hsecond h0 h1 h2
  have hres : ∀ i, edgeResidual (secondMatrix m d.P) i =
      edgeResidual (symm3 (diagOf d.P) (edgeOf d.P)) i /
        bCoeff m i := by
    intro i
    rw [secondMatrix_residual, hPrepr]
  change (edgeResidual (secondMatrix m d.P) 0 < 4 ∧
      edgeResidual (secondMatrix m d.P) 1 < 4) ∨
    (edgeResidual (secondMatrix m d.P) 0 < 4 ∧
      edgeResidual (secondMatrix m d.P) 2 < 4) ∨
    (edgeResidual (secondMatrix m d.P) 1 < 4 ∧
      edgeResidual (secondMatrix m d.P) 2 < 4) at htwo
  rw [hres 0, hres 1, hres 2] at htwo
  simpa [TwoOfThree] using htwo

noncomputable def criticalDataOfEuler (d : EulerData) (m : I3 → ℝ)
    (hm : ∀ i, m i ≠ 0) (hM : d.M = Matrix.diagonal m)
    (hnorm : rhoP d = 1)
    (hfirst : S3xS3.Trivial.StrictBelowFour (rhoQ d • d.Q))
    (hsecond : S3xS3.Trivial.StrictBelowFour (secondMatrix m d.P))
    (haxis : ∀ i,
      ¬(edgeOf d.P (jIndex i) = 0 ∧ edgeOf d.P (kIndex i) = 0 ∧
        edgeOf d.Q (jIndex i) = 0 ∧ edgeOf d.Q (kIndex i) = 0)) :
    CriticalData where
  m := m
  p := diagOf d.P
  q := diagOf d.Q
  x := edgeOf d.P
  y := edgeOf d.Q
  sigma := rhoQ d
  m_ne_zero := hm
  sigma_pos := rhoQ_pos d
  offP := offP_equation d m hM hnorm
  offQ := offQ_equation d m hM
  noCommonAxis := haxis
  firstDiag := firstBarrier_diag d hfirst
  secondDiag := secondBarrier_diag d m hsecond
  firstResidual := firstBarrier_residual d hfirst
  secondResidual := secondBarrier_residual d m hsecond

theorem no_fullRank_normalized_diagonal_euler
    (d : EulerData) (m : I3 → ℝ)
    (hm : ∀ i, m i ≠ 0) (hM : d.M = Matrix.diagonal m)
    (hnorm : rhoP d = 1)
    (hfirst : S3xS3.Trivial.StrictBelowFour (rhoQ d • d.Q))
    (hsecond : S3xS3.Trivial.StrictBelowFour (secondMatrix m d.P))
    (haxis : ∀ i,
      ¬(edgeOf d.P (jIndex i) = 0 ∧ edgeOf d.P (kIndex i) = 0 ∧
        edgeOf d.Q (jIndex i) = 0 ∧ edgeOf d.Q (kIndex i) = 0)) : False := by
  exact criticalData_false
    (criticalDataOfEuler d m hm hM hnorm hfirst hsecond haxis)

end S3xS3.Trivial.FullRank
