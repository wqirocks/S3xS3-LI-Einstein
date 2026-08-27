import S3xS3.Trivial.FactorSwap

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.FactorSwapFormulas

open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.FactorSwap

lemma pdSqrt_det_pos {A : Mat3} (hA : A.PosDef) :
    0 < (pdSqrt A).det :=
  (pdSqrt_posDef hA).det_pos

lemma pdSqrt_det_sq {A : Mat3} (hA : A.PosDef) :
    (pdSqrt A).det ^ 2 = A.det := by
  have h := congrArg Matrix.det (pdSqrt_sq hA)
  rw [Matrix.det_mul] at h
  simpa [pow_two] using h

lemma pdSqrt_det {A : Mat3} (hA : A.PosDef) :
    (pdSqrt A).det = Real.sqrt A.det := by
  have hleft := pdSqrt_det_pos hA
  have hright := Real.sqrt_pos.2 hA.det_pos
  have hsquare := pdSqrt_det_sq hA
  have hsqrt : (Real.sqrt A.det) ^ 2 = A.det :=
    Real.sq_sqrt hA.det_pos.le
  nlinarith

lemma graphD_closed {g : LeftInvariantMetric} (d : GraphData g) :
    d.D = Real.sqrt d.P.det • (pdSqrt d.P)⁻¹ := by
  let S := pdSqrt d.P
  let c := Real.sqrt d.P.det
  have hS : S.PosDef := pdSqrt_posDef d.P_pos
  have hc : 0 < c := Real.sqrt_pos.2 d.P_pos.det_pos
  have hR : (c • S⁻¹).PosDef := hS.inv.smul hc
  apply posDef_sqrt_unique d.D_pos hR
  rw [d.D_sq]
  have hSdet : IsUnit S.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hS.det_pos)
  have hsquare : S⁻¹ * S⁻¹ = d.P⁻¹ := by
    rw [← Matrix.mul_inv_rev, show S * S = d.P by
      exact pdSqrt_sq d.P_pos]
  have hc2 : c ^ 2 = d.P.det := Real.sq_sqrt d.P_pos.det_pos.le
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsquare,
    cofactor3_eq_det_smul_inv d.P_pos]
  congr 1
  simpa [pow_two] using hc2.symm

lemma graphE_closed {g : LeftInvariantMetric} (d : GraphData g) :
    d.E = Real.sqrt d.Q.det • (pdSqrt d.Q)⁻¹ := by
  let S := pdSqrt d.Q
  let c := Real.sqrt d.Q.det
  have hS : S.PosDef := pdSqrt_posDef d.Q_pos
  have hc : 0 < c := Real.sqrt_pos.2 d.Q_pos.det_pos
  have hR : (c • S⁻¹).PosDef := hS.inv.smul hc
  apply posDef_sqrt_unique d.E_pos hR
  rw [d.E_sq]
  have hsquare : S⁻¹ * S⁻¹ = d.Q⁻¹ := by
    rw [← Matrix.mul_inv_rev, show S * S = d.Q by
      exact pdSqrt_sq d.Q_pos]
  have hc2 : c ^ 2 = d.Q.det := Real.sq_sqrt d.Q_pos.det_pos.le
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsquare,
    cofactor3_eq_det_smul_inv d.Q_pos]
  congr 1
  simpa [pow_two] using hc2.symm

noncomputable def swapDetRoot (m : I3 → ℝ) : ℝ := (rootB m).det

lemma swapDetRoot_pos (m : I3 → ℝ) : 0 < swapDetRoot m :=
  (rootB_posDef m).det_pos

lemma invBRoot_eq_inv (m : I3 → ℝ) :
    invBRoot m = (rootB m)⁻¹ := by
  have hdet : IsUnit (rootB m).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (rootB_posDef m).det_pos)
  apply (rootB_posDef m).isUnit.mul_left_cancel
  rw [rootB_mul_invBRoot, (rootB m).mul_nonsing_inv hdet]

lemma swapDetRoot_sq (m : I3 → ℝ) :
    swapDetRoot m ^ 2 = (1 + diagonalM m * diagonalM m).det := by
  have h := congrArg Matrix.det (rootB_sq m)
  rw [Matrix.det_mul] at h
  simpa [swapDetRoot, pow_two] using h

lemma invBRoot_det (m : I3 → ℝ) :
    (invBRoot m).det = (swapDetRoot m)⁻¹ := by
  rw [invBRoot_eq_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  rfl

lemma cofactor3_inj_posDef {A B : Mat3} (hA : A.PosDef)
    (hB : B.PosDef) (hcof : cofactor3 A = cofactor3 B) : A = B := by
  have hdetSq := congrArg Matrix.det hcof
  rw [det_cofactor3, det_cofactor3] at hdetSq
  have hdet : A.det = B.det := by
    nlinarith [hA.det_pos, hB.det_pos]
  have hcofA := cofactor3_eq_det_smul_inv hA
  have hcofB := cofactor3_eq_det_smul_inv hB
  rw [hcofA, hcofB, hdet] at hcof
  have hdet0 : B.det ≠ 0 := ne_of_gt hB.det_pos
  have hinv : A⁻¹ = B⁻¹ := by
    ext i j
    have hij := congrFun (congrFun hcof i) j
    simp only [real_smul_apply] at hij
    exact (mul_left_cancel₀ hdet0 hij)
  have hAdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hBdet : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet0
  calc
    A = A * 1 := by simp
    _ = A * (B⁻¹ * B) := by rw [B.nonsing_inv_mul hBdet]
    _ = (A * A⁻¹) * B := by rw [hinv]; noncomm_ring
    _ = B := by rw [A.mul_nonsing_inv hAdet]; simp

lemma sandwich_posDef {A B : Mat3} (hA : A.PosDef) (hB : B.PosDef) :
    (A * B * A).PosDef := by
  have hAt : Aᴴ = A := hA.isHermitian.eq
  have hunit : IsUnit A := hA.isUnit
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have h := hB.conjTranspose_mul_mul_same hinj
  rw [hAt] at h
  exact h

lemma rootB_sq_posDef (m : I3 → ℝ) :
    (rootB m * rootB m).PosDef := by
  have h := transpose_mul_posDef_of_det_ne_zero
    (ne_of_gt (rootB_posDef m).det_pos)
  rw [rootB_transpose m] at h
  exact h

lemma invBRoot_sq_posDef (m : I3 → ℝ) :
    (invBRoot m * invBRoot m).PosDef := by
  have h := transpose_mul_posDef_of_det_ne_zero
    (ne_of_gt (invBRoot_posDef m).det_pos)
  rw [invBRoot_transpose m] at h
  exact h

lemma cofactor3_pdSqrt {A : Mat3} (hA : A.PosDef) :
    cofactor3 (pdSqrt A) =
      Real.sqrt A.det • (pdSqrt A)⁻¹ := by
  rw [cofactor3_eq_det_smul_inv (pdSqrt_posDef hA), pdSqrt_det hA]

lemma cofactor3_rootB (m : I3 → ℝ) :
    cofactor3 (rootB m) = swapDetRoot m • invBRoot m := by
  rw [cofactor3_eq_det_smul_inv (rootB_posDef m), invBRoot_eq_inv]
  rfl

lemma cofactor3_invBRoot (m : I3 → ℝ) :
    cofactor3 (invBRoot m) = (swapDetRoot m)⁻¹ • rootB m := by
  rw [cofactor3_eq_det_smul_inv (invBRoot_posDef m), invBRoot_det]
  have hdet : IsUnit (rootB m).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (rootB_posDef m).det_pos)
  have hinvInv : (invBRoot m)⁻¹ = rootB m := by
    rw [invBRoot_eq_inv]
    letI : Invertible (rootB m) :=
      Matrix.invertibleOfIsUnitDet (rootB m) hdet
    exact Matrix.inv_inv_of_invertible (rootB m)
  rw [hinvInv]

lemma Hone_cofactor_target (m : I3 → ℝ) {g : LeftInvariantMetric}
    (d : GraphData g) :
    Hone m d.E * Hone m d.E =
      d.E * invBRoot m * invBRoot m * d.E := by
  have hEt : d.Eᵀ = d.E := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      d.E_pos.isHermitian.eq
  rw [Hone_sq m d.E d.E_pos, Dzero, Matrix.transpose_mul,
    hEt, invBRoot_transpose]
  noncomm_ring

lemma Htwo_cofactor_target (m : I3 → ℝ) {g : LeftInvariantMetric}
    (d : GraphData g) :
    Htwo m d.D * Htwo m d.D =
      d.D * rootB m * rootB m * d.D := by
  have hDt : d.Dᵀ = d.D := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      d.D_pos.isHermitian.eq
  rw [Htwo_sq m d.D d.D_pos, Ezero, Matrix.transpose_mul,
    hDt, rootB_transpose]
  noncomm_ring

noncomputable def swappedPClosed {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) : Mat3 :=
  (swapDetRoot m)⁻¹ •
    (pdSqrt d.Q * (rootB m * rootB m) * pdSqrt d.Q)

noncomputable def swappedQClosed {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) : Mat3 :=
  swapDetRoot m •
    (pdSqrt d.P * (invBRoot m * invBRoot m) * pdSqrt d.P)

lemma swappedPClosed_posDef {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) :
    (swappedPClosed d m).PosDef := by
  apply (sandwich_posDef (pdSqrt_posDef d.Q_pos) (rootB_sq_posDef m)).smul
  exact inv_pos.mpr (swapDetRoot_pos m)

lemma swappedQClosed_posDef {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) :
    (swappedQClosed d m).PosDef := by
  apply (sandwich_posDef (pdSqrt_posDef d.P_pos) (invBRoot_sq_posDef m)).smul
  exact swapDetRoot_pos m

lemma cofactor3_swappedPClosed {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) :
    cofactor3 (swappedPClosed d m) =
      d.E * invBRoot m * invBRoot m * d.E := by
  have hdelta : swapDetRoot m ≠ 0 := ne_of_gt (swapDetRoot_pos m)
  rw [swappedPClosed, cofactor3_smul, cofactor3_mul,
    cofactor3_mul, cofactor3_mul, cofactor3_pdSqrt d.Q_pos,
    graphE_closed d, cofactor3_rootB]
  simp only [Matrix.mul_assoc]
  ext i j
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    real_smul_apply]
  field_simp [hdelta]

lemma cofactor3_swappedQClosed {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) :
    cofactor3 (swappedQClosed d m) =
      d.D * rootB m * rootB m * d.D := by
  have hdelta : swapDetRoot m ≠ 0 := ne_of_gt (swapDetRoot_pos m)
  rw [swappedQClosed, cofactor3_smul, cofactor3_mul,
    cofactor3_mul, cofactor3_mul, cofactor3_pdSqrt d.P_pos,
    graphD_closed d, cofactor3_invBRoot]
  simp only [Matrix.mul_assoc]
  ext i j
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    real_smul_apply]
  field_simp [hdelta]

theorem swappedP_closed {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) :
    swappedP m d.E d.E_pos = swappedPClosed d m := by
  apply cofactor3_inj_posDef
    (invCof_posDef (HoneSq_posDef m d.E d.E_pos))
    (swappedPClosed_posDef d m)
  rw [cofactor3_invCof (HoneSq_posDef m d.E d.E_pos),
    cofactor3_swappedPClosed, Hone_cofactor_target]

theorem swappedQ_closed {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) :
    swappedQ m d.D d.D_pos = swappedQClosed d m := by
  apply cofactor3_inj_posDef
    (invCof_posDef (HtwoSq_posDef m d.D d.D_pos))
    (swappedQClosed_posDef d m)
  rw [cofactor3_invCof (HtwoSq_posDef m d.D d.D_pos),
    cofactor3_swappedQClosed, Htwo_cofactor_target]

@[simp] lemma swapGraphData_P {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = diagonalM m) :
    (swapGraphData d m hM).P = swappedP m d.E d.E_pos := rfl

@[simp] lemma swapGraphData_Q {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = diagonalM m) :
    (swapGraphData d m hM).Q = swappedQ m d.D d.D_pos := rfl

@[simp] lemma swapGraphData_M {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = diagonalM m) :
    (swapGraphData d m hM).M =
      swappedM m d.D d.E d.D_pos d.E_pos := rfl

theorem swapGraphData_P_closed {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = diagonalM m) :
    (swapGraphData d m hM).P = swappedPClosed d m := by
  rw [swapGraphData_P, swappedP_closed]

theorem swapGraphData_Q_closed {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = diagonalM m) :
    (swapGraphData d m hM).Q = swappedQClosed d m := by
  rw [swapGraphData_Q, swappedQ_closed]

lemma det_swappedPClosed {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) :
    (swappedPClosed d m).det =
      (swapDetRoot m)⁻¹ * d.Q.det := by
  have hdelta : swapDetRoot m ≠ 0 := ne_of_gt (swapDetRoot_pos m)
  rw [swappedPClosed, Matrix.det_smul, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_mul, pdSqrt_det d.Q_pos]
  simp only [Fintype.card_fin]
  have hq : (Real.sqrt d.Q.det) ^ 2 = d.Q.det :=
    Real.sq_sqrt d.Q_pos.det_pos.le
  rw [show (rootB m).det = swapDetRoot m by rfl]
  field_simp [hdelta]
  nlinarith

lemma det_swappedQClosed {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) :
    (swappedQClosed d m).det =
      swapDetRoot m * d.P.det := by
  have hdelta : swapDetRoot m ≠ 0 := ne_of_gt (swapDetRoot_pos m)
  rw [swappedQClosed, Matrix.det_smul, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_mul, pdSqrt_det d.P_pos,
    invBRoot_det]
  simp only [Fintype.card_fin]
  have hp : (Real.sqrt d.P.det) ^ 2 = d.P.det :=
    Real.sq_sqrt d.P_pos.det_pos.le
  field_simp [hdelta]
  nlinarith

theorem swapGraphData_det_P {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = diagonalM m) :
    (swapGraphData d m hM).P.det =
      (swapDetRoot m)⁻¹ * d.Q.det := by
  rw [swapGraphData_P_closed, det_swappedPClosed]

theorem swapGraphData_det_Q {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = diagonalM m) :
    (swapGraphData d m hM).Q.det =
      swapDetRoot m * d.P.det := by
  rw [swapGraphData_Q_closed, det_swappedQClosed]

lemma swappedM_det (m : I3 → ℝ) (D E : Mat3)
    (hD : D.PosDef) (hE : E.PosDef) :
    (swappedM m D E hD hE).det = (diagonalM m).det := by
  rw [swappedM, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  have hR1 := (Matrix.mem_specialOrthogonalGroup_iff.mp
    (Rone m E hE).property).2
  have hR2 := (Matrix.mem_specialOrthogonalGroup_iff.mp
    (Rtwo m D hD).property).2
  rw [hR1, hR2]
  ring

lemma swapGraphData_M_det_ne_zero {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) (hM : d.M = diagonalM m)
    (hm : ∀ i, m i ≠ 0) :
    (swapGraphData d m hM).M.det ≠ 0 := by
  rw [swapGraphData_M, swappedM_det]
  exact S3xS3.Trivial.Preparation.diagonal_det_ne_zero hm

end S3xS3.Trivial.FactorSwapFormulas
