import S3xS3.Trivial.SwapNaturality

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.FactorSwap

open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.SwapNaturality
open S3xS3.Trivial.Support

lemma transpose_mul_posDef_of_det_ne_zero {A : Mat3} (hdet : A.det ≠ 0) :
    (Aᵀ * A).PosDef := by
  have hunit : IsUnit A :=
    (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self A hinj

noncomputable def polarH (A : Mat3) : Mat3 := pdSqrt (Aᵀ * A)

lemma polarH_posDef (A : Mat3) (hdet : A.det ≠ 0) :
    (polarH A).PosDef :=
  pdSqrt_posDef (transpose_mul_posDef_of_det_ne_zero hdet)

lemma polarH_sq (A : Mat3) (hdet : A.det ≠ 0) :
    polarH A * polarH A = Aᵀ * A :=
  pdSqrt_sq (transpose_mul_posDef_of_det_ne_zero hdet)

lemma polarH_transpose (A : Mat3) (hdet : A.det ≠ 0) :
    (polarH A)ᵀ = polarH A :=
  pdSqrt_transpose (transpose_mul_posDef_of_det_ne_zero hdet)

noncomputable def polarRmat (A : Mat3) : Mat3 :=
  (polarH A)⁻¹ * Aᵀ

lemma polarRmat_mul_transpose (A : Mat3) (hdet : A.det ≠ 0) :
    polarRmat A * (polarRmat A)ᵀ = 1 := by
  let H := polarH A
  have hH : H.PosDef := polarH_posDef A hdet
  have hHsq : H * H = Aᵀ * A := polarH_sq A hdet
  have hHt : Hᵀ = H := polarH_transpose A hdet
  have hHdet : IsUnit H.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos)
  change (H⁻¹ * Aᵀ) * (H⁻¹ * Aᵀ)ᵀ = 1
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hHt,
    Matrix.transpose_transpose]
  calc
    H⁻¹ * Aᵀ * (A * H⁻¹) = H⁻¹ * (Aᵀ * A) * H⁻¹ := by
      noncomm_ring
    _ = H⁻¹ * (H * H) * H⁻¹ := by rw [hHsq]
    _ = 1 := by
      rw [← Matrix.mul_assoc, H.nonsing_inv_mul hHdet]
      simp [H.mul_nonsing_inv hHdet]

lemma polarRmat_det_pos (A : Mat3) (hdet : 0 < A.det) :
    0 < (polarRmat A).det := by
  have hA0 : A.det ≠ 0 := ne_of_gt hdet
  have hH := polarH_posDef A hA0
  rw [polarRmat, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact mul_pos (inv_pos.mpr hH.det_pos) hdet

noncomputable def polarRotation (A : Mat3) (hdet : 0 < A.det) : SO3 := by
  let R := polarRmat A
  have hRRt : R * Rᵀ = 1 := polarRmat_mul_transpose A (ne_of_gt hdet)
  have hRdetpos : 0 < R.det := polarRmat_det_pos A hdet
  have hdetSq : R.det ^ 2 = 1 := by
    have h := congrArg Matrix.det hRRt
    rw [Matrix.det_mul, Matrix.det_transpose] at h
    simpa [pow_two] using h
  have hRdet : R.det = 1 := by nlinarith
  exact ⟨R, (Matrix.mem_specialOrthogonalGroup_iff).2
    ⟨(Matrix.mem_orthogonalGroup_iff I3 ℝ).2 hRRt, hRdet⟩⟩

lemma polarRotation_coe (A : Mat3) (hdet : 0 < A.det) :
    (polarRotation A hdet : Mat3) = polarRmat A := rfl

lemma polarRotation_mul (A : Mat3) (hdet : 0 < A.det) :
    (polarRotation A hdet : Mat3) * A = polarH A := by
  let H := polarH A
  have hH : H.PosDef := polarH_posDef A (ne_of_gt hdet)
  have hHsq : H * H = Aᵀ * A := polarH_sq A (ne_of_gt hdet)
  have hHdet : IsUnit H.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos)
  change H⁻¹ * Aᵀ * A = H
  calc
    H⁻¹ * Aᵀ * A = H⁻¹ * (Aᵀ * A) := by noncomm_ring
    _ = H⁻¹ * (H * H) := by rw [hHsq]
    _ = H := by
      rw [← Matrix.mul_assoc, H.nonsing_inv_mul hHdet]
      simp

noncomputable def rootB (m : I3 → ℝ) : Mat3 :=
  Matrix.diagonal (bRoot m)

def diagonalM (m : I3 → ℝ) : Mat3 := Matrix.diagonal m

lemma rootB_posDef (m : I3 → ℝ) : (rootB m).PosDef := by
  rw [rootB, Matrix.posDef_diagonal_iff]
  exact bRoot_pos m

lemma rootB_transpose (m : I3 → ℝ) : (rootB m)ᵀ = rootB m := by
  simp [rootB]

lemma invBRoot_transpose (m : I3 → ℝ) : (invBRoot m)ᵀ = invBRoot m := by
  simp [invBRoot]

lemma diagonalM_transpose (m : I3 → ℝ) : (diagonalM m)ᵀ = diagonalM m := by
  simp [diagonalM]

lemma invBRoot_mul_rootB (m : I3 → ℝ) :
    invBRoot m * rootB m = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invBRoot, rootB, Matrix.mul_apply, Fin.sum_univ_succ,
      ne_of_gt (bRoot_pos m 0), ne_of_gt (bRoot_pos m 1),
      ne_of_gt (bRoot_pos m 2)]

lemma rootB_mul_invBRoot (m : I3 → ℝ) :
    rootB m * invBRoot m = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invBRoot, rootB, Matrix.mul_apply, Fin.sum_univ_succ,
      ne_of_gt (bRoot_pos m 0), ne_of_gt (bRoot_pos m 1),
      ne_of_gt (bRoot_pos m 2)]

lemma rootB_sq (m : I3 → ℝ) :
    rootB m * rootB m = 1 + diagonalM m * diagonalM m := by
  rw [rootB, diagonalM, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
    simpa [bCoeff, aCoeff, pow_two] using bRoot_sq m i
  · simp [Matrix.diagonal, hij]

lemma invBRoot_mul_B (m : I3 → ℝ) :
    invBRoot m * (1 + diagonalM m * diagonalM m) = rootB m := by
  rw [← rootB_sq]
  calc
    invBRoot m * (rootB m * rootB m) =
        (invBRoot m * rootB m) * rootB m := by noncomm_ring
    _ = rootB m := by rw [invBRoot_mul_rootB]; simp

lemma invBRoot_commute_M (m : I3 → ℝ) :
    invBRoot m * diagonalM m = diagonalM m * invBRoot m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invBRoot, diagonalM, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

noncomputable def swapOrthogonal (m : I3 → ℝ) : Mat6 :=
  Matrix.fromBlocks
    (-(invBRoot m * diagonalM m)) (invBRoot m)
    (invBRoot m) (invBRoot m * diagonalM m)

lemma swapOrthogonal_transpose_mul (m : I3 → ℝ) :
    (swapOrthogonal m)ᵀ * swapOrthogonal m = 1 := by
  have hr0 : bRoot m 0 ≠ 0 := ne_of_gt (bRoot_pos m 0)
  have hr1 : bRoot m 1 ≠ 0 := ne_of_gt (bRoot_pos m 1)
  have hr2 : bRoot m 2 ≠ 0 := ne_of_gt (bRoot_pos m 2)
  have hs0 := bRoot_sq m 0
  have hs1 := bRoot_sq m 1
  have hs2 := bRoot_sq m 2
  simp [bCoeff, aCoeff] at hs0 hs1 hs2
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [swapOrthogonal, invBRoot, diagonalM,
      Matrix.fromBlocks_transpose, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals field_simp [hr0, hr1, hr2]
  all_goals nlinarith

lemma swapOrthogonal_mul_transpose (m : I3 → ℝ) :
    swapOrthogonal m * (swapOrthogonal m)ᵀ = 1 := by
  have hd := congrArg Matrix.det (swapOrthogonal_transpose_mul m)
  have hdet0 : (swapOrthogonal m).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose] at hd
    intro hz
    rw [hz] at hd
    norm_num at hd
  have hdet : IsUnit (swapOrthogonal m).det :=
    isUnit_iff_ne_zero.mpr hdet0
  have hinv : (swapOrthogonal m)⁻¹ = (swapOrthogonal m)ᵀ :=
    Matrix.inv_eq_left_inv (swapOrthogonal_transpose_mul m)
  rw [← hinv]
  exact (swapOrthogonal m).mul_nonsing_inv hdet

noncomputable def Dzero (m : I3 → ℝ) (E : Mat3) : Mat3 :=
  invBRoot m * E

noncomputable def Ezero (m : I3 → ℝ) (D : Mat3) : Mat3 :=
  rootB m * D

lemma swap_frame_before_polar (D E : Mat3) (m : I3 → ℝ) :
    swapOrthogonal m * graphFrame D E (diagonalM m) * swapMatrix =
      graphFrame (Dzero m E) (Ezero m D) (diagonalM m) := by
  rw [swapOrthogonal, graphFrame, swapMatrix,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  apply Matrix.fromBlocks_inj.mpr
  have hcomm := invBRoot_commute_M m
  have hB := invBRoot_mul_B m
  constructor
  · simp [Dzero]
  constructor
  · simp
    noncomm_ring
  constructor
  · simp [Dzero]
    rw [hcomm]
    noncomm_ring
  · simp [Ezero]
    calc
      invBRoot m * D + (invBRoot m * diagonalM m) *
          (diagonalM m * D) =
        (invBRoot m * (1 + diagonalM m * diagonalM m)) * D := by
          noncomm_ring
      _ = rootB m * D := by rw [hB]

lemma invBRoot_posDef (m : I3 → ℝ) : (invBRoot m).PosDef := by
  rw [invBRoot, Matrix.posDef_diagonal_iff]
  intro i
  exact inv_pos.mpr (bRoot_pos m i)

lemma Dzero_det_pos (m : I3 → ℝ) {E : Mat3} (hE : E.PosDef) :
    0 < (Dzero m E).det := by
  rw [Dzero, Matrix.det_mul]
  exact mul_pos (invBRoot_posDef m).det_pos hE.det_pos

lemma Ezero_det_pos (m : I3 → ℝ) {D : Mat3} (hD : D.PosDef) :
    0 < (Ezero m D).det := by
  rw [Ezero, Matrix.det_mul]
  exact mul_pos (rootB_posDef m).det_pos hD.det_pos

noncomputable def Rone (m : I3 → ℝ) (E : Mat3) (hE : E.PosDef) : SO3 :=
  polarRotation (Dzero m E) (Dzero_det_pos m hE)

noncomputable def Rtwo (m : I3 → ℝ) (D : Mat3) (hD : D.PosDef) : SO3 :=
  polarRotation (Ezero m D) (Ezero_det_pos m hD)

noncomputable def Hone (m : I3 → ℝ) (E : Mat3) : Mat3 :=
  polarH (Dzero m E)

noncomputable def Htwo (m : I3 → ℝ) (D : Mat3) : Mat3 :=
  polarH (Ezero m D)

lemma Rone_mul_Dzero (m : I3 → ℝ) (E : Mat3) (hE : E.PosDef) :
    (Rone m E hE : Mat3) * Dzero m E = Hone m E := by
  exact polarRotation_mul (Dzero m E) (Dzero_det_pos m hE)

lemma Rtwo_mul_Ezero (m : I3 → ℝ) (D : Mat3) (hD : D.PosDef) :
    (Rtwo m D hD : Mat3) * Ezero m D = Htwo m D := by
  exact polarRotation_mul (Ezero m D) (Ezero_det_pos m hD)

lemma Hone_posDef (m : I3 → ℝ) (E : Mat3) (hE : E.PosDef) :
    (Hone m E).PosDef :=
  polarH_posDef (Dzero m E) (ne_of_gt (Dzero_det_pos m hE))

lemma Htwo_posDef (m : I3 → ℝ) (D : Mat3) (hD : D.PosDef) :
    (Htwo m D).PosDef :=
  polarH_posDef (Ezero m D) (ne_of_gt (Ezero_det_pos m hD))

noncomputable def swappedM (m : I3 → ℝ)
    (D E : Mat3) (hD : D.PosDef) (hE : E.PosDef) : Mat3 :=
  (Rtwo m D hD : Mat3) * diagonalM m * (Rone m E hE : Mat3)ᵀ

lemma polar_frame (m : I3 → ℝ) (D E : Mat3)
    (hD : D.PosDef) (hE : E.PosDef) :
    Matrix.fromBlocks (Rone m E hE : Mat3) 0 0 (Rtwo m D hD : Mat3) *
        graphFrame (Dzero m E) (Ezero m D) (diagonalM m) =
      graphFrame (Hone m E) (Htwo m D) (swappedM m D E hD hE) := by
  rw [graphFrame, graphFrame, Matrix.fromBlocks_multiply]
  apply Matrix.fromBlocks_inj.mpr
  have hR1 := Rone_mul_Dzero m E hE
  have hR2 := Rtwo_mul_Ezero m D hD
  have hR1orth := so3_transpose_mul (Rone m E hE)
  constructor
  · simpa using hR1
  constructor
  · simp
  constructor
  · simp [swappedM]
    calc
      (Rtwo m D hD : Mat3) * (diagonalM m * Dzero m E) =
          (Rtwo m D hD : Mat3) * diagonalM m *
            ((Rone m E hE : Mat3)ᵀ * (Rone m E hE : Mat3)) *
              Dzero m E := by rw [hR1orth]; simp; noncomm_ring
      _ = swappedM m D E hD hE * Hone m E := by
        rw [← hR1]
        simp [swappedM]
        noncomm_ring
  · simpa using hR2

lemma Hone_sq (m : I3 → ℝ) (E : Mat3) (hE : E.PosDef) :
    Hone m E * Hone m E = (Dzero m E)ᵀ * Dzero m E :=
  polarH_sq (Dzero m E) (ne_of_gt (Dzero_det_pos m hE))

lemma Htwo_sq (m : I3 → ℝ) (D : Mat3) (hD : D.PosDef) :
    Htwo m D * Htwo m D = (Ezero m D)ᵀ * Ezero m D :=
  polarH_sq (Ezero m D) (ne_of_gt (Ezero_det_pos m hD))

lemma HoneSq_posDef (m : I3 → ℝ) (E : Mat3) (hE : E.PosDef) :
    (Hone m E * Hone m E).PosDef := by
  rw [Hone_sq m E hE]
  exact transpose_mul_posDef_of_det_ne_zero (ne_of_gt (Dzero_det_pos m hE))

lemma HtwoSq_posDef (m : I3 → ℝ) (D : Mat3) (hD : D.PosDef) :
    (Htwo m D * Htwo m D).PosDef := by
  rw [Htwo_sq m D hD]
  exact transpose_mul_posDef_of_det_ne_zero (ne_of_gt (Ezero_det_pos m hD))

noncomputable def swappedP (m : I3 → ℝ) (E : Mat3) (_hE : E.PosDef) : Mat3 :=
  invCof (Hone m E * Hone m E)

noncomputable def swappedQ (m : I3 → ℝ) (D : Mat3) (_hD : D.PosDef) : Mat3 :=
  invCof (Htwo m D * Htwo m D)

noncomputable def swapGraphData {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = diagonalM m) :
    GraphData (swapMetric g) := by
  let Dv := Hone m d.E
  let Ev := Htwo m d.D
  let Mv := swappedM m d.D d.E d.D_pos d.E_pos
  let CP := Dv * Dv
  let CQ := Ev * Ev
  have hCP : CP.PosDef := HoneSq_posDef m d.E d.E_pos
  have hCQ : CQ.PosDef := HtwoSq_posDef m d.D d.D_pos
  let Pv := invCof CP
  let Qv := invCof CQ
  refine
    { P := Pv, Q := Qv, M := Mv, D := Dv, E := Ev
      P_pos := invCof_posDef hCP, Q_pos := invCof_posDef hCQ
      D_pos := Hone_posDef m d.E d.E_pos
      E_pos := Htwo_posDef m d.D d.D_pos
      D_sq := ?_, E_sq := ?_, cometric_eq := ?_ }
  · change CP = cofactor3 (invCof CP)
    exact (cofactor3_invCof hCP).symm
  · change CQ = cofactor3 (invCof CQ)
    exact (cofactor3_invCof hCQ).symm
  · let A : Mat6 := graphFrame d.D d.E (diagonalM m)
    let A0 : Mat6 := graphFrame (Dzero m d.E) (Ezero m d.D) (diagonalM m)
    let C : Mat6 := graphFrame Dv Ev Mv
    let O : Mat6 := swapOrthogonal m
    let L : Mat6 := innerMatrix (Rone m d.E d.E_pos, Rtwo m d.D d.D_pos)
    let J : Mat6 := swapMatrix
    have hbefore : O * A * J = A0 := by
      exact swap_frame_before_polar d.D d.E m
    have hpolar : L * A0 = C := by
      exact polar_frame m d.D d.E d.D_pos d.E_pos
    have hC : C = L * O * A * J := by
      calc
        C = L * A0 := hpolar.symm
        _ = L * (O * A * J) := by rw [hbefore]
        _ = L * O * A * J := by noncomm_ring
    have hLtL : Lᵀ * L = 1 :=
      innerMatrix_transpose_mul (Rone m d.E d.E_pos, Rtwo m d.D d.D_pos)
    have hOtO : Oᵀ * O = 1 := swapOrthogonal_transpose_mul m
    rw [swapMetric_gram_inv, d.cometric_eq, hM]
    change Jᵀ * (Aᵀ * A) * J = Cᵀ * C
    rw [hC, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul]
    calc
      Jᵀ * (Aᵀ * A) * J =
          Jᵀ * Aᵀ * (Oᵀ * O) * A * J := by
        rw [hOtO]
        simp
        noncomm_ring
      _ = Jᵀ * Aᵀ * Oᵀ * (Lᵀ * L) * O * A * J := by
        rw [hLtL]
        simp
        noncomm_ring
      _ = (Jᵀ * (Aᵀ * (Oᵀ * Lᵀ))) * (L * O * A * J) := by
        noncomm_ring

end S3xS3.Trivial.FactorSwap
