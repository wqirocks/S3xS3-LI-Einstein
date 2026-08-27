import S3xS3.Trivial.SwappedEuler

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.SecondBarrier

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.FactorSwap
open S3xS3.Trivial.FactorSwapFormulas
open S3xS3.Trivial.SwappedEuler
open S3xS3.Trivial.SwapNaturality

lemma strictBelowFour_diagonal_of_entries (s : I3 → ℝ)
    (hs : ∀ i, s i < 4) :
    S3xS3.Trivial.StrictBelowFour (Matrix.diagonal s) := by
  intro v hv
  have hn := normSq3_pos hv
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  simp [S3xS3.Trivial.quad3, S3xS3.Trivial.normSq3,
    Fin.sum_univ_succ] at hn ⊢
  have hn0 : 0 ≤ (4 - s 0) * v 0 ^ 2 :=
    mul_nonneg (sub_nonneg.mpr h0.le) (sq_nonneg _)
  have hn1 : 0 ≤ (4 - s 1) * v 1 ^ 2 :=
    mul_nonneg (sub_nonneg.mpr h1.le) (sq_nonneg _)
  have hn2 : 0 ≤ (4 - s 2) * v 2 ^ 2 :=
    mul_nonneg (sub_nonneg.mpr h2.le) (sq_nonneg _)
  by_cases hv0 : v 0 = 0
  · by_cases hv1 : v 1 = 0
    · have hv2 : v 2 ≠ 0 := by
        intro hv2
        apply hv
        funext i
        fin_cases i <;> assumption
      have hp2 : 0 < (4 - s 2) * v 2 ^ 2 :=
        mul_pos (sub_pos.mpr h2) (sq_pos_of_ne_zero hv2)
      nlinarith
    · have hp1 : 0 < (4 - s 1) * v 1 ^ 2 :=
        mul_pos (sub_pos.mpr h1) (sq_pos_of_ne_zero hv1)
      nlinarith
  · have hp0 : 0 < (4 - s 0) * v 0 ^ 2 :=
      mul_pos (sub_pos.mpr h0) (sq_pos_of_ne_zero hv0)
    nlinarith

lemma mulVec_basis3_diagonal (s : I3 → ℝ) (i : I3) :
    (Matrix.diagonal s : Mat3) *ᵥ basis3 i = s i • basis3 i := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [basis3, Matrix.mulVec, dotProduct]

lemma matrix_eigenvectors_from_diagonalization (A : Mat3) (U : SO3)
    (s : I3 → ℝ)
    (hdiag : (U : Mat3)ᵀ * A * U = Matrix.diagonal s) (i : I3) :
    A *ᵥ ((U : Mat3) *ᵥ basis3 i) =
      s i • ((U : Mat3) *ᵥ basis3 i) := by
  have hAU : A * (U : Mat3) =
      (U : Mat3) * Matrix.diagonal s := by
    calc
      A * (U : Mat3) =
          ((U : Mat3) * (U : Mat3)ᵀ) * A * U := by
        rw [so3_mul_transpose]
        simp
      _ = (U : Mat3) * ((U : Mat3)ᵀ * A * U) := by noncomm_ring
      _ = (U : Mat3) * Matrix.diagonal s := by rw [hdiag]
  rw [Matrix.mulVec_mulVec, hAU, ← Matrix.mulVec_mulVec,
    mulVec_basis3_diagonal]
  exact Matrix.mulVec_smul (U : Mat3) (s i) (basis3 i)

lemma so3_mulVec_basis_ne_zero (U : SO3) (i : I3) :
    (U : Mat3) *ᵥ basis3 i ≠ 0 := by
  intro hz
  have h := congrArg (fun v : Vec3 ↦ (U : Mat3)ᵀ *ᵥ v) hz
  rw [Matrix.mulVec_mulVec, so3_transpose_mul] at h
  have hb : basis3 i = 0 := by simpa using h
  exact (basis3_ne_zero i) hb

lemma mulVec_ne_zero_of_det_ne_zero {X : Mat3} (hX : X.det ≠ 0)
    {v : Vec3} (hv : v ≠ 0) : X *ᵥ v ≠ 0 := by
  have hunit : IsUnit X :=
    (Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr hX)
  intro hx
  apply hv
  apply Matrix.mulVec_injective_iff_isUnit.mpr hunit
  simpa using hx

lemma transpose_mul_eigen_to_mul_transpose (X : Mat3) (u : Vec3)
    (s : ℝ) (hu : (Xᵀ * X) *ᵥ u = s • u) :
    (X * Xᵀ) *ᵥ (X *ᵥ u) = s • (X *ᵥ u) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    hu, Matrix.mulVec_smul]

lemma quad3_eigenvalue {A : Mat3} {v : Vec3} {s : ℝ}
    (hAv : A *ᵥ v = s • v) :
    S3xS3.Trivial.quad3 A v =
      s * S3xS3.Trivial.normSq3 v := by
  rw [quad3_eq_dotProduct, hAv, normSq3_eq_dotProduct]
  simp only [dotProduct, Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem strictBelowFour_transpose_mul_of_mul_transpose
    (X : Mat3) (hXdet : X.det ≠ 0)
    (hfirst : S3xS3.Trivial.StrictBelowFour (X * Xᵀ)) :
    S3xS3.Trivial.StrictBelowFour (Xᵀ * X) := by
  have hA : (Xᵀ * X).PosDef :=
    transpose_mul_posDef_of_det_ne_zero hXdet
  obtain ⟨U, s, hspos, hdiag⟩ := diagonalize_posDef_three hA
  have hslt : ∀ i, s i < 4 := by
    intro i
    let u : Vec3 := (U : Mat3) *ᵥ basis3 i
    let w : Vec3 := X *ᵥ u
    have hu0 : u ≠ 0 := so3_mulVec_basis_ne_zero U i
    have hw0 : w ≠ 0 := mulVec_ne_zero_of_det_ne_zero hXdet hu0
    have hAu : (Xᵀ * X) *ᵥ u = s i • u :=
      matrix_eigenvectors_from_diagonalization (Xᵀ * X) U s hdiag i
    have hBw : (X * Xᵀ) *ᵥ w = s i • w :=
      transpose_mul_eigen_to_mul_transpose X u (s i) hAu
    have hb := hfirst w hw0
    rw [quad3_eigenvalue hBw] at hb
    have hn := normSq3_pos hw0
    nlinarith
  have hdiagBarrier := strictBelowFour_diagonal_of_entries s hslt
  rw [← hdiag] at hdiagBarrier
  exact strictBelowFour_of_conjugate (Xᵀ * X) U hdiagBarrier

lemma einsteinConstant_pos_for_graph {g : LeftInvariantMetric}
    (d : GraphData g) {lambda : ℝ}
    (hEin : ricci g = lambda • g.gram) : 0 < lambda := by
  let p := eulerForGraph d hEin
  have hk := p.euler.kappa_pos
  rw [p.kappa_eq] at hk
  nlinarith

lemma ricci_swap_of_einstein_constant {g : LeftInvariantMetric}
    {lambda : ℝ} (hEin : ricci g = lambda • g.gram) :
    ricci (swapMetric g) = lambda • (swapMetric g).gram := by
  rw [ricci_swap, hEin]
  change swapMatrixᵀ * (lambda • g.gram) * swapMatrix =
    lambda • (swapMatrixᵀ * g.gram * swapMatrix)
  simp

noncomputable def barrierTransferMatrix {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) (t : ℝ) : Mat3 :=
  Real.sqrt t • (pdSqrt d.P * invBRoot m)

lemma barrierTransferMatrix_transpose {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) (t : ℝ) :
    (barrierTransferMatrix d m t)ᵀ =
      Real.sqrt t • (invBRoot m * pdSqrt d.P) := by
  rw [barrierTransferMatrix, Matrix.transpose_smul, Matrix.transpose_mul,
    pdSqrt_transpose d.P_pos, invBRoot_transpose]

lemma barrierTransfer_mul_transpose {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) (t : ℝ) (ht : 0 < t) :
    barrierTransferMatrix d m t * (barrierTransferMatrix d m t)ᵀ =
      t • (pdSqrt d.P * (invBRoot m * invBRoot m) * pdSqrt d.P) := by
  rw [barrierTransferMatrix_transpose, barrierTransferMatrix,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hs : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  congr 1
  · simpa [pow_two] using hs
  · noncomm_ring

lemma barrierTransfer_transpose_mul {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) (t : ℝ) (ht : 0 < t) :
    (barrierTransferMatrix d m t)ᵀ * barrierTransferMatrix d m t =
      secondMatrix m (t • d.P) := by
  rw [barrierTransferMatrix_transpose, barrierTransferMatrix,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, secondMatrix,
    Matrix.mul_smul, Matrix.smul_mul]
  rw [show invBRoot m * pdSqrt d.P *
        (pdSqrt d.P * invBRoot m) =
      invBRoot m * (pdSqrt d.P * pdSqrt d.P) * invBRoot m by
        noncomm_ring,
    pdSqrt_sq d.P_pos]
  have hs : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  congr 1
  · simpa [pow_two] using hs

lemma barrierTransfer_det_ne_zero {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ) (t : ℝ) (ht : 0 < t) :
    (barrierTransferMatrix d m t).det ≠ 0 := by
  rw [barrierTransferMatrix, Matrix.det_smul, Matrix.det_mul]
  exact mul_ne_zero
    (pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.2 ht)))
    (mul_ne_zero (ne_of_gt (pdSqrt_posDef d.P_pos).det_pos)
      (ne_of_gt (invBRoot_posDef m).det_pos))

theorem second_barrier_for_graph_of_trivial {g : LeftInvariantMetric}
    (d : GraphData g) (m : I3 → ℝ)
    (hM : d.M = diagonalM m) (hm : ∀ i, m i ≠ 0)
    {lambda : ℝ} (hEin : ricci g = lambda • g.gram)
    (htriv : ¬ HasNontrivialInnerIsotropy g) :
    S3xS3.Trivial.StrictBelowFour
      (secondMatrix m ((4 * lambda / d.P.det) • d.P)) := by
  let dv := swapGraphData d m hM
  have hEinV : ricci (swapMetric g) =
      lambda • (swapMetric g).gram :=
    ricci_swap_of_einstein_constant hEin
  have hMdetV : dv.M.det ≠ 0 :=
    swapGraphData_M_det_ne_zero d m hM hm
  have htrivV : ¬ HasNontrivialInnerIsotropy (swapMetric g) := by
    intro hnon
    exact htriv (nontrivial_of_swap hnon)
  have hb := first_barrier_for_graph_of_trivial dv hEinV hMdetV htrivV
  rw [show dv.Q.det = swapDetRoot m * d.P.det by
        exact swapGraphData_det_Q d m hM,
      show dv.Q = swappedQClosed d m by
        exact swapGraphData_Q_closed d m hM] at hb
  let delta := swapDetRoot m
  let t := 4 * lambda / d.P.det
  have hdelta0 : swapDetRoot m ≠ 0 := ne_of_gt (swapDetRoot_pos m)
  have hPdet : d.P.det ≠ 0 := ne_of_gt d.P_pos.det_pos
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (mul_pos (by norm_num) (einsteinConstant_pos_for_graph d hEin))
      d.P_pos.det_pos
  have hscalar :
      (4 * lambda / (swapDetRoot m * d.P.det)) •
          swappedQClosed d m =
        t • (pdSqrt d.P * (invBRoot m * invBRoot m) * pdSqrt d.P) := by
    rw [swappedQClosed, smul_smul]
    congr 1
    dsimp [t, delta]
    field_simp [hdelta0, hPdet]
  rw [hscalar] at hb
  let X := barrierTransferMatrix d m t
  have hXX : X * Xᵀ =
      t • (pdSqrt d.P * (invBRoot m * invBRoot m) * pdSqrt d.P) :=
    barrierTransfer_mul_transpose d m t ht
  have hXtX : Xᵀ * X = secondMatrix m (t • d.P) :=
    barrierTransfer_transpose_mul d m t ht
  have hXdet : X.det ≠ 0 := barrierTransfer_det_ne_zero d m t ht
  rw [← hXX] at hb
  have hsecond := strictBelowFour_transpose_mul_of_mul_transpose X hXdet hb
  rw [hXtX] at hsecond
  exact hsecond

end S3xS3.Trivial.SecondBarrier
