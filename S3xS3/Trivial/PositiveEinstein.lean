import S3xS3.Trivial.EinsteinBridge

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.PositiveEinstein

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.EinsteinBridge
open S3xS3.Trivial.Euler

noncomputable def killingDerivativeCoeff (r : RawGraph)
    (i a k : I6) : ℝ :=
  ∑ j, r.inverseTranspose j a *
    (r.gamma i j k + r.bracketCoeff j i k)

noncomputable def killingEnergy (r : RawGraph) : ℝ :=
  ∑ i, ∑ a, ∑ k, killingDerivativeCoeff r i a k ^ 2

noncomputable def backgroundRicciTrace (r : RawGraph) : ℝ :=
  ∑ a, ∑ j, ∑ k,
    r.inverseTranspose j a * r.inverseTranspose k a * r.ricciCoeff j k

set_option maxHeartbeats 20000000 in
lemma bochner_certificate (r : RawGraph) (h : RawPositive r) :
    backgroundRicciTrace r = killingEnergy r := by
  simp [backgroundRicciTrace, killingEnergy,
    killingDerivativeCoeff, RawGraph.ricciCoeff,
    RawGraph.curvatureCoeff, RawGraph.gamma, RawGraph.bracketCoeff,
    RawGraph.inverseTranspose, RawGraph.Dinv, RawGraph.Einv,
    RawGraph.frame, graphFrame, RawGraph.D, RawGraph.E,
    frameVec, basisVec, bracket, cross_apply, Matrix.mulVec,
    dotProduct, Matrix.mul_apply, Fin.sum_univ_succ]
  field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
    ne_of_gt (h.d_pos 2), ne_of_gt (h.e_pos 0),
    ne_of_gt (h.e_pos 1), ne_of_gt (h.e_pos 2)]
  ring

lemma bracketCoeff_swap (r : RawGraph) (i j k : I6) :
    r.bracketCoeff j i k = -r.bracketCoeff i j k := by
  simp [RawGraph.bracketCoeff, RawGraph.inverseTranspose,
    RawGraph.Dinv, RawGraph.Einv, RawGraph.frame, graphFrame,
    RawGraph.D, RawGraph.E, frameVec, basisVec, bracket, cross_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

lemma gamma_torsion (r : RawGraph) (i j k : I6) :
    r.gamma i j k - r.gamma j i k = r.bracketCoeff i j k := by
  rw [RawGraph.gamma, RawGraph.gamma]
  rw [bracketCoeff_swap r j i k, bracketCoeff_swap r k j i,
    bracketCoeff_swap r i k j]
  ring

lemma bracketCoeff_012_pos (r : RawGraph) (h : RawPositive r) :
    0 < r.bracketCoeff (Sum.inl 0) (Sum.inl 1) (Sum.inl 2) := by
  simp [RawGraph.bracketCoeff, RawGraph.inverseTranspose,
    RawGraph.Dinv, RawGraph.Einv, RawGraph.frame, graphFrame,
    RawGraph.D, RawGraph.E, frameVec, basisVec, bracket, cross_apply,
    Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Fin.sum_univ_succ]
  simpa [div_eq_inv_mul, mul_comm] using
    (div_pos (mul_pos (h.d_pos 0) (h.d_pos 1)) (h.d_pos 2))

lemma killingEnergy_nonneg (r : RawGraph) : 0 ≤ killingEnergy r := by
  simp only [killingEnergy]
  positivity

lemma killingEnergy_pos (r : RawGraph) (h : RawPositive r) :
    0 < killingEnergy r := by
  have hnonneg := killingEnergy_nonneg r
  apply lt_of_le_of_ne hnonneg
  intro hzero'
  have hzero : killingEnergy r = 0 := hzero'.symm
  have houter :
      (fun i : I6 ↦ ∑ a, ∑ k, killingDerivativeCoeff r i a k ^ 2) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg (fun i ↦ by positivity)).mp hzero
  have hall : ∀ i a k : I6, killingDerivativeCoeff r i a k = 0 := by
    intro i a k
    have hi : ∑ a, ∑ k, killingDerivativeCoeff r i a k ^ 2 = 0 :=
      congrFun houter i
    have hmiddle :
        (fun a : I6 ↦ ∑ k, killingDerivativeCoeff r i a k ^ 2) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (fun a ↦ by positivity)).mp hi
    have ha : ∑ k, killingDerivativeCoeff r i a k ^ 2 = 0 :=
      congrFun hmiddle a
    have hinner :
        (fun k : I6 ↦ killingDerivativeCoeff r i a k ^ 2) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (fun k ↦ sq_nonneg _)).mp ha
    have hk := congrFun hinner k
    simp only [Pi.zero_apply, sq_eq_zero_iff] at hk
    exact hk
  have hKzero : ∀ i j k : I6,
      r.gamma i j k + r.bracketCoeff j i k = 0 := by
    intro i j k
    let K : LieVec := fun l ↦ r.gamma i l k + r.bracketCoeff l i k
    have hDK : r.inverseTransposeᵀ *ᵥ K = 0 := by
      funext a
      simpa [K, killingDerivativeCoeff, Matrix.mulVec, dotProduct] using
        hall i a k
    have hDt : r.frame * r.inverseTransposeᵀ = 1 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_one] using
        congrArg Matrix.transpose (r.inverseTranspose_mul h)
    have hh := congrArg (fun v : LieVec ↦ r.frame *ᵥ v) hDK
    simp only [Matrix.mulVec_mulVec, hDt, Matrix.one_mulVec,
      Matrix.mulVec_zero] at hh
    exact congrFun hh j
  let i : I6 := Sum.inl 0
  let j : I6 := Sum.inl 1
  let k : I6 := Sum.inl 2
  have hij := hKzero i j k
  have hji := hKzero j i k
  have hswap := bracketCoeff_swap r i j k
  have htorsion := gamma_torsion r i j k
  have hpos := bracketCoeff_012_pos r h
  change 0 < r.bracketCoeff i j k at hpos
  linarith

noncomputable def backgroundNorm (r : RawGraph) : ℝ :=
  ∑ a, ∑ j, r.inverseTranspose j a ^ 2

lemma backgroundNorm_pos (r : RawGraph) (h : RawPositive r) :
    0 < backgroundNorm r := by
  let a : I6 := Sum.inr 0
  let j : I6 := Sum.inr 0
  have hentry : r.inverseTranspose j a = (r.e 0)⁻¹ := by
    simp [a, j, RawGraph.inverseTranspose, RawGraph.Einv]
  have hterm : 0 < r.inverseTranspose j a ^ 2 := by
    rw [hentry]
    exact sq_pos_of_ne_zero (inv_ne_zero (ne_of_gt (h.e_pos 0)))
  have hinner : r.inverseTranspose j a ^ 2 ≤
      ∑ q, r.inverseTranspose q a ^ 2 := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun q ↦ r.inverseTranspose q a ^ 2)
      (fun q _ ↦ sq_nonneg _) (Finset.mem_univ j)
  have houter : (∑ q, r.inverseTranspose q a ^ 2) ≤ backgroundNorm r := by
    rw [backgroundNorm]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun q ↦ ∑ z, r.inverseTranspose z q ^ 2)
      (fun q _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
      (Finset.mem_univ a)
  exact lt_of_lt_of_le hterm (hinner.trans houter)

lemma backgroundRicciTrace_of_Einstein (r : RawGraph) (h : RawPositive r)
    {lambda : ℝ}
    (hEin : ricci (r.metric h) = lambda • (r.metric h).gram) :
    backgroundRicciTrace r = lambda * backgroundNorm r := by
  simp only [backgroundRicciTrace, backgroundNorm]
  simp_rw [r.ricciCoeff_of_Einstein h hEin]
  simp
  simp [Fin.sum_univ_succ]
  ring

theorem einsteinConstant_pos (r : RawGraph) (h : RawPositive r)
    {lambda : ℝ}
    (hEin : ricci (r.metric h) = lambda • (r.metric h).gram) :
    0 < lambda := by
  have henergy : 0 < killingEnergy r := killingEnergy_pos r h
  have hbochner := bochner_certificate r h
  have htrace := backgroundRicciTrace_of_Einstein r h hEin
  have hproduct : 0 < lambda * backgroundNorm r := by
    rw [← htrace, hbochner]
    exact henergy
  have hnorm : 0 < backgroundNorm r := backgroundNorm_pos r h
  nlinarith

noncomputable def eulerDataOfEinstein (r : RawGraph) (h : RawPositive r)
    {lambda : ℝ}
    (hEin : ricci (r.metric h) = lambda • (r.metric h).gram) : EulerData where
  P := r.P
  Q := r.Q
  M := r.M
  kappa := 2 * lambda
  P_pos := h.P_posDef
  Q_pos := h.Q_posDef
  kappa_pos := mul_pos two_pos (einsteinConstant_pos r h hEin)
  gradP := by
    simpa [RawGraph.gradPExpr, RawGraph.residual] using
      r.gradP_eq_of_Einstein h hEin
  gradQ := by
    simpa [RawGraph.gradQExpr, RawGraph.residual] using
      r.gradQ_eq_of_Einstein h hEin
  gradM := by
    simpa [RawGraph.gradMExpr, RawGraph.residual] using
      r.gradM_eq_zero_of_Einstein h hEin

end S3xS3.Trivial.PositiveEinstein
