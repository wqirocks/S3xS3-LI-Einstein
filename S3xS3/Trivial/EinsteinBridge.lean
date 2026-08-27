import S3xS3.Trivial.Euler

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.EinsteinBridge

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler

structure RawGraph where
  d : I3 → ℝ
  e : I3 → ℝ
  M : Mat3

structure RawPositive (r : RawGraph) : Prop where
  d_pos : ∀ i, 0 < r.d i
  e_pos : ∀ i, 0 < r.e i

def RawGraph.D (r : RawGraph) : Mat3 := Matrix.diagonal r.d
def RawGraph.E (r : RawGraph) : Mat3 := Matrix.diagonal r.e
def RawGraph.frame (r : RawGraph) : Mat6 := graphFrame r.D r.E r.M

noncomputable def RawGraph.p (r : RawGraph) : I3 → ℝ :=
  ![r.d 1 * r.d 2 / r.d 0,
    r.d 0 * r.d 2 / r.d 1,
    r.d 0 * r.d 1 / r.d 2]

noncomputable def RawGraph.q (r : RawGraph) : I3 → ℝ :=
  ![r.e 1 * r.e 2 / r.e 0,
    r.e 0 * r.e 2 / r.e 1,
    r.e 0 * r.e 1 / r.e 2]

noncomputable def RawGraph.P (r : RawGraph) : Mat3 := Matrix.diagonal r.p
noncomputable def RawGraph.Q (r : RawGraph) : Mat3 := Matrix.diagonal r.q

lemma RawPositive.p_pos {r : RawGraph} (h : RawPositive r) (i : I3) :
    0 < r.p i := by
  fin_cases i
  · simpa [RawGraph.p] using div_pos (mul_pos (h.d_pos 1) (h.d_pos 2)) (h.d_pos 0)
  · simpa [RawGraph.p] using div_pos (mul_pos (h.d_pos 0) (h.d_pos 2)) (h.d_pos 1)
  · simpa [RawGraph.p] using div_pos (mul_pos (h.d_pos 0) (h.d_pos 1)) (h.d_pos 2)

lemma RawPositive.q_pos {r : RawGraph} (h : RawPositive r) (i : I3) :
    0 < r.q i := by
  fin_cases i
  · simpa [RawGraph.q] using div_pos (mul_pos (h.e_pos 1) (h.e_pos 2)) (h.e_pos 0)
  · simpa [RawGraph.q] using div_pos (mul_pos (h.e_pos 0) (h.e_pos 2)) (h.e_pos 1)
  · simpa [RawGraph.q] using div_pos (mul_pos (h.e_pos 0) (h.e_pos 1)) (h.e_pos 2)

lemma RawPositive.D_posDef {r : RawGraph} (h : RawPositive r) : r.D.PosDef := by
  exact Matrix.posDef_diagonal_iff.mpr h.d_pos

lemma RawPositive.E_posDef {r : RawGraph} (h : RawPositive r) : r.E.PosDef := by
  exact Matrix.posDef_diagonal_iff.mpr h.e_pos

lemma RawPositive.P_posDef {r : RawGraph} (h : RawPositive r) : r.P.PosDef := by
  exact Matrix.posDef_diagonal_iff.mpr h.p_pos

lemma RawPositive.Q_posDef {r : RawGraph} (h : RawPositive r) : r.Q.PosDef := by
  exact Matrix.posDef_diagonal_iff.mpr h.q_pos

lemma RawGraph.D_sq_cofactor_P (r : RawGraph) (h : RawPositive r) :
    r.D * r.D = cofactor3 r.P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RawGraph.D, RawGraph.P, RawGraph.p, cofactor3,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
      ne_of_gt (h.d_pos 2)]

lemma RawGraph.E_sq_cofactor_Q (r : RawGraph) (h : RawPositive r) :
    r.E * r.E = cofactor3 r.Q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RawGraph.E, RawGraph.Q, RawGraph.q, cofactor3,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt (h.e_pos 0), ne_of_gt (h.e_pos 1),
      ne_of_gt (h.e_pos 2)]

lemma RawGraph.frame_det_ne_zero (r : RawGraph) (h : RawPositive r) :
    r.frame.det ≠ 0 :=
  graphFrame_det_ne_zero h.D_posDef h.E_posDef

noncomputable def RawGraph.metric (r : RawGraph) (h : RawPositive r) :
    LeftInvariantMetric := metricOfFrame r.frame (r.frame_det_ne_zero h)

noncomputable def RawGraph.graphData (r : RawGraph) (h : RawPositive r) :
    GraphData (r.metric h) where
  P := r.P
  Q := r.Q
  M := r.M
  D := r.D
  E := r.E
  P_pos := h.P_posDef
  Q_pos := h.Q_posDef
  D_pos := h.D_posDef
  E_pos := h.E_posDef
  D_sq := r.D_sq_cofactor_P h
  E_sq := r.E_sq_cofactor_Q h
  cometric_eq := by
    simpa [RawGraph.metric, RawGraph.frame] using
      metricOfFrame_gram_inv r.frame (r.frame_det_ne_zero h)

noncomputable def RawGraph.Dinv (r : RawGraph) : Mat3 :=
  Matrix.diagonal (fun i ↦ (r.d i)⁻¹)

noncomputable def RawGraph.Einv (r : RawGraph) : Mat3 :=
  Matrix.diagonal (fun i ↦ (r.e i)⁻¹)

noncomputable def RawGraph.inverseTranspose (r : RawGraph) : Mat6 :=
  Matrix.fromBlocks r.Dinv (-(r.Mᵀ * r.Einv)) 0 r.Einv

lemma RawGraph.inverseTranspose_mul (r : RawGraph) (h : RawPositive r) :
    r.inverseTranspose * r.frameᵀ = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [RawGraph.inverseTranspose, RawGraph.frame, graphFrame,
      RawGraph.Dinv, RawGraph.Einv, RawGraph.D, RawGraph.E,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
      ne_of_gt (h.d_pos 2), ne_of_gt (h.e_pos 0),
      ne_of_gt (h.e_pos 1), ne_of_gt (h.e_pos 2)] <;> ring

lemma RawGraph.mul_inverseTranspose (r : RawGraph) (h : RawPositive r) :
    r.frameᵀ * r.inverseTranspose = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [RawGraph.inverseTranspose, RawGraph.frame, graphFrame,
      RawGraph.Dinv, RawGraph.Einv, RawGraph.D, RawGraph.E,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
      ne_of_gt (h.d_pos 2), ne_of_gt (h.e_pos 0),
      ne_of_gt (h.e_pos 1), ne_of_gt (h.e_pos 2)] <;> ring

def frameVec (V : Mat6) (i : I6) : LieVec := V *ᵥ basisVec i

@[simp] lemma frameVec_apply (V : Mat6) (i j : I6) :
    frameVec V i j = V j i := by
  simp [frameVec, basisVec, Matrix.mulVec, dotProduct]

lemma vec_eq_sum_frame {V D : Mat6} (hVD : V * D = 1) (x : LieVec) :
    x = ∑ i, (D *ᵥ x) i • frameVec V i := by
  have hx : V *ᵥ (D *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hVD]
    simp
  calc
    x = V *ᵥ (D *ᵥ x) := hx.symm
    _ = ∑ i, (D *ᵥ x) i • frameVec V i := by
      funext j
      simp [frameVec, basisVec, Matrix.mulVec, dotProduct, mul_comm]

lemma frameMetric_gram_congruence (C : Mat6) (hC : C.det ≠ 0) :
    C * (metricOfFrame C hC).gram * Cᵀ = 1 := by
  have hunitDet : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  have hunitC : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr hunitDet
  have hunitCt : IsUnit Cᵀ := (Matrix.isUnit_transpose C).2 hunitC
  letI : Invertible C := hunitC.invertible
  letI : Invertible Cᵀ := hunitCt.invertible
  rw [metricOfFrame_gram, Matrix.mul_inv_rev]
  simp

lemma frameMetric_orthonormal (C : Mat6) (hC : C.det ≠ 0) (i j : I6) :
    metricInner (metricOfFrame C hC) (frameVec Cᵀ i) (frameVec Cᵀ j) =
      if i = j then 1 else 0 := by
  have hcong := congrArg (fun M : Mat6 ↦ M i j)
    (frameMetric_gram_congruence C hC)
  rw [metricInner]
  have hi : frameVec Cᵀ i = C i := by funext k; simp [frameVec_apply]
  have hj : frameVec Cᵀ j = C j := by funext k; simp [frameVec_apply]
  rw [hi, hj]
  rw [Matrix.mul_mul_apply] at hcong
  simpa [Matrix.one_apply] using hcong

noncomputable def RawGraph.bracketCoeff (r : RawGraph) (i j k : I6) : ℝ :=
  (r.inverseTranspose *ᵥ bracket (frameVec r.frameᵀ i) (frameVec r.frameᵀ j)) k

noncomputable def RawGraph.gamma (r : RawGraph) (i j k : I6) : ℝ :=
  (r.bracketCoeff i j k - r.bracketCoeff j k i + r.bracketCoeff k i j) / 2

noncomputable def RawGraph.curvatureCoeff (r : RawGraph)
    (i j k n : I6) : ℝ :=
  (∑ m, r.gamma j k m * r.gamma i m n) -
    (∑ m, r.gamma i k m * r.gamma j m n) -
      ∑ m, r.bracketCoeff i j m * r.gamma m k n

noncomputable def RawGraph.ricciCoeff (r : RawGraph) (j k : I6) : ℝ :=
  ∑ i, r.curvatureCoeff i j k i

noncomputable def metricInnerLeftLinear (g : LeftInvariantMetric) (y : LieVec) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := fun x ↦ metricInner g x y
  map_add' := fun x x' ↦ metricInner_add_left g x x' y
  map_smul' c x := by
    simp only [metricInner_smul_left, RingHom.id_apply, smul_eq_mul]

lemma RawGraph.vec_eq_sum_frame (r : RawGraph) (h : RawPositive r) (x : LieVec) :
    x = ∑ i, (r.inverseTranspose *ᵥ x) i • frameVec r.frameᵀ i :=
  S3xS3.Trivial.EinsteinBridge.vec_eq_sum_frame (r.mul_inverseTranspose h) x

lemma RawGraph.coordinate_eq_metric (r : RawGraph) (h : RawPositive r)
    (x : LieVec) (k : I6) :
    (r.inverseTranspose *ᵥ x) k =
      metricInner (r.metric h) x (frameVec r.frameᵀ k) := by
  conv_rhs => rw [r.vec_eq_sum_frame h x]
  change (r.inverseTranspose *ᵥ x) k =
    metricInnerLeftLinear (r.metric h) (frameVec r.frameᵀ k)
      (∑ i, (r.inverseTranspose *ᵥ x) i • frameVec r.frameᵀ i)
  rw [map_sum]
  simp [metricInnerLeftLinear, RawGraph.metric, frameMetric_orthonormal]

lemma RawGraph.bracket_metric (r : RawGraph) (h : RawPositive r)
    (i j k : I6) :
    metricInner (r.metric h)
        (bracket (frameVec r.frameᵀ i) (frameVec r.frameᵀ j))
        (frameVec r.frameᵀ k) = r.bracketCoeff i j k := by
  rw [← r.coordinate_eq_metric h]
  rfl

lemma RawGraph.connection_coordinate (r : RawGraph) (h : RawPositive r)
    (i j k : I6) :
    (r.inverseTranspose *ᵥ
      connectionVec (r.metric h) (frameVec r.frameᵀ i)
        (frameVec r.frameᵀ j)) k = r.gamma i j k := by
  rw [r.coordinate_eq_metric h, metricInner_connectionVec]
  rw [koszulForm, r.bracket_metric h, r.bracket_metric h, r.bracket_metric h]
  rfl

noncomputable def coordinateLinear (D : Mat6) (n : I6) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := fun x ↦ (D *ᵥ x) n
  map_add' x y := by rw [Matrix.mulVec_add]; rfl
  map_smul' c x := by rw [Matrix.mulVec_smul]; rfl

lemma RawGraph.connection_expansion (r : RawGraph) (h : RawPositive r)
    (i j : I6) :
    connectionVec (r.metric h) (frameVec r.frameᵀ i) (frameVec r.frameᵀ j) =
      ∑ k, r.gamma i j k • frameVec r.frameᵀ k := by
  conv_lhs =>
    rw [r.vec_eq_sum_frame h
      (connectionVec (r.metric h) (frameVec r.frameᵀ i)
        (frameVec r.frameᵀ j))]
  simp only [r.connection_coordinate h]

lemma RawGraph.nested_connection_coordinate (r : RawGraph) (h : RawPositive r)
    (i j k n : I6) :
    (r.inverseTranspose *ᵥ
      connectionVec (r.metric h) (frameVec r.frameᵀ i)
        (connectionVec (r.metric h) (frameVec r.frameᵀ j)
          (frameVec r.frameᵀ k))) n =
      ∑ m, r.gamma j k m * r.gamma i m n := by
  rw [r.connection_expansion h j k]
  change coordinateLinear r.inverseTranspose n
      (connectionRight (r.metric h) (frameVec r.frameᵀ i)
        (∑ m, r.gamma j k m • frameVec r.frameᵀ m)) = _
  rw [map_sum]
  simp only [map_smul]
  change coordinateLinear r.inverseTranspose n
      (∑ m, r.gamma j k m •
        connectionVec (r.metric h) (frameVec r.frameᵀ i)
          (frameVec r.frameᵀ m)) = _
  rw [map_sum]
  simp [coordinateLinear, r.connection_coordinate h]

lemma RawGraph.bracket_expansion (r : RawGraph) (h : RawPositive r)
    (i j : I6) :
    bracket (frameVec r.frameᵀ i) (frameVec r.frameᵀ j) =
      ∑ m, r.bracketCoeff i j m • frameVec r.frameᵀ m := by
  conv_lhs =>
    rw [r.vec_eq_sum_frame h
      (bracket (frameVec r.frameᵀ i) (frameVec r.frameᵀ j))]
  rfl

lemma RawGraph.bracket_connection_coordinate (r : RawGraph) (h : RawPositive r)
    (i j k n : I6) :
    (r.inverseTranspose *ᵥ
      connectionVec (r.metric h)
        (bracket (frameVec r.frameᵀ i) (frameVec r.frameᵀ j))
        (frameVec r.frameᵀ k)) n =
      ∑ m, r.bracketCoeff i j m * r.gamma m k n := by
  rw [r.bracket_expansion h i j]
  change coordinateLinear r.inverseTranspose n
      (connectionLeft (r.metric h) (frameVec r.frameᵀ k)
        (∑ m, r.bracketCoeff i j m • frameVec r.frameᵀ m)) = _
  rw [map_sum]
  simp only [map_smul]
  change coordinateLinear r.inverseTranspose n
      (∑ m, r.bracketCoeff i j m •
        connectionVec (r.metric h) (frameVec r.frameᵀ m)
          (frameVec r.frameᵀ k)) = _
  rw [map_sum]
  simp [coordinateLinear, r.connection_coordinate h]

lemma RawGraph.curvature_coordinate (r : RawGraph) (h : RawPositive r)
    (i j k n : I6) :
    (r.inverseTranspose *ᵥ
      curvatureVec (r.metric h) (frameVec r.frameᵀ i)
        (frameVec r.frameᵀ j) (frameVec r.frameᵀ k)) n =
      r.curvatureCoeff i j k n := by
  simp only [curvatureVec, Matrix.mulVec_sub, Pi.sub_apply,
    r.nested_connection_coordinate h, r.bracket_connection_coordinate h,
    RawGraph.curvatureCoeff]

lemma RawGraph.ricciForm_eq (r : RawGraph) (h : RawPositive r) (j k : I6) :
    ricciForm (r.metric h) (frameVec r.frameᵀ j) (frameVec r.frameᵀ k) =
      r.ricciCoeff j k := by
  let V : Mat6 := r.frameᵀ
  let D : Mat6 := r.inverseTranspose
  let C : Mat6 := curvatureEndomorphism (r.metric h) (frameVec V j) (frameVec V k)
  have hVD : V * D = 1 := r.mul_inverseTranspose h
  have htrace : Matrix.trace C = Matrix.trace (D * C * V) := by
    symm
    rw [Matrix.trace_mul_cycle, hVD]
    simp
  rw [ricciForm]
  change Matrix.trace C = r.ricciCoeff j k
  rw [htrace]
  simp only [Matrix.trace, RawGraph.ricciCoeff]
  apply Finset.sum_congr rfl
  intro i _
  change (D * C * V) i i = r.curvatureCoeff i j k i
  rw [Matrix.mul_mul_apply]
  have hcol : Vᵀ i = frameVec V i := by funext n; simp [frameVec_apply]
  rw [hcol, curvatureEndomorphism_mulVec]
  change (D *ᵥ curvatureVec (r.metric h) (frameVec V i)
    (frameVec V j) (frameVec V k)) i = r.curvatureCoeff i j k i
  exact r.curvature_coordinate h i j k i

lemma RawGraph.ricciCoeff_of_Einstein (r : RawGraph) (h : RawPositive r)
    {lambda : ℝ} (hEin : ricci (r.metric h) = lambda • (r.metric h).gram)
    (j k : I6) :
    r.ricciCoeff j k = if j = k then lambda else 0 := by
  rw [← r.ricciForm_eq h, ricciForm_eq_matrix, hEin]
  rw [Matrix.smul_mulVec, dotProduct_smul]
  change lambda * metricInner (r.metric h) (frameVec r.frameᵀ j)
    (frameVec r.frameᵀ k) = _
  simp [RawGraph.metric, frameMetric_orthonormal]

noncomputable def RawGraph.residual (r : RawGraph) : Mat3 :=
  S3xS3.Trivial.Euler.residual r.P r.Q r.M

noncomputable def RawGraph.gradMExpr (r : RawGraph) : Mat3 :=
  -(r.M * lop' r.P) - dcof r.M (r.residual * r.P) + r.Q * r.residual

noncomputable def RawGraph.gradPExpr (r : RawGraph) : Mat3 :=
  r.P.trace • (1 : Mat3) - (2 : ℝ) • r.P -
      (r.Mᵀ * r.M).trace • r.P +
      (1 / 2 : ℝ) • (r.Mᵀ * r.M * r.P + r.P * (r.Mᵀ * r.M)) +
      dcof r.P (r.Mᵀ * r.M) -
      (1 / 2 : ℝ) •
        ((cofactor3 r.M)ᵀ * r.residual +
          ((cofactor3 r.M)ᵀ * r.residual)ᵀ)

noncomputable def RawGraph.gradQExpr (r : RawGraph) : Mat3 :=
  r.Q.trace • (1 : Mat3) - (2 : ℝ) • r.Q +
    (1 / 2 : ℝ) • (r.residual * r.Mᵀ + r.M * r.residualᵀ)

def otherJ : I3 → I3 := ![1, 0, 0]
def otherK : I3 → I3 := ![2, 2, 1]

set_option maxHeartbeats 1200000 in
lemma RawGraph.gradM00_ricci_certificate (r : RawGraph) (h : RawPositive r) :
    r.gradMExpr 0 0 = 2 * r.ricciCoeff (Sum.inr 0) (Sum.inl 0) := by
  simp [RawGraph.gradMExpr, RawGraph.residual,
    RawGraph.ricciCoeff, RawGraph.curvatureCoeff, RawGraph.gamma,
    RawGraph.bracketCoeff, RawGraph.inverseTranspose, RawGraph.Dinv,
    RawGraph.Einv, RawGraph.frame, graphFrame, RawGraph.D, RawGraph.E,
    RawGraph.P, RawGraph.Q, RawGraph.p, RawGraph.q,
    frameVec, basisVec, bracket, cross_apply, Matrix.mulVec, Matrix.vecMul,
    dotProduct,
    Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ,
    lop', dcof, cofactor3, S3xS3.Trivial.Euler.residual]
  field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
    ne_of_gt (h.d_pos 2), ne_of_gt (h.e_pos 0),
    ne_of_gt (h.e_pos 1), ne_of_gt (h.e_pos 2)]
  ring

set_option maxHeartbeats 10000000 in
lemma RawGraph.gradM_ricci_certificate (r : RawGraph) (h : RawPositive r)
    (i j : I3) :
    r.gradMExpr i j = 2 * r.ricciCoeff (Sum.inr i) (Sum.inl j) := by
  fin_cases i <;> fin_cases j <;>
    simp [RawGraph.gradMExpr, RawGraph.residual,
      RawGraph.ricciCoeff, RawGraph.curvatureCoeff, RawGraph.gamma,
      RawGraph.bracketCoeff, RawGraph.inverseTranspose, RawGraph.Dinv,
      RawGraph.Einv, RawGraph.frame, graphFrame, RawGraph.D, RawGraph.E,
      RawGraph.P, RawGraph.Q, RawGraph.p, RawGraph.q,
      frameVec, basisVec, bracket, cross_apply, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Matrix.mul_apply, Matrix.trace, Matrix.one_apply,
      Fin.sum_univ_succ,
      lop', dcof, cofactor3, S3xS3.Trivial.Euler.residual] <;>
    field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
      ne_of_gt (h.d_pos 2), ne_of_gt (h.e_pos 0),
      ne_of_gt (h.e_pos 1), ne_of_gt (h.e_pos 2)] <;>
    ring

set_option maxHeartbeats 2000000 in
lemma RawGraph.gradQ00_ricci_certificate (r : RawGraph) (h : RawPositive r) :
    r.gradQExpr 0 0 =
      (r.e 0 / (r.e 1 * r.e 2)) *
        (r.ricciCoeff (Sum.inr 1) (Sum.inr 1) +
          r.ricciCoeff (Sum.inr 2) (Sum.inr 2) -
          (∑ j, r.M 1 j * r.ricciCoeff (Sum.inr 1) (Sum.inl j)) -
          (∑ j, r.M 2 j * r.ricciCoeff (Sum.inr 2) (Sum.inl j))) := by
  simp [RawGraph.gradQExpr, RawGraph.residual,
    RawGraph.ricciCoeff, RawGraph.curvatureCoeff, RawGraph.gamma,
    RawGraph.bracketCoeff, RawGraph.inverseTranspose, RawGraph.Dinv,
    RawGraph.Einv, RawGraph.frame, graphFrame, RawGraph.D, RawGraph.E,
    RawGraph.P, RawGraph.Q, RawGraph.p, RawGraph.q,
    frameVec, basisVec, bracket, cross_apply, Matrix.mulVec, Matrix.vecMul,
    dotProduct, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ, cofactor3,
    S3xS3.Trivial.Euler.residual]
  field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
    ne_of_gt (h.d_pos 2), ne_of_gt (h.e_pos 0),
    ne_of_gt (h.e_pos 1), ne_of_gt (h.e_pos 2)]
  ring

set_option maxHeartbeats 3000000 in
lemma RawGraph.gradQ12_ricci_certificate (r : RawGraph) (h : RawPositive r) :
    r.gradQExpr 1 2 =
      (-r.q 0 / (r.e 2 * (r.e 1 + r.e 2))) *
          (r.ricciCoeff (Sum.inr 1) (Sum.inr 2) -
            ∑ t, r.M 2 t * r.ricciCoeff (Sum.inr 1) (Sum.inl t)) +
        (-r.q 0 / (r.e 1 * (r.e 1 + r.e 2))) *
          (r.ricciCoeff (Sum.inr 2) (Sum.inr 1) -
            ∑ t, r.M 1 t * r.ricciCoeff (Sum.inr 2) (Sum.inl t)) := by
  simp [RawGraph.gradQExpr, RawGraph.residual,
    RawGraph.ricciCoeff, RawGraph.curvatureCoeff, RawGraph.gamma,
    RawGraph.bracketCoeff, RawGraph.inverseTranspose, RawGraph.Dinv,
    RawGraph.Einv, RawGraph.frame, graphFrame, RawGraph.D, RawGraph.E,
    RawGraph.P, RawGraph.Q, RawGraph.p, RawGraph.q,
    frameVec, basisVec, bracket, cross_apply, Matrix.mulVec, Matrix.vecMul,
    dotProduct, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ, cofactor3,
    S3xS3.Trivial.Euler.residual]
  field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
    ne_of_gt (h.d_pos 2), ne_of_gt (h.e_pos 0),
    ne_of_gt (h.e_pos 1), ne_of_gt (h.e_pos 2),
    ne_of_gt (add_pos (h.e_pos 1) (h.e_pos 2))]
  ring

set_option maxHeartbeats 10000000 in
lemma RawGraph.gradQ_diag_ricci_certificate (r : RawGraph)
    (h : RawPositive r) (i : I3) :
    r.gradQExpr i i =
      (r.e i / (r.e (otherJ i) * r.e (otherK i))) *
        (r.ricciCoeff (Sum.inr (otherJ i)) (Sum.inr (otherJ i)) +
          r.ricciCoeff (Sum.inr (otherK i)) (Sum.inr (otherK i)) -
          (∑ t, r.M (otherJ i) t *
            r.ricciCoeff (Sum.inr (otherJ i)) (Sum.inl t)) -
          (∑ t, r.M (otherK i) t *
            r.ricciCoeff (Sum.inr (otherK i)) (Sum.inl t))) := by
  fin_cases i <;>
    simp [otherJ, otherK, RawGraph.gradQExpr, RawGraph.residual,
      RawGraph.ricciCoeff, RawGraph.curvatureCoeff, RawGraph.gamma,
      RawGraph.bracketCoeff, RawGraph.inverseTranspose, RawGraph.Dinv,
      RawGraph.Einv, RawGraph.frame, graphFrame, RawGraph.D, RawGraph.E,
      RawGraph.P, RawGraph.Q, RawGraph.p, RawGraph.q,
      frameVec, basisVec, bracket, cross_apply, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ, cofactor3,
      S3xS3.Trivial.Euler.residual] <;>
    field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
      ne_of_gt (h.d_pos 2), ne_of_gt (h.e_pos 0),
      ne_of_gt (h.e_pos 1), ne_of_gt (h.e_pos 2)] <;>
    ring

set_option maxHeartbeats 10000000 in
lemma RawGraph.gradQ_offdiag_ricci_certificate (r : RawGraph)
    (h : RawPositive r) (i : I3) :
    r.gradQExpr (otherJ i) (otherK i) =
      (-r.q i /
          (r.e (otherK i) * (r.e (otherJ i) + r.e (otherK i)))) *
          (r.ricciCoeff (Sum.inr (otherJ i)) (Sum.inr (otherK i)) -
            ∑ t, r.M (otherK i) t *
              r.ricciCoeff (Sum.inr (otherJ i)) (Sum.inl t)) +
        (-r.q i /
          (r.e (otherJ i) * (r.e (otherJ i) + r.e (otherK i)))) *
          (r.ricciCoeff (Sum.inr (otherK i)) (Sum.inr (otherJ i)) -
            ∑ t, r.M (otherJ i) t *
              r.ricciCoeff (Sum.inr (otherK i)) (Sum.inl t)) := by
  fin_cases i <;>
    simp [otherJ, otherK, RawGraph.gradQExpr, RawGraph.residual,
      RawGraph.ricciCoeff, RawGraph.curvatureCoeff, RawGraph.gamma,
      RawGraph.bracketCoeff, RawGraph.inverseTranspose, RawGraph.Dinv,
      RawGraph.Einv, RawGraph.frame, graphFrame, RawGraph.D, RawGraph.E,
      RawGraph.P, RawGraph.Q, RawGraph.p, RawGraph.q,
      frameVec, basisVec, bracket, cross_apply, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ, cofactor3,
      S3xS3.Trivial.Euler.residual] <;>
    field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
      ne_of_gt (h.d_pos 2), ne_of_gt (h.e_pos 0),
      ne_of_gt (h.e_pos 1), ne_of_gt (h.e_pos 2),
      ne_of_gt (add_pos (h.e_pos 0) (h.e_pos 1)),
      ne_of_gt (add_pos (h.e_pos 0) (h.e_pos 2)),
      ne_of_gt (add_pos (h.e_pos 1) (h.e_pos 2))] <;>
    ring

set_option maxHeartbeats 10000000 in
lemma RawGraph.gradP_diag_ricci_certificate (r : RawGraph)
    (h : RawPositive r) (i : I3) :
    r.gradPExpr i i =
      (r.d i / (r.d (otherJ i) * r.d (otherK i))) *
        (r.ricciCoeff (Sum.inl (otherJ i)) (Sum.inl (otherJ i)) +
          r.ricciCoeff (Sum.inl (otherK i)) (Sum.inl (otherK i)) +
          (∑ b, r.M b (otherJ i) *
            r.ricciCoeff (Sum.inr b) (Sum.inl (otherJ i))) +
          (∑ b, r.M b (otherK i) *
            r.ricciCoeff (Sum.inr b) (Sum.inl (otherK i)))) := by
  fin_cases i <;>
    simp [otherJ, otherK, RawGraph.gradPExpr, RawGraph.residual,
      RawGraph.ricciCoeff, RawGraph.curvatureCoeff, RawGraph.gamma,
      RawGraph.bracketCoeff, RawGraph.inverseTranspose, RawGraph.Dinv,
      RawGraph.Einv, RawGraph.frame, graphFrame, RawGraph.D, RawGraph.E,
      RawGraph.P, RawGraph.Q, RawGraph.p, RawGraph.q,
      frameVec, basisVec, bracket, cross_apply, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Matrix.mul_apply, Matrix.trace,
      Fin.sum_univ_succ, dcof, cofactor3,
      S3xS3.Trivial.Euler.residual] <;>
    field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
      ne_of_gt (h.d_pos 2), ne_of_gt (h.e_pos 0),
      ne_of_gt (h.e_pos 1), ne_of_gt (h.e_pos 2)] <;>
    ring

set_option maxHeartbeats 10000000 in
lemma RawGraph.gradP_offdiag_ricci_certificate (r : RawGraph)
    (h : RawPositive r) (i : I3) :
    r.gradPExpr (otherJ i) (otherK i) =
      (-r.p i /
          (r.d (otherK i) * (r.d (otherJ i) + r.d (otherK i)))) *
          (r.ricciCoeff (Sum.inl (otherJ i)) (Sum.inl (otherK i)) +
            ∑ b, r.M b (otherJ i) *
              r.ricciCoeff (Sum.inr b) (Sum.inl (otherK i))) +
        (-r.p i /
          (r.d (otherJ i) * (r.d (otherJ i) + r.d (otherK i)))) *
          (r.ricciCoeff (Sum.inl (otherK i)) (Sum.inl (otherJ i)) +
            ∑ b, r.M b (otherK i) *
              r.ricciCoeff (Sum.inr b) (Sum.inl (otherJ i))) := by
  fin_cases i <;>
    simp [otherJ, otherK, RawGraph.gradPExpr, RawGraph.residual,
      RawGraph.ricciCoeff, RawGraph.curvatureCoeff, RawGraph.gamma,
      RawGraph.bracketCoeff, RawGraph.inverseTranspose, RawGraph.Dinv,
      RawGraph.Einv, RawGraph.frame, graphFrame, RawGraph.D, RawGraph.E,
      RawGraph.P, RawGraph.Q, RawGraph.p, RawGraph.q,
      frameVec, basisVec, bracket, cross_apply, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Matrix.mul_apply, Matrix.trace,
      Fin.sum_univ_succ, dcof, cofactor3,
      S3xS3.Trivial.Euler.residual] <;>
    field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
      ne_of_gt (h.d_pos 2), ne_of_gt (h.e_pos 0),
      ne_of_gt (h.e_pos 1), ne_of_gt (h.e_pos 2),
      ne_of_gt (add_pos (h.d_pos 0) (h.d_pos 1)),
      ne_of_gt (add_pos (h.d_pos 0) (h.d_pos 2)),
      ne_of_gt (add_pos (h.d_pos 1) (h.d_pos 2))] <;>
    ring

lemma RawGraph.gradPExpr_symmetric (r : RawGraph) :
    r.gradPExprᵀ = r.gradPExpr := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RawGraph.gradPExpr, RawGraph.residual, RawGraph.P, RawGraph.Q,
      RawGraph.p, RawGraph.q, Matrix.mul_apply, Matrix.trace,
      Fin.sum_univ_succ, dcof, cofactor3,
      S3xS3.Trivial.Euler.residual] <;>
    ring

lemma RawGraph.gradQExpr_symmetric (r : RawGraph) :
    r.gradQExprᵀ = r.gradQExpr := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RawGraph.gradQExpr, RawGraph.residual, RawGraph.P, RawGraph.Q,
      RawGraph.p, RawGraph.q, Matrix.mul_apply, Matrix.trace,
      Fin.sum_univ_succ, cofactor3,
      S3xS3.Trivial.Euler.residual] <;>
    ring

lemma RawGraph.gradM_eq_zero_of_Einstein (r : RawGraph) (h : RawPositive r)
    {lambda : ℝ} (hEin : ricci (r.metric h) = lambda • (r.metric h).gram) :
    r.gradMExpr = 0 := by
  ext i j
  rw [r.gradM_ricci_certificate h i j,
    r.ricciCoeff_of_Einstein h hEin]
  simp

lemma RawGraph.gradQ_diag_of_Einstein (r : RawGraph) (h : RawPositive r)
    {lambda : ℝ} (hEin : ricci (r.metric h) = lambda • (r.metric h).gram)
    (i : I3) :
    r.gradQExpr i i = (2 * lambda) * (r.q i)⁻¹ := by
  rw [r.gradQ_diag_ricci_certificate h i]
  simp_rw [r.ricciCoeff_of_Einstein h hEin]
  fin_cases i <;>
    simp [otherJ, otherK, RawGraph.q] <;>
    field_simp [ne_of_gt (h.e_pos 0), ne_of_gt (h.e_pos 1),
      ne_of_gt (h.e_pos 2)] <;>
    ring

lemma RawGraph.gradQ_offdiag_of_Einstein (r : RawGraph) (h : RawPositive r)
    {lambda : ℝ} (hEin : ricci (r.metric h) = lambda • (r.metric h).gram)
    (i : I3) :
    r.gradQExpr (otherJ i) (otherK i) = 0 := by
  rw [r.gradQ_offdiag_ricci_certificate h i]
  simp_rw [r.ricciCoeff_of_Einstein h hEin]
  fin_cases i <;> simp [otherJ, otherK]

lemma RawGraph.gradP_diag_of_Einstein (r : RawGraph) (h : RawPositive r)
    {lambda : ℝ} (hEin : ricci (r.metric h) = lambda • (r.metric h).gram)
    (i : I3) :
    r.gradPExpr i i = (2 * lambda) * (r.p i)⁻¹ := by
  rw [r.gradP_diag_ricci_certificate h i]
  simp_rw [r.ricciCoeff_of_Einstein h hEin]
  fin_cases i <;>
    simp [otherJ, otherK, RawGraph.p] <;>
    field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
      ne_of_gt (h.d_pos 2)] <;>
    ring

lemma RawGraph.gradP_offdiag_of_Einstein (r : RawGraph) (h : RawPositive r)
    {lambda : ℝ} (hEin : ricci (r.metric h) = lambda • (r.metric h).gram)
    (i : I3) :
    r.gradPExpr (otherJ i) (otherK i) = 0 := by
  rw [r.gradP_offdiag_ricci_certificate h i]
  simp_rw [r.ricciCoeff_of_Einstein h hEin]
  fin_cases i <;> simp [otherJ, otherK]

lemma RawGraph.Q_inv_apply (r : RawGraph) (h : RawPositive r) (i j : I3) :
    r.Q⁻¹ i j = if i = j then (r.q i)⁻¹ else 0 := by
  rw [RawGraph.Q, Matrix.inv_diagonal]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, if_pos]
    have hqunit : IsUnit r.q := Pi.isUnit_iff.mpr fun k ↦
      isUnit_iff_ne_zero.mpr (ne_of_gt (h.q_pos k))
    have hc := congrFun (Ring.inverse_mul_cancel r.q hqunit) i
    change Ring.inverse r.q i * r.q i = 1 at hc
    apply mul_right_cancel₀ (ne_of_gt (h.q_pos i))
    rw [hc, inv_mul_cancel₀ (ne_of_gt (h.q_pos i))]
  · simp [Matrix.diagonal, hij]

lemma RawGraph.P_inv_apply (r : RawGraph) (h : RawPositive r) (i j : I3) :
    r.P⁻¹ i j = if i = j then (r.p i)⁻¹ else 0 := by
  rw [RawGraph.P, Matrix.inv_diagonal]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, if_pos]
    have hpunit : IsUnit r.p := Pi.isUnit_iff.mpr fun k ↦
      isUnit_iff_ne_zero.mpr (ne_of_gt (h.p_pos k))
    have hc := congrFun (Ring.inverse_mul_cancel r.p hpunit) i
    change Ring.inverse r.p i * r.p i = 1 at hc
    apply mul_right_cancel₀ (ne_of_gt (h.p_pos i))
    rw [hc, inv_mul_cancel₀ (ne_of_gt (h.p_pos i))]
  · simp [Matrix.diagonal, hij]

lemma RawGraph.gradQ_eq_of_Einstein (r : RawGraph) (h : RawPositive r)
    {lambda : ℝ} (hEin : ricci (r.metric h) = lambda • (r.metric h).gram) :
    r.gradQExpr = (2 * lambda) • r.Q⁻¹ := by
  have hs := r.gradQExpr_symmetric
  have hdiag := r.gradQ_diag_of_Einstein h hEin
  have hoff := r.gradQ_offdiag_of_Einstein h hEin
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [r.Q_inv_apply h] using hdiag 0
  · simpa [otherJ, otherK, r.Q_inv_apply h] using hoff 2
  · simpa [otherJ, otherK, r.Q_inv_apply h] using hoff 1
  · have ht := congrFun (congrFun hs 0) 1
    simpa [otherJ, otherK, r.Q_inv_apply h] using
      (ht.trans (hoff 2))
  · simpa [r.Q_inv_apply h] using hdiag 1
  · simpa [otherJ, otherK, r.Q_inv_apply h] using hoff 0
  · have ht := congrFun (congrFun hs 0) 2
    simpa [otherJ, otherK, r.Q_inv_apply h] using
      (ht.trans (hoff 1))
  · have ht := congrFun (congrFun hs 1) 2
    simpa [otherJ, otherK, r.Q_inv_apply h] using
      (ht.trans (hoff 0))
  · simpa [r.Q_inv_apply h] using hdiag 2

lemma RawGraph.gradP_eq_of_Einstein (r : RawGraph) (h : RawPositive r)
    {lambda : ℝ} (hEin : ricci (r.metric h) = lambda • (r.metric h).gram) :
    r.gradPExpr = (2 * lambda) • r.P⁻¹ := by
  have hs := r.gradPExpr_symmetric
  have hdiag := r.gradP_diag_of_Einstein h hEin
  have hoff := r.gradP_offdiag_of_Einstein h hEin
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [r.P_inv_apply h] using hdiag 0
  · simpa [otherJ, otherK, r.P_inv_apply h] using hoff 2
  · simpa [otherJ, otherK, r.P_inv_apply h] using hoff 1
  · have ht := congrFun (congrFun hs 0) 1
    simpa [otherJ, otherK, r.P_inv_apply h] using
      (ht.trans (hoff 2))
  · simpa [r.P_inv_apply h] using hdiag 1
  · simpa [otherJ, otherK, r.P_inv_apply h] using hoff 0
  · have ht := congrFun (congrFun hs 0) 2
    simpa [otherJ, otherK, r.P_inv_apply h] using
      (ht.trans (hoff 1))
  · have ht := congrFun (congrFun hs 1) 2
    simpa [otherJ, otherK, r.P_inv_apply h] using
      (ht.trans (hoff 0))
  · simpa [r.P_inv_apply h] using hdiag 2

end S3xS3.Trivial.EinsteinBridge
