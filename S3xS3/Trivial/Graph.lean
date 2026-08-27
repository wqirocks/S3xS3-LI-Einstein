import S3xS3.Naturality

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.Graph

lemma transpose_mul_cofactor3 (A : Mat3) :
    Aᵀ * cofactor3 A = A.det • (1 : Mat3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactor3, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.det_fin_three] <;> ring

lemma det_cofactor3 (A : Mat3) : (cofactor3 A).det = A.det ^ 2 := by
  simp [cofactor3, Matrix.det_fin_three]
  ring

lemma cofactor3_smul (c : ℝ) (A : Mat3) :
    cofactor3 (c • A) = c ^ 2 • cofactor3 A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cofactor3] <;> ring

lemma cofactor3_transpose (A : Mat3) :
    cofactor3 Aᵀ = (cofactor3 A)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cofactor3] <;> ring

set_option maxHeartbeats 800000 in
lemma cofactor3_mul (A B : Mat3) :
    cofactor3 (A * B) = cofactor3 A * cofactor3 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactor3, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

lemma cofactor3_so3_conjugate (U : SO3) (A : Mat3) :
    cofactor3 ((U : Mat3)ᵀ * A * U) =
      (U : Mat3)ᵀ * cofactor3 A * U := by
  rw [cofactor3_mul, cofactor3_mul, cofactor3_transpose,
    cofactor3_eq_of_mem_SO3]

noncomputable def invCof (C : Mat3) : Mat3 :=
  Real.sqrt C.det • C⁻¹

lemma invCof_posDef {C : Mat3} (hC : C.PosDef) : (invCof C).PosDef := by
  apply hC.inv.smul
  exact Real.sqrt_pos.2 hC.det_pos

lemma det_invCof {C : Mat3} (hC : C.PosDef) :
    (invCof C).det = Real.sqrt C.det := by
  have hdet : 0 < C.det := hC.det_pos
  have hs : 0 < Real.sqrt C.det := Real.sqrt_pos.2 hdet
  have hs2 : (Real.sqrt C.det) ^ 2 = C.det := Real.sq_sqrt hdet.le
  rw [invCof, Matrix.det_smul, Matrix.det_nonsing_inv]
  simp only [Fintype.card_fin]
  rw [Ring.inverse_eq_inv]
  field_simp [ne_of_gt hdet]
  nlinarith [hs2]

lemma cofactor3_invCof {C : Mat3} (hC : C.PosDef) :
    cofactor3 (invCof C) = C := by
  let P := invCof C
  have hP : P.PosDef := invCof_posDef hC
  have hdetP : P.det = Real.sqrt C.det := det_invCof hC
  have hs : Real.sqrt C.det ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hC.det_pos)
  have hCunit : IsUnit C.det := isUnit_iff_ne_zero.mpr (ne_of_gt hC.det_pos)
  have hPinv : IsUnit P := hP.isUnit
  have hPtinv : IsUnit Pᵀ := (Matrix.isUnit_transpose P).2 hPinv
  apply hPtinv.mul_right_cancel
  rw [cofactor3_mul_transpose]
  change P.det • (1 : Mat3) = C * Pᵀ
  rw [hdetP]
  change Real.sqrt C.det • (1 : Mat3) =
    C * (Real.sqrt C.det • C⁻¹)ᵀ
  have hCt : Cᵀ = C := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hC.isHermitian.eq
  rw [Matrix.transpose_smul, Matrix.transpose_nonsing_inv, hCt]
  rw [Matrix.mul_smul, C.mul_nonsing_inv hCunit]

noncomputable def pdSqrt (A : Mat3) : Mat3 := CFC.sqrt A

lemma pdSqrt_posDef {A : Mat3} (hA : A.PosDef) : (pdSqrt A).PosDef := by
  have hspsd : (CFC.sqrt A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  apply hspsd.posDef_iff_isUnit.mpr
  exact (CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt
    (a := A)).mp hA.isStrictlyPositive |>.1

lemma pdSqrt_sq {A : Mat3} (hA : A.PosDef) :
    pdSqrt A * pdSqrt A = A := by
  exact CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg

lemma pdSqrt_transpose {A : Mat3} (hA : A.PosDef) :
    (pdSqrt A)ᵀ = pdSqrt A := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (pdSqrt_posDef hA).isHermitian.eq

lemma block22_posDef {K : Mat6} (hK : K.PosDef) : K.toBlocks₂₂.PosDef := by
  exact hK.submatrix Sum.inr_injective

lemma block11_posDef {K : Mat6} (hK : K.PosDef) : K.toBlocks₁₁.PosDef := by
  exact hK.submatrix Sum.inl_injective

lemma block21_eq_transpose_block12 {K : Mat6} (hK : K.IsHermitian) :
    K.toBlocks₂₁ = K.toBlocks₁₂ᵀ := by
  ext i j
  have hij := congrFun (congrFun hK.eq (Sum.inl j)) (Sum.inr i)
  simpa [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hij

theorem schur_posDef {K : Mat6} (hK : K.PosDef) :
    (K.toBlocks₁₁ - K.toBlocks₁₂ * K.toBlocks₂₂⁻¹ *
      K.toBlocks₁₂ᵀ).PosDef := by
  let A : Mat3 := K.toBlocks₁₁
  let B : Mat3 := K.toBlocks₁₂
  let D : Mat3 := K.toBlocks₂₂
  have hD : D.PosDef := block22_posDef hK
  letI : Invertible D := hD.isUnit.invertible
  have hform : K = Matrix.fromBlocks A B Bᴴ D := by
    rw [← Matrix.fromBlocks_toBlocks K]
    congr 1
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      block21_eq_transpose_block12 hK.isHermitian
  have hA : A.PosDef := block11_posDef hK
  have hterm : (B * D⁻¹ * Bᴴ).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose B hD.isHermitian.inv
  have hSsym : (A - B * D⁻¹ * Bᴴ).IsHermitian :=
    hA.isHermitian.sub hterm
  have hS : (A - B * D⁻¹ * Bᴴ).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hSsym
    intro x hx
    let y : I3 → ℝ := -((D⁻¹ * Bᴴ) *ᵥ x)
    have hxy : Sum.elim x y ≠ 0 := by
      intro hz
      apply hx
      funext i
      have hi := congrFun hz (Sum.inl i)
      exact hi
    have hp := hK.dotProduct_mulVec_pos hxy
    rw [hform] at hp
    rw [Matrix.dotProduct_mulVec,
      Matrix.schur_complement_eq₂₂ A B x y hD.isHermitian] at hp
    rw [Matrix.dotProduct_mulVec]
    simpa [y, Matrix.conjTranspose_eq_transpose_of_trivial] using hp
  simpa [A, B, D, Matrix.conjTranspose_eq_transpose_of_trivial] using hS

def graphFrame (D E M : Mat3) : Mat6 :=
  Matrix.fromBlocks D 0 (M * D) E

structure GraphData (g : LeftInvariantMetric) where
  P : Mat3
  Q : Mat3
  M : Mat3
  D : Mat3
  E : Mat3
  P_pos : P.PosDef
  Q_pos : Q.PosDef
  D_pos : D.PosDef
  E_pos : E.PosDef
  D_sq : D * D = cofactor3 P
  E_sq : E * E = cofactor3 Q
  cometric_eq : g.gram⁻¹ = (graphFrame D E M)ᵀ * graphFrame D E M

lemma graphFrame_det_ne_zero {D E M : Mat3}
    (hD : D.PosDef) (hE : E.PosDef) : (graphFrame D E M).det ≠ 0 := by
  rw [graphFrame, Matrix.det_fromBlocks_zero₁₂]
  exact mul_ne_zero (ne_of_gt hD.det_pos) (ne_of_gt hE.det_pos)

lemma GraphData.metric_eq (d : GraphData g) :
    g = metricOfFrame (graphFrame d.D d.E d.M)
      (graphFrame_det_ne_zero d.D_pos d.E_pos) := by
  apply LeftInvariantMetric.ext_of_inv_eq
  rw [metricOfFrame_gram_inv]
  exact d.cometric_eq

noncomputable def canonicalGraphData (g : LeftInvariantMetric) : GraphData g := by
  let K : Mat6 := g.gram⁻¹
  have hK : K.PosDef := g.posDef.inv
  let K11 : Mat3 := K.toBlocks₁₁
  let K12 : Mat3 := K.toBlocks₁₂
  let K21 : Mat3 := K.toBlocks₂₁
  let K22 : Mat3 := K.toBlocks₂₂
  have hK22 : K22.PosDef := block22_posDef hK
  let S : Mat3 := K11 - K12 * K22⁻¹ * K12ᵀ
  have hS : S.PosDef := by simpa [S, K11, K12, K22] using schur_posDef hK
  let E : Mat3 := pdSqrt K22
  let D : Mat3 := pdSqrt S
  have hE : E.PosDef := pdSqrt_posDef hK22
  have hD : D.PosDef := pdSqrt_posDef hS
  let W : Mat3 := E⁻¹ * K21
  let M : Mat3 := W * D⁻¹
  let CP : Mat3 := D * D
  let CQ : Mat3 := E * E
  have hCP : CP.PosDef := by
    change (D * D).PosDef
    rw [show D * D = S by simpa [D] using pdSqrt_sq hS]
    exact hS
  have hCQ : CQ.PosDef := by
    change (E * E).PosDef
    rw [show E * E = K22 by simpa [E] using pdSqrt_sq hK22]
    exact hK22
  let P : Mat3 := invCof CP
  let Q : Mat3 := invCof CQ
  have hP : P.PosDef := invCof_posDef hCP
  have hQ : Q.PosDef := invCof_posDef hCQ
  refine
    { P := P, Q := Q, M := M, D := D, E := E
      P_pos := hP, Q_pos := hQ, D_pos := hD, E_pos := hE
      D_sq := ?_, E_sq := ?_, cometric_eq := ?_ }
  · exact (cofactor3_invCof hCP).symm
  · exact (cofactor3_invCof hCQ).symm
  · change K = (graphFrame D E M)ᵀ * graphFrame D E M
    have hKsym : K21 = K12ᵀ := by
      simpa [K21, K12] using block21_eq_transpose_block12 hK.isHermitian
    have hEsq : E * E = K22 := pdSqrt_sq hK22
    have hDsq : D * D = S := pdSqrt_sq hS
    have hEt : Eᵀ = E := pdSqrt_transpose hK22
    have hDt : Dᵀ = D := pdSqrt_transpose hS
    have hEu : IsUnit E := hE.isUnit
    have hDu : IsUnit D := hD.isUnit
    have hEdetu : IsUnit E.det := (Matrix.isUnit_iff_isUnit_det E).mp hEu
    have hDdetu : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDu
    have hK22u : IsUnit K22 := hK22.isUnit
    have hED : W * D⁻¹ * D = W := by
      rw [Matrix.mul_assoc, D.nonsing_inv_mul hDdetu]
      simp
    have hEW : E * W = K21 := by
      change E * (E⁻¹ * K21) = K21
      rw [← Matrix.mul_assoc, E.mul_nonsing_inv hEdetu]
      simp
    have hWtE : Wᵀ * E = K12 := by
      rw [← hEt, ← Matrix.transpose_mul, hEW, hKsym,
        Matrix.transpose_transpose]
    have hWtW : Wᵀ * W = K12 * K22⁻¹ * K12ᵀ := by
      change (E⁻¹ * K21)ᵀ * (E⁻¹ * K21) = _
      rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hEt, hKsym]
      have hEinvSq : E⁻¹ * E⁻¹ = K22⁻¹ := by
        rw [← Matrix.mul_inv_rev, hEsq]
      rw [Matrix.transpose_transpose]
      calc
        (K12 * E⁻¹) * (E⁻¹ * K12ᵀ) =
            K12 * (E⁻¹ * E⁻¹) * K12ᵀ := by noncomm_ring
        _ = _ := by rw [hEinvSq]
    rw [← Matrix.fromBlocks_toBlocks K]
    rw [graphFrame, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply]
    apply Matrix.fromBlocks_inj.mpr
    constructor
    · change K11 = Dᵀ * D + (M * D)ᵀ * (M * D)
      rw [hDt, show M * D = W by exact hED, hDsq, hWtW]
      dsimp [S]
      abel
    constructor
    · change K12 = Dᵀ * 0 + (M * D)ᵀ * E
      simp [show M * D = W by exact hED, hWtE]
    constructor
    · change K21 = 0ᵀ * D + Eᵀ * (M * D)
      simp [hEt, show M * D = W by exact hED, hEW]
    · change K22 = 0ᵀ * 0 + Eᵀ * E
      simp [hEt, hEsq]

lemma so3_mul_transpose (U : SO3) :
    (U : Mat3) * (U : Mat3)ᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff I3 ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1

lemma so3_transpose_mul (U : SO3) :
    (U : Mat3)ᵀ * (U : Mat3) = 1 :=
  (Matrix.mem_orthogonalGroup_iff' I3 ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1

lemma posDef_conjugate_so3 {A : Mat3} (hA : A.PosDef) (U : SO3) :
    ((U : Mat3)ᵀ * A * U).PosDef := by
  have hunit : IsUnit (U : Mat3) :=
    IsUnit.of_mul_eq_one (U : Mat3)ᵀ (so3_mul_transpose U)
  have hinj : Function.Injective (U : Mat3).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hA.conjTranspose_mul_mul_same hinj

lemma posDef_sqrt_unique {A B : Mat3} (hA : A.PosDef) (hB : B.PosDef)
    (hsq : A * A = B * B) : A = B := by
  exact (CFC.mul_self_eq_mul_self_iff A B
    hA.posSemidef.nonneg hB.posSemidef.nonneg).mp hsq

lemma GraphData.conjugates_D (d : GraphData g) (U : SO3)
    (hP : (U : Mat3)ᵀ * d.P * U = d.P) :
    (U : Mat3)ᵀ * d.D * U = d.D := by
  let DU : Mat3 := (U : Mat3)ᵀ * d.D * U
  have hDU : DU.PosDef := posDef_conjugate_so3 d.D_pos U
  apply posDef_sqrt_unique hDU d.D_pos
  change ((U : Mat3)ᵀ * d.D * U) * ((U : Mat3)ᵀ * d.D * U) =
    d.D * d.D
  calc
    ((U : Mat3)ᵀ * d.D * U) * ((U : Mat3)ᵀ * d.D * U) =
        (U : Mat3)ᵀ * (d.D * d.D) * U := by
      calc
        _ = (U : Mat3)ᵀ * d.D *
            ((U : Mat3) * (U : Mat3)ᵀ) * d.D * U := by noncomm_ring
        _ = _ := by rw [so3_mul_transpose]; simp; noncomm_ring
    _ = (U : Mat3)ᵀ * cofactor3 d.P * U := by rw [d.D_sq]
    _ = cofactor3 ((U : Mat3)ᵀ * d.P * U) := by
      rw [cofactor3_so3_conjugate]
    _ = d.D * d.D := by rw [hP, ← d.D_sq]

lemma GraphData.conjugates_E (d : GraphData g) (V : SO3)
    (hQ : (V : Mat3)ᵀ * d.Q * V = d.Q) :
    (V : Mat3)ᵀ * d.E * V = d.E := by
  let EV : Mat3 := (V : Mat3)ᵀ * d.E * V
  have hEV : EV.PosDef := posDef_conjugate_so3 d.E_pos V
  apply posDef_sqrt_unique hEV d.E_pos
  change ((V : Mat3)ᵀ * d.E * V) * ((V : Mat3)ᵀ * d.E * V) =
    d.E * d.E
  calc
    ((V : Mat3)ᵀ * d.E * V) * ((V : Mat3)ᵀ * d.E * V) =
        (V : Mat3)ᵀ * (d.E * d.E) * V := by
      calc
        _ = (V : Mat3)ᵀ * d.E *
            ((V : Mat3) * (V : Mat3)ᵀ) * d.E * V := by noncomm_ring
        _ = _ := by rw [so3_mul_transpose]; simp; noncomm_ring
    _ = (V : Mat3)ᵀ * cofactor3 d.Q * V := by rw [d.E_sq]
    _ = cofactor3 ((V : Mat3)ᵀ * d.Q * V) := by
      rw [cofactor3_so3_conjugate]
    _ = d.E * d.E := by rw [hQ, ← d.E_sq]

lemma graphFrame_conjugate (D E M : Mat3) (U V : SO3) :
    Matrix.fromBlocks (U : Mat3)ᵀ 0 0 (V : Mat3)ᵀ *
        graphFrame D E M *
        Matrix.fromBlocks (U : Mat3) 0 0 (V : Mat3) =
      graphFrame ((U : Mat3)ᵀ * D * U) ((V : Mat3)ᵀ * E * V)
        ((V : Mat3)ᵀ * M * U) := by
  rw [graphFrame, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  apply Matrix.fromBlocks_inj.mpr
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
    calc
      (V : Mat3)ᵀ * (M * D) * U =
          (V : Mat3)ᵀ * M *
            ((U : Mat3) * (U : Mat3)ᵀ) * D * U := by
        rw [so3_mul_transpose]
        simp
        noncomm_ring
      _ = ((V : Mat3)ᵀ * M * U) *
          ((U : Mat3)ᵀ * D * U) := by noncomm_ring
  · simp

lemma GraphData.fixes_of_stabilizes (d : GraphData g) (U V : SO3)
    (hP : (U : Mat3)ᵀ * d.P * U = d.P)
    (hQ : (V : Mat3)ᵀ * d.Q * V = d.Q)
    (hM : (V : Mat3)ᵀ * d.M * U = d.M) :
    Fixes (U, V) g := by
  let A : Mat6 := graphFrame d.D d.E d.M
  let T : Mat6 := innerMatrix (U, V)
  have hAt : Tᵀ * A * T = A := by
    dsimp [T, innerMatrix]
    rw [Matrix.fromBlocks_transpose]
    simp only [Matrix.transpose_zero]
    rw [show A = graphFrame d.D d.E d.M by rfl,
      graphFrame_conjugate]
    rw [d.conjugates_D U hP, d.conjugates_E V hQ, hM]
  have hTT : Tᵀ * T = 1 := innerMatrix_transpose_mul (U, V)
  have hTT' : T * Tᵀ = 1 := innerMatrix_mul_transpose (U, V)
  have hcometric : Tᵀ * (Aᵀ * A) * T = Aᵀ * A := by
    have hAT : A * T = T * A := by
      calc
        A * T = (T * Tᵀ) * A * T := by rw [hTT']; simp
        _ = T * (Tᵀ * A * T) := by noncomm_ring
        _ = T * A := by rw [hAt]
    calc
      Tᵀ * (Aᵀ * A) * T = (A * T)ᵀ * (A * T) := by
        rw [Matrix.transpose_mul]
        noncomm_ring
      _ = (T * A)ᵀ * (T * A) := by rw [hAT]
      _ = Aᵀ * (Tᵀ * T) * A := by
        rw [Matrix.transpose_mul]
        noncomm_ring
      _ = Aᵀ * A := by rw [hTT]; simp
  rw [d.metric_eq]
  exact fixes_metricOfFrame_of_fixes_cometric (U, V) A
    (graphFrame_det_ne_zero d.D_pos d.E_pos) hcometric

noncomputable def GraphData.pullback (d : GraphData g) (U V : SO3) :
    GraphData (pullbackMetric (U, V) g) := by
  let P' : Mat3 := (U : Mat3)ᵀ * d.P * U
  let Q' : Mat3 := (V : Mat3)ᵀ * d.Q * V
  let M' : Mat3 := (V : Mat3)ᵀ * d.M * U
  let D' : Mat3 := (U : Mat3)ᵀ * d.D * U
  let E' : Mat3 := (V : Mat3)ᵀ * d.E * V
  have hP' : P'.PosDef := posDef_conjugate_so3 d.P_pos U
  have hQ' : Q'.PosDef := posDef_conjugate_so3 d.Q_pos V
  have hD' : D'.PosDef := posDef_conjugate_so3 d.D_pos U
  have hE' : E'.PosDef := posDef_conjugate_so3 d.E_pos V
  refine
    { P := P', Q := Q', M := M', D := D', E := E'
      P_pos := hP', Q_pos := hQ', D_pos := hD', E_pos := hE'
      D_sq := ?_, E_sq := ?_, cometric_eq := ?_ }
  · change ((U : Mat3)ᵀ * d.D * U) * ((U : Mat3)ᵀ * d.D * U) =
      cofactor3 ((U : Mat3)ᵀ * d.P * U)
    calc
      ((U : Mat3)ᵀ * d.D * U) * ((U : Mat3)ᵀ * d.D * U) =
          (U : Mat3)ᵀ * (d.D * d.D) * U := by
        calc
          _ = (U : Mat3)ᵀ * d.D *
              ((U : Mat3) * (U : Mat3)ᵀ) * d.D * U := by noncomm_ring
          _ = _ := by rw [so3_mul_transpose]; simp; noncomm_ring
      _ = (U : Mat3)ᵀ * cofactor3 d.P * U := by rw [d.D_sq]
      _ = _ := (cofactor3_so3_conjugate U d.P).symm
  · change ((V : Mat3)ᵀ * d.E * V) * ((V : Mat3)ᵀ * d.E * V) =
      cofactor3 ((V : Mat3)ᵀ * d.Q * V)
    calc
      ((V : Mat3)ᵀ * d.E * V) * ((V : Mat3)ᵀ * d.E * V) =
          (V : Mat3)ᵀ * (d.E * d.E) * V := by
        calc
          _ = (V : Mat3)ᵀ * d.E *
              ((V : Mat3) * (V : Mat3)ᵀ) * d.E * V := by noncomm_ring
          _ = _ := by rw [so3_mul_transpose]; simp; noncomm_ring
      _ = (V : Mat3)ᵀ * cofactor3 d.Q * V := by rw [d.E_sq]
      _ = _ := (cofactor3_so3_conjugate V d.Q).symm
  · let A : Mat6 := graphFrame d.D d.E d.M
    let A' : Mat6 := graphFrame D' E' M'
    let T : Mat6 := innerMatrix (U, V)
    have hA' : A' = Tᵀ * A * T := by
      dsimp [A', D', E', M', T, innerMatrix]
      rw [Matrix.fromBlocks_transpose]
      simp only [Matrix.transpose_zero]
      exact (graphFrame_conjugate d.D d.E d.M U V).symm
    have hTT' : T * Tᵀ = 1 := innerMatrix_mul_transpose (U, V)
    rw [pullbackMetric_gram_inv, d.cometric_eq]
    change Tᵀ * (Aᵀ * A) * T = A'ᵀ * A'
    rw [hA', Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    calc
      Tᵀ * (Aᵀ * A) * T =
          Tᵀ * Aᵀ * (T * Tᵀ) * A * T := by rw [hTT']; simp; noncomm_ring
      _ = Tᵀ * (Aᵀ * T) * (Tᵀ * A * T) := by
        noncomm_ring

def orientationCorrection (W : Mat3) : Mat3 :=
  Matrix.diagonal ![W.det, (1 : ℝ), (1 : ℝ)]

def orientedMatrix (W : Mat3) : Mat3 := W * orientationCorrection W

lemma det_sq_of_transpose_mul_eq_one {W : Mat3} (hW : Wᵀ * W = 1) :
    W.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hW
  rw [Matrix.det_mul, Matrix.det_transpose] at h
  simpa [pow_two] using h

lemma orientationCorrection_transpose (W : Mat3) :
    (orientationCorrection W)ᵀ = orientationCorrection W := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [orientationCorrection]

lemma orientationCorrection_sq {W : Mat3} (hW : Wᵀ * W = 1) :
    orientationCorrection W * orientationCorrection W = 1 := by
  have hd := det_sq_of_transpose_mul_eq_one hW
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orientationCorrection, Matrix.mul_apply, Fin.sum_univ_succ] ;
    nlinarith

lemma orientedMatrix_transpose_mul {W : Mat3} (hW : Wᵀ * W = 1) :
    (orientedMatrix W)ᵀ * orientedMatrix W = 1 := by
  rw [orientedMatrix, Matrix.transpose_mul, orientationCorrection_transpose]
  calc
    orientationCorrection W * Wᵀ * (W * orientationCorrection W) =
        orientationCorrection W * (Wᵀ * W) * orientationCorrection W := by
      noncomm_ring
    _ = 1 := by rw [hW]; simpa using orientationCorrection_sq hW

lemma orientedMatrix_det {W : Mat3} (hW : Wᵀ * W = 1) :
    (orientedMatrix W).det = 1 := by
  have hd := det_sq_of_transpose_mul_eq_one hW
  rw [orientedMatrix, Matrix.det_mul]
  have hc : (orientationCorrection W).det = W.det := by
    rw [orientationCorrection, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ]
  rw [hc]
  simpa [pow_two] using hd

def orientedSO3 (W : Mat3) (hW : Wᵀ * W = 1) : SO3 :=
  ⟨orientedMatrix W, (Matrix.mem_specialOrthogonalGroup_iff).2
    ⟨(Matrix.mem_orthogonalGroup_iff' I3 ℝ).2
      (orientedMatrix_transpose_mul hW), orientedMatrix_det hW⟩⟩

lemma correction_preserves_diagonal (W : Mat3) (s : I3 → ℝ)
    (hW : Wᵀ * W = 1) :
    (orientationCorrection W)ᵀ * Matrix.diagonal s * orientationCorrection W =
      Matrix.diagonal s := by
  have hd := det_sq_of_transpose_mul_eq_one hW
  rw [orientationCorrection_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orientationCorrection, Matrix.mul_apply, Fin.sum_univ_succ]
  calc
    W.det * s 0 * W.det = W.det ^ 2 * s 0 := by ring
    _ = s 0 := by rw [hd]; ring

theorem diagonalize_posDef_three {N : Mat3} (hN : N.PosDef) :
    ∃ q : SO3, ∃ s : I3 → ℝ, (∀ i, 0 < s i) ∧
      (q : Mat3)ᵀ * N * q = Matrix.diagonal s := by
  let U : Mat3 := hN.isHermitian.eigenvectorUnitary
  let s : I3 → ℝ := hN.isHermitian.eigenvalues
  have hs : ∀ i, 0 < s i := hN.eigenvalues_pos
  have hUtU : Uᵀ * U = 1 := by
    change (hN.isHermitian.eigenvectorUnitary : Mat3)ᵀ *
      hN.isHermitian.eigenvectorUnitary = 1
    simpa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hN.isHermitian.eigenvectorUnitary
  have hspect : N = U * Matrix.diagonal s * Uᵀ := by
    simpa [U, s, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hN.isHermitian.spectral_theorem
  have hdiag : Uᵀ * N * U = Matrix.diagonal s := by
    rw [hspect]
    calc
      Uᵀ * (U * Matrix.diagonal s * Uᵀ) * U =
          (Uᵀ * U) * Matrix.diagonal s * (Uᵀ * U) := by noncomm_ring
      _ = Matrix.diagonal s := by rw [hUtU]; simp
  let q := orientedSO3 U hUtU
  refine ⟨q, s, hs, ?_⟩
  change (orientedMatrix U)ᵀ * N * orientedMatrix U = _
  rw [orientedMatrix, Matrix.transpose_mul]
  calc
    (orientationCorrection U)ᵀ * Uᵀ * N *
          (U * orientationCorrection U) =
        (orientationCorrection U)ᵀ * (Uᵀ * N * U) *
          orientationCorrection U := by noncomm_ring
    _ = _ := by rw [hdiag]; exact correction_preserves_diagonal U s hUtU

theorem signedSVD_of_invertible (M : Mat3) (hMdet : M.det ≠ 0) :
    ∃ U V : SO3, ∃ m : I3 → ℝ, (∀ i, m i ≠ 0) ∧
      (V : Mat3)ᵀ * M * U = Matrix.diagonal m := by
  have hMunit : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hMdet)
  have hMinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hMunit
  let N : Mat3 := Mᵀ * M
  have hN : N.PosDef := by
    simpa [N, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.conjTranspose_mul_self M hMinj
  let H : Mat3 := pdSqrt N
  have hH : H.PosDef := pdSqrt_posDef hN
  have hHsq : H * H = N := pdSqrt_sq hN
  have hHt : Hᵀ = H := pdSqrt_transpose hN
  have hHunit : IsUnit H := hH.isUnit
  have hHdetunit : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hHunit
  let O : Mat3 := M * H⁻¹
  have hOorth : Oᵀ * O = 1 := by
    change (M * H⁻¹)ᵀ * (M * H⁻¹) = 1
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hHt]
    change H⁻¹ * Mᵀ * (M * H⁻¹) = 1
    calc
      H⁻¹ * Mᵀ * (M * H⁻¹) = H⁻¹ * (Mᵀ * M) * H⁻¹ := by
        noncomm_ring
      _ = H⁻¹ * (H * H) * H⁻¹ := by rw [hHsq]
      _ = 1 := by
        rw [← Matrix.mul_assoc, H.nonsing_inv_mul hHdetunit]
        simp [H.mul_nonsing_inv hHdetunit]
  have hOtM : Oᵀ * M = H := by
    change (M * H⁻¹)ᵀ * M = H
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hHt]
    calc
      H⁻¹ * Mᵀ * M = H⁻¹ * (Mᵀ * M) := by noncomm_ring
      _ = H⁻¹ * (H * H) := by rw [hHsq]
      _ = H := by
        rw [← Matrix.mul_assoc, H.nonsing_inv_mul hHdetunit]
        simp
  obtain ⟨U, s, hs, hdiag⟩ := diagonalize_posDef_three hH
  let W : Mat3 := O * (U : Mat3)
  have hWorth : Wᵀ * W = 1 := by
    change (O * (U : Mat3))ᵀ * (O * (U : Mat3)) = 1
    rw [Matrix.transpose_mul]
    calc
      (U : Mat3)ᵀ * Oᵀ * (O * U) =
          (U : Mat3)ᵀ * (Oᵀ * O) * U := by noncomm_ring
      _ = 1 := by rw [hOorth]; simpa using so3_transpose_mul U
  let V : SO3 := orientedSO3 W hWorth
  let m : I3 → ℝ := ![W.det * s 0, s 1, s 2]
  have hWdet : W.det ≠ 0 := by
    have hd := det_sq_of_transpose_mul_eq_one hWorth
    nlinarith
  have hm : ∀ i, m i ≠ 0 := by
    intro i
    fin_cases i
    · exact mul_ne_zero hWdet (ne_of_gt (hs 0))
    · exact ne_of_gt (hs 1)
    · exact ne_of_gt (hs 2)
  refine ⟨U, V, m, hm, ?_⟩
  change (orientedMatrix W)ᵀ * M * (U : Mat3) = Matrix.diagonal m
  rw [orientedMatrix, Matrix.transpose_mul, orientationCorrection_transpose]
  have hWM : Wᵀ * M * (U : Mat3) = Matrix.diagonal s := by
    change (O * (U : Mat3))ᵀ * M * (U : Mat3) = _
    rw [Matrix.transpose_mul]
    calc
      (U : Mat3)ᵀ * Oᵀ * M * U =
          (U : Mat3)ᵀ * (Oᵀ * M) * U := by noncomm_ring
      _ = Matrix.diagonal s := by rw [hOtM]; exact hdiag
  rw [show (orientationCorrection W) * Wᵀ * M * (U : Mat3) =
      orientationCorrection W * (Wᵀ * M * (U : Mat3)) by noncomm_ring,
    hWM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orientationCorrection, m, Matrix.mul_apply, Fin.sum_univ_succ]

end S3xS3.Trivial.Graph
