import S3xS3.Trivial.Preparation

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.SwapNaturality

open S3xS3.Naturality

def swapMatrix : Mat6 := Matrix.fromBlocks 0 1 1 0

def swapVec (x : LieVec) : LieVec
  | Sum.inl i => x (Sum.inr i)
  | Sum.inr i => x (Sum.inl i)

@[simp] lemma swapVec_inl (x : LieVec) (i : I3) :
    swapVec x (Sum.inl i) = x (Sum.inr i) := rfl

@[simp] lemma swapVec_inr (x : LieVec) (i : I3) :
    swapVec x (Sum.inr i) = x (Sum.inl i) := rfl

lemma swapMatrix_transpose : swapMatrixᵀ = swapMatrix := by
  rw [swapMatrix, Matrix.fromBlocks_transpose]
  simp

lemma swapMatrix_sq : swapMatrix * swapMatrix = 1 := by
  rw [swapMatrix, Matrix.fromBlocks_multiply]
  simp

lemma swapMatrix_mul_transpose : swapMatrix * swapMatrixᵀ = 1 := by
  rw [swapMatrix_transpose, swapMatrix_sq]

lemma swapMatrix_transpose_mul : swapMatrixᵀ * swapMatrix = 1 := by
  rw [swapMatrix_transpose, swapMatrix_sq]

lemma swapMatrix_mulVec (x : LieVec) : swapMatrix *ᵥ x = swapVec x := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [swapMatrix, swapVec, Matrix.mulVec, dotProduct,
      Matrix.one_apply]

lemma swapVec_involutive (x : LieVec) : swapVec (swapVec x) = x := by
  funext i
  cases i <;> rfl

lemma bracket_swapVec (x y : LieVec) :
    bracket (swapVec x) (swapVec y) = swapVec (bracket x y) := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, swapVec, cross_apply]

noncomputable def swapMetric (g : LeftInvariantMetric) : LeftInvariantMetric where
  gram := swapMatrixᵀ * g.gram * swapMatrix
  posDef := by
    have hunit : IsUnit swapMatrix :=
      IsUnit.of_mul_eq_one swapMatrixᵀ swapMatrix_mul_transpose
    have hinj : Function.Injective swapMatrix.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr hunit
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      g.posDef.conjTranspose_mul_mul_same hinj

lemma swapMetric_gram (g : LeftInvariantMetric) :
    (swapMetric g).gram = swapMatrixᵀ * g.gram * swapMatrix := rfl

lemma swapMetric_involutive (g : LeftInvariantMetric) :
    swapMetric (swapMetric g) = g := by
  apply LeftInvariantMetric.ext
  simp only [swapMetric_gram]
  rw [swapMatrix_transpose]
  calc
    swapMatrix * (swapMatrix * g.gram * swapMatrix) * swapMatrix =
        (swapMatrix * swapMatrix) * g.gram *
          (swapMatrix * swapMatrix) := by noncomm_ring
    _ = g.gram := by rw [swapMatrix_sq]; simp

lemma swapMetric_gram_inv (g : LeftInvariantMetric) :
    (swapMetric g).gram⁻¹ = swapMatrixᵀ * g.gram⁻¹ * swapMatrix := by
  have hJinv : swapMatrix⁻¹ = swapMatrix :=
    Matrix.inv_eq_right_inv swapMatrix_sq
  rw [swapMetric_gram, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    swapMatrix_transpose, hJinv]
  noncomm_ring

lemma metricInner_swap (g : LeftInvariantMetric) (x y : LieVec) :
    metricInner (swapMetric g) x y =
      metricInner g (swapVec x) (swapVec y) := by
  change x ⬝ᵥ (swapMatrixᵀ * g.gram * swapMatrix) *ᵥ y =
    (swapVec x) ⬝ᵥ g.gram *ᵥ swapVec y
  rw [← swapMatrix_mulVec x, ← swapMatrix_mulVec y]
  calc
    x ⬝ᵥ (swapMatrixᵀ * g.gram * swapMatrix) *ᵥ y =
        x ⬝ᵥ swapMatrixᵀ *ᵥ
          (g.gram *ᵥ (swapMatrix *ᵥ y)) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (g.gram *ᵥ (swapMatrix *ᵥ y)) ⬝ᵥ
        (swapMatrix *ᵥ x) :=
      Matrix.dotProduct_transpose_mulVec swapMatrix x
        (g.gram *ᵥ (swapMatrix *ᵥ y))
    _ = (swapMatrix *ᵥ x) ⬝ᵥ
        g.gram *ᵥ (swapMatrix *ᵥ y) := dotProduct_comm _ _

lemma koszulForm_swap (g : LeftInvariantMetric) (x y z : LieVec) :
    koszulForm (swapMetric g) x y z =
      koszulForm g (swapVec x) (swapVec y) (swapVec z) := by
  simp only [koszulForm, metricInner_swap, bracket_swapVec]

lemma koszulCovector_swap (g : LeftInvariantMetric) (x y : LieVec) :
    koszulCovector (swapMetric g) x y =
      swapMatrixᵀ *ᵥ koszulCovector g (swapVec x) (swapVec y) := by
  funext i
  rw [koszulCovector, koszulForm_swap, koszulForm_eq_sum_basis]
  simp only [koszulCovector, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  rcases i with i | i <;> fin_cases i <;>
    simp [swapMatrix, swapVec, basisVec, Matrix.one_apply]

lemma connectionVec_swap (g : LeftInvariantMetric) (x y : LieVec) :
    swapVec (connectionVec (swapMetric g) x y) =
      connectionVec g (swapVec x) (swapVec y) := by
  rw [← swapMatrix_mulVec]
  let k := koszulCovector g (swapVec x) (swapVec y)
  change swapMatrix *ᵥ ((swapMetric g).gram⁻¹ *ᵥ
      koszulCovector (swapMetric g) x y) = g.gram⁻¹ *ᵥ k
  rw [swapMetric_gram_inv, koszulCovector_swap]
  simp only [Matrix.mulVec_mulVec]
  rw [swapMatrix_transpose]
  have hmat : swapMatrix *
      (swapMatrix * g.gram⁻¹ * swapMatrix * swapMatrix) = g.gram⁻¹ := by
    calc
      swapMatrix * (swapMatrix * g.gram⁻¹ * swapMatrix * swapMatrix) =
          (swapMatrix * swapMatrix) * g.gram⁻¹ *
            (swapMatrix * swapMatrix) := by noncomm_ring
      _ = g.gram⁻¹ := by rw [swapMatrix_sq]; simp
  rw [hmat]

lemma swapVec_sub (x y : LieVec) : swapVec (x - y) = swapVec x - swapVec y := by
  funext i
  cases i <;> rfl

lemma curvatureVec_swap (g : LeftInvariantMetric) (x y z : LieVec) :
    swapVec (curvatureVec (swapMetric g) x y z) =
      curvatureVec g (swapVec x) (swapVec y) (swapVec z) := by
  rw [curvatureVec, swapVec_sub, swapVec_sub,
    connectionVec_swap, connectionVec_swap, connectionVec_swap,
    connectionVec_swap, connectionVec_swap]
  rw [← bracket_swapVec, curvatureVec]

lemma curvatureEndomorphism_swap (g : LeftInvariantMetric)
    (x y : LieVec) :
    curvatureEndomorphism (swapMetric g) x y =
      swapMatrixᵀ *
        curvatureEndomorphism g (swapVec x) (swapVec y) * swapMatrix := by
  let M := curvatureEndomorphism g (swapVec x) (swapVec y)
  rw [Matrix.ext_iff_mulVec]
  intro v
  have hnat := curvatureVec_swap g v x y
  rw [← curvatureEndomorphism_mulVec (swapMetric g) x y v] at hnat
  rw [← curvatureEndomorphism_mulVec g (swapVec x) (swapVec y)
    (swapVec v)] at hnat
  rw [← swapMatrix_mulVec
      (curvatureEndomorphism (swapMetric g) x y *ᵥ v),
    ← swapMatrix_mulVec v] at hnat
  have hh := congrArg (fun w : LieVec ↦ swapMatrixᵀ *ᵥ w) hnat
  simp only [Matrix.mulVec_mulVec] at hh ⊢
  have hh' : ((swapMatrixᵀ * swapMatrix) *
      curvatureEndomorphism (swapMetric g) x y) *ᵥ v =
      (swapMatrixᵀ * M * swapMatrix) *ᵥ v := by
    simpa only [Matrix.mul_assoc] using hh
  rw [swapMatrix_transpose_mul] at hh'
  simpa using hh'

lemma ricciForm_swap (g : LeftInvariantMetric) (x y : LieVec) :
    ricciForm (swapMetric g) x y =
      ricciForm g (swapVec x) (swapVec y) := by
  rw [ricciForm, curvatureEndomorphism_swap, ricciForm]
  rw [Matrix.trace_mul_cycle, swapMatrix_mul_transpose]
  simp

lemma swapVec_basis (i : I6) :
    swapVec (basisVec i) = basisVec (Sum.swap i) := by
  funext j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [swapVec, basisVec]

theorem ricci_swap (g : LeftInvariantMetric) :
    ricci (swapMetric g) = swapMatrixᵀ * ricci g * swapMatrix := by
  ext j k
  rw [← ricciForm_basis, ricciForm_swap, ricciForm_eq_matrix]
  rw [← swapMatrix_mulVec, ← swapMatrix_mulVec]
  have hj : swapMatrix *ᵥ basisVec j = swapMatrixᵀ j := by
    funext i
    simp [basisVec, Matrix.mulVec, dotProduct]
  have hk : swapMatrix *ᵥ basisVec k = swapMatrixᵀ k := by
    funext i
    simp [basisVec, Matrix.mulVec, dotProduct]
  rw [hj, hk]
  exact (Matrix.mul_mul_apply swapMatrixᵀ (ricci g) swapMatrix j k).symm

theorem Einstein.swap {g : LeftInvariantMetric} (hg : Einstein g) :
    Einstein (swapMetric g) := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, ?_⟩
  rw [ricci_swap, hc]
  change swapMatrixᵀ * (c • g.gram) * swapMatrix =
    c • (swapMatrixᵀ * g.gram * swapMatrix)
  simp

def swapAction (a : InnerAction) : InnerAction := (a.2, a.1)

lemma innerMatrix_swapAction (a : InnerAction) :
    innerMatrix (swapAction a) = swapMatrix * innerMatrix a * swapMatrix := by
  change Matrix.fromBlocks (a.2 : Mat3) 0 0 (a.1 : Mat3) =
    Matrix.fromBlocks 0 1 1 0 *
      Matrix.fromBlocks (a.1 : Mat3) 0 0 (a.2 : Mat3) *
        Matrix.fromBlocks 0 1 1 0
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  apply Matrix.fromBlocks_inj.mpr
  simp

lemma swapAction_ne_one {a : InnerAction} (ha : a ≠ 1) : swapAction a ≠ 1 := by
  intro h
  apply ha
  apply Prod.ext
  · have h' := congrArg Prod.snd h
    simpa [swapAction] using h'
  · have h' := congrArg Prod.fst h
    simpa [swapAction] using h'

lemma fixes_swap_iff (a : InnerAction) (g : LeftInvariantMetric) :
    Fixes a (swapMetric g) ↔ Fixes (swapAction a) g := by
  let A := innerMatrix a
  let J := swapMatrix
  have hJt : Jᵀ = J := swapMatrix_transpose
  have hJJ : J * J = 1 := swapMatrix_sq
  have hshape : (J * A * J)ᵀ * g.gram * (J * A * J) =
      J * (Aᵀ * (J * g.gram * J) * A) * J := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hJt]
    noncomm_ring
  constructor
  · intro h
    rw [Fixes] at h ⊢
    change Aᵀ * (Jᵀ * g.gram * J) * A = Jᵀ * g.gram * J at h
    have hcenter : Aᵀ * (J * g.gram * J) * A = J * g.gram * J := by
      simpa [hJt] using h
    rw [innerMatrix_swapAction]
    rw [hshape, hcenter]
    calc
      J * (J * g.gram * J) * J = (J * J) * g.gram * (J * J) := by
        noncomm_ring
      _ = g.gram := by rw [hJJ]; simp
  · intro h
    rw [Fixes] at h ⊢
    rw [innerMatrix_swapAction] at h
    rw [hshape] at h
    change Aᵀ * (Jᵀ * g.gram * J) * A = Jᵀ * g.gram * J
    rw [hJt]
    let C : Mat6 := Aᵀ * (J * g.gram * J) * A
    have hC : J * C * J = g.gram := by simpa [C] using h
    change C = J * g.gram * J
    calc
      C = J * (J * C * J) * J := by
        symm
        calc
          J * (J * C * J) * J = (J * J) * C * (J * J) := by
            noncomm_ring
          _ = C := by rw [hJJ]; simp
      _ = J * g.gram * J := by rw [hC]

theorem nontrivial_of_swap {g : LeftInvariantMetric}
    (h : HasNontrivialInnerIsotropy (swapMetric g)) :
    HasNontrivialInnerIsotropy g := by
  obtain ⟨a, ha, hfix⟩ := h
  exact ⟨swapAction a, swapAction_ne_one ha, (fixes_swap_iff a g).1 hfix⟩

end S3xS3.Trivial.SwapNaturality
