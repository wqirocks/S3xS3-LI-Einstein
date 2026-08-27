import S3xS3.Core

open scoped Matrix BigOperators

namespace S3xS3.Naturality

lemma innerMatrix_mulVec_inl (a : InnerAction) (x : LieVec) (i : I3) :
    (innerMatrix a *ᵥ x) (Sum.inl i) =
      ((a.1 : Mat3) *ᵥ (fun j ↦ x (Sum.inl j))) i := by
  simp [innerMatrix, Matrix.mulVec, dotProduct]

lemma innerMatrix_mulVec_inr (a : InnerAction) (x : LieVec) (i : I3) :
    (innerMatrix a *ᵥ x) (Sum.inr i) =
      ((a.2 : Mat3) *ᵥ (fun j ↦ x (Sum.inr j))) i := by
  simp [innerMatrix, Matrix.mulVec, dotProduct]

lemma bracket_innerMatrix (a : InnerAction) (x y : LieVec) :
    bracket (innerMatrix a *ᵥ x) (innerMatrix a *ᵥ y) =
      innerMatrix a *ᵥ bracket x y := by
  funext i
  cases i with
  | inl i =>
      simpa only [bracket_apply_inl, innerMatrix_mulVec_inl] using
        congrFun (so3_cross_mulVec a.1
          (fun j ↦ x (Sum.inl j)) (fun j ↦ y (Sum.inl j))) i
  | inr i =>
      simpa only [bracket_apply_inr, innerMatrix_mulVec_inr] using
        congrFun (so3_cross_mulVec a.2
          (fun j ↦ x (Sum.inr j)) (fun j ↦ y (Sum.inr j))) i

lemma metricInner_pullback (a : InnerAction) (g : LeftInvariantMetric)
    (x y : LieVec) :
    metricInner (pullbackMetric a g) x y =
      metricInner g (innerMatrix a *ᵥ x) (innerMatrix a *ᵥ y) := by
  let T := innerMatrix a
  change x ⬝ᵥ (Tᵀ * g.gram * T) *ᵥ y =
    (T *ᵥ x) ⬝ᵥ g.gram *ᵥ (T *ᵥ y)
  calc
    x ⬝ᵥ (Tᵀ * g.gram * T) *ᵥ y =
        x ⬝ᵥ Tᵀ *ᵥ (g.gram *ᵥ (T *ᵥ y)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (g.gram *ᵥ (T *ᵥ y)) ⬝ᵥ (T *ᵥ x) :=
      Matrix.dotProduct_transpose_mulVec T x (g.gram *ᵥ (T *ᵥ y))
    _ = (T *ᵥ x) ⬝ᵥ g.gram *ᵥ (T *ᵥ y) := dotProduct_comm _ _

@[simp] lemma bracket_add_left (x x' y : LieVec) :
    bracket (x + x') y = bracket x y + bracket x' y := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

@[simp] lemma bracket_add_right (x y y' : LieVec) :
    bracket x (y + y') = bracket x y + bracket x y' := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

@[simp] lemma bracket_smul_left (c : ℝ) (x y : LieVec) :
    bracket (c • x) y = c • bracket x y := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

@[simp] lemma bracket_smul_right (c : ℝ) (x y : LieVec) :
    bracket x (c • y) = c • bracket x y := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

@[simp] lemma metricInner_add_left (g : LeftInvariantMetric) (x x' y : LieVec) :
    metricInner g (x + x') y = metricInner g x y + metricInner g x' y := by
  simp [metricInner, add_dotProduct]

@[simp] lemma metricInner_add_right (g : LeftInvariantMetric) (x y y' : LieVec) :
    metricInner g x (y + y') = metricInner g x y + metricInner g x y' := by
  simp [metricInner, Matrix.mulVec_add, dotProduct_add]

@[simp] lemma metricInner_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    metricInner g (c • x) y = c * metricInner g x y := by
  simp [metricInner, smul_dotProduct]

@[simp] lemma metricInner_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    metricInner g x (c • y) = c * metricInner g x y := by
  simp [metricInner, Matrix.mulVec_smul, dotProduct_smul]

/-- Koszul's trilinear expression before raising its final index. -/
noncomputable def koszulForm (g : LeftInvariantMetric) (x y z : LieVec) : ℝ :=
  (metricInner g (bracket x y) z - metricInner g (bracket y z) x +
    metricInner g (bracket z x) y) / 2

@[simp] lemma koszulForm_add_right (g : LeftInvariantMetric) (x y z z' : LieVec) :
    koszulForm g x y (z + z') =
      koszulForm g x y z + koszulForm g x y z' := by
  simp [koszulForm]
  ring

@[simp] lemma koszulForm_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    koszulForm g x y (c • z) = c * koszulForm g x y z := by
  simp [koszulForm]
  ring

noncomputable def koszulFormRight (g : LeftInvariantMetric) (x y : LieVec) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := koszulForm g x y
  map_add' := koszulForm_add_right g x y
  map_smul' c z := by
    simp only [koszulForm_smul_right, RingHom.id_apply, smul_eq_mul]

lemma lieVec_eq_sum_basis (x : LieVec) :
    x = ∑ i, x i • basisVec i := by
  funext j
  simp [basisVec]

lemma koszulForm_eq_sum_basis (g : LeftInvariantMetric) (x y z : LieVec) :
    koszulForm g x y z = ∑ i, z i * koszulForm g x y (basisVec i) := by
  conv_lhs => rw [lieVec_eq_sum_basis z]
  change koszulFormRight g x y (∑ i, z i • basisVec i) = _
  rw [map_sum]
  simp [koszulFormRight]

lemma koszulForm_pullback (a : InnerAction) (g : LeftInvariantMetric)
    (x y z : LieVec) :
    koszulForm (pullbackMetric a g) x y z =
      koszulForm g (innerMatrix a *ᵥ x) (innerMatrix a *ᵥ y)
        (innerMatrix a *ᵥ z) := by
  simp only [koszulForm, metricInner_pullback, bracket_innerMatrix]

/-- The covector obtained from Koszul's expression by inserting coordinate
basis vectors in its final slot. -/
noncomputable def koszulCovector (g : LeftInvariantMetric) (x y : LieVec) :
    LieVec := fun i ↦ koszulForm g x y (basisVec i)

lemma innerMatrix_mulVec_basis (a : InnerAction) (i j : I6) :
    (innerMatrix a *ᵥ basisVec i) j = innerMatrix a j i := by
  simp [basisVec, Matrix.mulVec, dotProduct]

lemma koszulCovector_pullback (a : InnerAction) (g : LeftInvariantMetric)
    (x y : LieVec) :
    koszulCovector (pullbackMetric a g) x y =
      (innerMatrix a)ᵀ *ᵥ
        koszulCovector g (innerMatrix a *ᵥ x) (innerMatrix a *ᵥ y) := by
  funext i
  rw [koszulCovector, koszulForm_pullback, koszulForm_eq_sum_basis]
  simp only [koszulCovector, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  simp [basisVec]

/-- The Levi-Civita connection on arbitrary coordinate vectors, obtained by
raising the Koszul covector with the inverse Gram matrix. -/
noncomputable def connectionVec (g : LeftInvariantMetric) (x y : LieVec) :
    LieVec := g.gram⁻¹ *ᵥ koszulCovector g x y

lemma metricInner_connectionVec (g : LeftInvariantMetric) (x y z : LieVec) :
    metricInner g (connectionVec g x y) z = koszulForm g x y z := by
  let G := g.gram
  let k := koszulCovector g x y
  letI : Invertible G := g.posDef.isUnit.invertible
  have hGt : Gᵀ = G := by
    simpa [G, Matrix.conjTranspose_eq_transpose_of_trivial] using
      g.isHermitian.eq
  change (G⁻¹ *ᵥ k) ⬝ᵥ (G *ᵥ z) = koszulForm g x y z
  calc
    (G⁻¹ *ᵥ k) ⬝ᵥ (G *ᵥ z) =
        z ⬝ᵥ Gᵀ *ᵥ (G⁻¹ *ᵥ k) := by
      symm
      exact Matrix.dotProduct_transpose_mulVec G z (G⁻¹ *ᵥ k)
    _ = z ⬝ᵥ (G * G⁻¹) *ᵥ k := by
      rw [hGt, Matrix.mulVec_mulVec]
    _ = z ⬝ᵥ k := by rw [Matrix.mul_inv_of_invertible]; simp
    _ = ∑ i, z i * koszulForm g x y (basisVec i) := by
      rfl
    _ = koszulForm g x y z := (koszulForm_eq_sum_basis g x y z).symm

lemma connectionVec_natural (a : InnerAction) (g : LeftInvariantMetric)
    (x y : LieVec) :
    innerMatrix a *ᵥ connectionVec (pullbackMetric a g) x y =
      connectionVec g (innerMatrix a *ᵥ x) (innerMatrix a *ᵥ y) := by
  let T := innerMatrix a
  let k := koszulCovector g (T *ᵥ x) (T *ᵥ y)
  have hTT : T * Tᵀ = 1 := innerMatrix_mul_transpose a
  change T *ᵥ ((pullbackMetric a g).gram⁻¹ *ᵥ
      koszulCovector (pullbackMetric a g) x y) = g.gram⁻¹ *ᵥ k
  rw [pullbackMetric_gram_inv, koszulCovector_pullback]
  change T *ᵥ ((Tᵀ * g.gram⁻¹ * T) *ᵥ (Tᵀ *ᵥ k)) = g.gram⁻¹ *ᵥ k
  simp only [Matrix.mulVec_mulVec]
  calc
    (T * (Tᵀ * g.gram⁻¹ * T * Tᵀ)) *ᵥ k =
        ((T * Tᵀ) * g.gram⁻¹ * (T * Tᵀ)) *ᵥ k := by
          congr 1
          noncomm_ring
    _ = g.gram⁻¹ *ᵥ k := by rw [hTT]; simp

/-- Curvature on arbitrary coordinate vectors, with the same sign convention
as `curvatureComponent`. -/
noncomputable def curvatureVec (g : LeftInvariantMetric)
    (x y z : LieVec) : LieVec :=
  connectionVec g x (connectionVec g y z) -
    connectionVec g y (connectionVec g x z) -
      connectionVec g (bracket x y) z

lemma curvatureVec_natural (a : InnerAction) (g : LeftInvariantMetric)
    (x y z : LieVec) :
    innerMatrix a *ᵥ curvatureVec (pullbackMetric a g) x y z =
      curvatureVec g (innerMatrix a *ᵥ x) (innerMatrix a *ᵥ y)
        (innerMatrix a *ᵥ z) := by
  simp only [curvatureVec, Matrix.mulVec_sub, connectionVec_natural,
    bracket_innerMatrix]

lemma metricInner_bracket_basis (g : LeftInvariantMetric) (i j k : I6) :
    metricInner g (bracket (basisVec i) (basisVec j)) (basisVec k) =
      loweredBracket g i j k := by
  simp [metricInner, loweredBracket, structureConstant, basisVec,
    Matrix.mulVec, dotProduct]

lemma koszulForm_basis (g : LeftInvariantMetric) (i j k : I6) :
    koszulForm g (basisVec i) (basisVec j) (basisVec k) =
      koszulLower g i j k := by
  simp only [koszulForm, koszulLower, metricInner_bracket_basis]

lemma connectionVec_basis_apply (g : LeftInvariantMetric) (i j k : I6) :
    connectionVec g (basisVec i) (basisVec j) k = christoffel g i j k := by
  simp [connectionVec, koszulCovector, christoffel, Matrix.mulVec,
    dotProduct, koszulForm_basis]

@[simp] lemma koszulForm_add_left (g : LeftInvariantMetric)
    (x x' y z : LieVec) :
    koszulForm g (x + x') y z =
      koszulForm g x y z + koszulForm g x' y z := by
  simp [koszulForm]
  ring

@[simp] lemma koszulForm_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    koszulForm g (c • x) y z = c * koszulForm g x y z := by
  simp [koszulForm]
  ring

@[simp] lemma koszulForm_add_middle (g : LeftInvariantMetric)
    (x y y' z : LieVec) :
    koszulForm g x (y + y') z =
      koszulForm g x y z + koszulForm g x y' z := by
  simp [koszulForm]
  ring

@[simp] lemma koszulForm_smul_middle (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    koszulForm g x (c • y) z = c * koszulForm g x y z := by
  simp [koszulForm]
  ring

@[simp] lemma connectionVec_add_left (g : LeftInvariantMetric)
    (x x' y : LieVec) :
    connectionVec g (x + x') y =
      connectionVec g x y + connectionVec g x' y := by
  have hcov : koszulCovector g (x + x') y =
      koszulCovector g x y + koszulCovector g x' y := by
    funext k
    simp [koszulCovector]
  simp [connectionVec, hcov, Matrix.mulVec_add]

@[simp] lemma connectionVec_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    connectionVec g (c • x) y = c • connectionVec g x y := by
  have hcov : koszulCovector g (c • x) y = c • koszulCovector g x y := by
    funext k
    simp [koszulCovector]
  simp [connectionVec, hcov, Matrix.mulVec_smul]

@[simp] lemma connectionVec_add_right (g : LeftInvariantMetric)
    (x y y' : LieVec) :
    connectionVec g x (y + y') =
      connectionVec g x y + connectionVec g x y' := by
  have hcov : koszulCovector g x (y + y') =
      koszulCovector g x y + koszulCovector g x y' := by
    funext k
    simp [koszulCovector]
  simp [connectionVec, hcov, Matrix.mulVec_add]

@[simp] lemma connectionVec_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    connectionVec g x (c • y) = c • connectionVec g x y := by
  have hcov : koszulCovector g x (c • y) = c • koszulCovector g x y := by
    funext k
    simp [koszulCovector]
  simp [connectionVec, hcov, Matrix.mulVec_smul]

noncomputable def connectionRight (g : LeftInvariantMetric) (x : LieVec) :
    LieVec →ₗ[ℝ] LieVec where
  toFun := connectionVec g x
  map_add' := connectionVec_add_right g x
  map_smul' c y := by
    simpa only [RingHom.id_apply] using connectionVec_smul_right g c x y

lemma connectionVec_eq_sum_basis_right (g : LeftInvariantMetric)
    (x y : LieVec) :
    connectionVec g x y = ∑ i, y i • connectionVec g x (basisVec i) := by
  conv_lhs => rw [lieVec_eq_sum_basis y]
  change connectionRight g x (∑ i, y i • basisVec i) = _
  rw [map_sum]
  simp [connectionRight]

noncomputable def connectionLeft (g : LeftInvariantMetric) (y : LieVec) :
    LieVec →ₗ[ℝ] LieVec where
  toFun := fun x ↦ connectionVec g x y
  map_add' := fun x x' ↦ connectionVec_add_left g x x' y
  map_smul' c x := by
    simpa only [RingHom.id_apply] using connectionVec_smul_left g c x y

lemma connectionVec_eq_sum_basis_left (g : LeftInvariantMetric)
    (x y : LieVec) :
    connectionVec g x y = ∑ i, x i • connectionVec g (basisVec i) y := by
  conv_lhs => rw [lieVec_eq_sum_basis x]
  change connectionLeft g y (∑ i, x i • basisVec i) = _
  rw [map_sum]
  simp [connectionLeft]

lemma connectionVec_basis_left_apply (g : LeftInvariantMetric)
    (i : I6) (y : LieVec) (n : I6) :
    connectionVec g (basisVec i) y n =
      ∑ m, y m * christoffel g i m n := by
  rw [connectionVec_eq_sum_basis_right]
  simp [connectionVec_basis_apply]

lemma connectionVec_basis_right_apply (g : LeftInvariantMetric)
    (x : LieVec) (k n : I6) :
    connectionVec g x (basisVec k) n =
      ∑ m, x m * christoffel g m k n := by
  rw [connectionVec_eq_sum_basis_left]
  simp [connectionVec_basis_apply]

lemma curvatureVec_basis_apply (g : LeftInvariantMetric) (i j k n : I6) :
    curvatureVec g (basisVec i) (basisVec j) (basisVec k) n =
      curvatureComponent g i j k n := by
  simp only [curvatureVec, Pi.sub_apply, connectionVec_basis_left_apply,
    connectionVec_basis_right_apply, curvatureComponent, structureConstant]
  simp [basisVec]

@[simp] lemma curvatureVec_add_left (g : LeftInvariantMetric)
    (x x' y z : LieVec) :
    curvatureVec g (x + x') y z =
      curvatureVec g x y z + curvatureVec g x' y z := by
  simp [curvatureVec]
  module

@[simp] lemma curvatureVec_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    curvatureVec g (c • x) y z = c • curvatureVec g x y z := by
  simp [curvatureVec]
  module

noncomputable def curvatureLeft (g : LeftInvariantMetric) (y z : LieVec) :
    LieVec →ₗ[ℝ] LieVec where
  toFun := fun x ↦ curvatureVec g x y z
  map_add' := fun x x' ↦ curvatureVec_add_left g x x' y z
  map_smul' c x := by
    simpa only [RingHom.id_apply] using curvatureVec_smul_left g c x y z

lemma curvatureVec_eq_sum_basis_left (g : LeftInvariantMetric)
    (x y z : LieVec) :
    curvatureVec g x y z = ∑ i, x i • curvatureVec g (basisVec i) y z := by
  conv_lhs => rw [lieVec_eq_sum_basis x]
  change curvatureLeft g y z (∑ i, x i • basisVec i) = _
  rw [map_sum]
  simp [curvatureLeft]

/-- Matrix of the curvature endomorphism `w ↦ R(w,x)y`; its column indexed
by `i` is the curvature vector evaluated on the `i`th basis vector. -/
noncomputable def curvatureEndomorphism (g : LeftInvariantMetric)
    (x y : LieVec) : Mat6 :=
  fun n i ↦ curvatureVec g (basisVec i) x y n

lemma curvatureEndomorphism_mulVec (g : LeftInvariantMetric)
    (x y v : LieVec) :
    curvatureEndomorphism g x y *ᵥ v = curvatureVec g v x y := by
  rw [curvatureVec_eq_sum_basis_left]
  funext n
  simp [curvatureEndomorphism, Matrix.mulVec, dotProduct, mul_comm]

lemma curvatureEndomorphism_pullback (a : InnerAction)
    (g : LeftInvariantMetric) (x y : LieVec) :
    curvatureEndomorphism (pullbackMetric a g) x y =
      (innerMatrix a)ᵀ *
        curvatureEndomorphism g (innerMatrix a *ᵥ x) (innerMatrix a *ᵥ y) *
          innerMatrix a := by
  let T := innerMatrix a
  let M := curvatureEndomorphism g (T *ᵥ x) (T *ᵥ y)
  have hTtT : Tᵀ * T = 1 := innerMatrix_transpose_mul a
  rw [Matrix.ext_iff_mulVec]
  intro v
  have hnat := curvatureVec_natural a g v x y
  rw [← curvatureEndomorphism_mulVec (pullbackMetric a g) x y v] at hnat
  rw [← curvatureEndomorphism_mulVec g (T *ᵥ x) (T *ᵥ y) (T *ᵥ v)] at hnat
  change T *ᵥ (curvatureEndomorphism (pullbackMetric a g) x y *ᵥ v) =
    M *ᵥ (T *ᵥ v) at hnat
  have hh := congrArg (fun w : LieVec ↦ Tᵀ *ᵥ w) hnat
  simp only [Matrix.mulVec_mulVec] at hh ⊢
  have hh' : ((Tᵀ * T) * curvatureEndomorphism (pullbackMetric a g) x y) *ᵥ v =
      (Tᵀ * M * T) *ᵥ v := by
    simpa only [Matrix.mul_assoc] using hh
  rw [hTtT] at hh'
  simpa only [Matrix.one_mul] using hh'

/-- Ricci as the trace of the curvature endomorphism. -/
noncomputable def ricciForm (g : LeftInvariantMetric) (x y : LieVec) : ℝ :=
  Matrix.trace (curvatureEndomorphism g x y)

lemma ricciForm_basis (g : LeftInvariantMetric) (j k : I6) :
    ricciForm g (basisVec j) (basisVec k) = ricci g j k := by
  simp [ricciForm, Matrix.trace, curvatureEndomorphism,
    ricci, curvatureVec_basis_apply]

lemma ricciForm_pullback (a : InnerAction) (g : LeftInvariantMetric)
    (x y : LieVec) :
    ricciForm (pullbackMetric a g) x y =
      ricciForm g (innerMatrix a *ᵥ x) (innerMatrix a *ᵥ y) := by
  rw [ricciForm, curvatureEndomorphism_pullback, ricciForm]
  rw [Matrix.trace_mul_cycle]
  rw [innerMatrix_mul_transpose]
  simp

@[simp] lemma curvatureVec_add_middle (g : LeftInvariantMetric)
    (x y y' z : LieVec) :
    curvatureVec g x (y + y') z =
      curvatureVec g x y z + curvatureVec g x y' z := by
  simp [curvatureVec]
  module

@[simp] lemma curvatureVec_smul_middle (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    curvatureVec g x (c • y) z = c • curvatureVec g x y z := by
  simp [curvatureVec]
  module

@[simp] lemma curvatureVec_add_right (g : LeftInvariantMetric)
    (x y z z' : LieVec) :
    curvatureVec g x y (z + z') =
      curvatureVec g x y z + curvatureVec g x y z' := by
  simp [curvatureVec]
  module

@[simp] lemma curvatureVec_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    curvatureVec g x y (c • z) = c • curvatureVec g x y z := by
  simp [curvatureVec]
  module

@[simp] lemma ricciForm_add_left (g : LeftInvariantMetric)
    (x x' y : LieVec) :
    ricciForm g (x + x') y = ricciForm g x y + ricciForm g x' y := by
  have hM : curvatureEndomorphism g (x + x') y =
      curvatureEndomorphism g x y + curvatureEndomorphism g x' y := by
    ext i j
    simp [curvatureEndomorphism]
  rw [ricciForm, hM, Matrix.trace_add]
  rfl

@[simp] lemma ricciForm_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    ricciForm g (c • x) y = c * ricciForm g x y := by
  have hM : curvatureEndomorphism g (c • x) y =
      c • curvatureEndomorphism g x y := by
    ext i j
    simp [curvatureEndomorphism]
  rw [ricciForm, hM, Matrix.trace_smul]
  rfl

@[simp] lemma ricciForm_add_right (g : LeftInvariantMetric)
    (x y y' : LieVec) :
    ricciForm g x (y + y') = ricciForm g x y + ricciForm g x y' := by
  have hM : curvatureEndomorphism g x (y + y') =
      curvatureEndomorphism g x y + curvatureEndomorphism g x y' := by
    ext i j
    simp [curvatureEndomorphism]
  rw [ricciForm, hM, Matrix.trace_add]
  rfl

@[simp] lemma ricciForm_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    ricciForm g x (c • y) = c * ricciForm g x y := by
  have hM : curvatureEndomorphism g x (c • y) =
      c • curvatureEndomorphism g x y := by
    ext i j
    simp [curvatureEndomorphism]
  rw [ricciForm, hM, Matrix.trace_smul]
  rfl

noncomputable def ricciLeft (g : LeftInvariantMetric) (y : LieVec) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := fun x ↦ ricciForm g x y
  map_add' := fun x x' ↦ ricciForm_add_left g x x' y
  map_smul' c x := by
    simp only [ricciForm_smul_left, RingHom.id_apply, smul_eq_mul]

noncomputable def ricciRight (g : LeftInvariantMetric) (x : LieVec) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := ricciForm g x
  map_add' := ricciForm_add_right g x
  map_smul' c y := by
    simp only [ricciForm_smul_right, RingHom.id_apply, smul_eq_mul]

lemma ricciForm_eq_sum_basis_left (g : LeftInvariantMetric) (x y : LieVec) :
    ricciForm g x y = ∑ i, x i * ricciForm g (basisVec i) y := by
  conv_lhs => rw [lieVec_eq_sum_basis x]
  change ricciLeft g y (∑ i, x i • basisVec i) = _
  rw [map_sum]
  simp [ricciLeft]

lemma ricciForm_eq_sum_basis_right (g : LeftInvariantMetric) (x y : LieVec) :
    ricciForm g x y = ∑ i, y i * ricciForm g x (basisVec i) := by
  conv_lhs => rw [lieVec_eq_sum_basis y]
  change ricciRight g x (∑ i, y i • basisVec i) = _
  rw [map_sum]
  simp [ricciRight]

lemma ricciForm_eq_matrix (g : LeftInvariantMetric) (x y : LieVec) :
    ricciForm g x y = x ⬝ᵥ ricci g *ᵥ y := by
  rw [ricciForm_eq_sum_basis_left]
  calc
    ∑ i, x i * ricciForm g (basisVec i) y =
        ∑ i, x i * (∑ j, y j * ricciForm g (basisVec i) (basisVec j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [ricciForm_eq_sum_basis_right]
    _ = ∑ i, x i * (∑ j, y j * ricci g i j) := by
      simp only [ricciForm_basis]
    _ = x ⬝ᵥ ricci g *ᵥ y := by
      simp_rw [Finset.mul_sum]
      rw [Matrix.dot_mulVec_eq_sum_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem ricci_pullback (a : InnerAction) (g : LeftInvariantMetric) :
    ricci (pullbackMetric a g) =
      (innerMatrix a)ᵀ * ricci g * innerMatrix a := by
  ext j k
  rw [← ricciForm_basis, ricciForm_pullback, ricciForm_eq_matrix]
  have hj : innerMatrix a *ᵥ basisVec j = (innerMatrix a)ᵀ j := by
    funext i
    simp [basisVec, Matrix.mulVec, dotProduct]
  have hk : innerMatrix a *ᵥ basisVec k = (innerMatrix a)ᵀ k := by
    funext i
    simp [basisVec, Matrix.mulVec, dotProduct]
  rw [hj, hk]
  exact (Matrix.mul_mul_apply (innerMatrix a)ᵀ (ricci g) (innerMatrix a) j k).symm

theorem Einstein.pullback {g : LeftInvariantMetric} (hg : Einstein g)
    (a : InnerAction) : Einstein (pullbackMetric a g) := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, ?_⟩
  rw [ricci_pullback, hc]
  change (innerMatrix a)ᵀ * (c • g.gram) * innerMatrix a =
    c • ((innerMatrix a)ᵀ * g.gram * innerMatrix a)
  simp

end S3xS3.Naturality
