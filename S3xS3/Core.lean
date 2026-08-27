import Mathlib

/-!
# The algebraic model of left-invariant metrics on `SU(2) × SU(2)`

The tangent Lie algebra is represented by `ℝ³ ⊕ ℝ³`.  Inner automorphisms act
through `SO(3) × SO(3)`.  This file fixes the action convention and defines the
inner-isotropy subgroup of a positive-definite metric matrix.
-/

open scoped Matrix

namespace S3xS3

abbrev I3 := Fin 3
abbrev I6 := Sum I3 I3
abbrev Mat3 := Matrix I3 I3 ℝ
abbrev Mat6 := Matrix I6 I6 ℝ
abbrev SO3 := Matrix.specialOrthogonalGroup I3 ℝ
abbrev InnerAction := SO3 × SO3

abbrev Vec3 := I3 → ℝ
abbrev LieVec := I6 → ℝ

/-! ## Cross-product covariance -/

/-- The explicit `3 × 3` cofactor matrix, in the convention satisfying
`cofactor3 A * Aᵀ = det A • 1`. -/
def cofactor3 (A : Mat3) : Mat3 :=
  !![A 1 1 * A 2 2 - A 1 2 * A 2 1,
     A 1 2 * A 2 0 - A 1 0 * A 2 2,
     A 1 0 * A 2 1 - A 1 1 * A 2 0;
     A 0 2 * A 2 1 - A 0 1 * A 2 2,
     A 0 0 * A 2 2 - A 0 2 * A 2 0,
     A 0 1 * A 2 0 - A 0 0 * A 2 1;
     A 0 1 * A 1 2 - A 0 2 * A 1 1,
     A 0 2 * A 1 0 - A 0 0 * A 1 2,
     A 0 0 * A 1 1 - A 0 1 * A 1 0]

lemma cross_mulVec (A : Mat3) (u v : Vec3) :
    (A *ᵥ u) ⨯₃ (A *ᵥ v) = cofactor3 A *ᵥ (u ⨯₃ v) := by
  funext i
  fin_cases i <;>
    simp [cofactor3, cross_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;>
    ring

lemma cofactor3_mul_transpose (A : Mat3) :
    cofactor3 A * Aᵀ = A.det • (1 : Mat3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactor3, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.det_fin_three] <;> ring

lemma cofactor3_eq_of_mem_SO3 (A : SO3) : cofactor3 A = (A : Mat3) := by
  have hcof : cofactor3 A * (A : Mat3)ᵀ = 1 := by
    rw [cofactor3_mul_transpose]
    have hdet : (A : Mat3).det = 1 :=
      (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).2
    rw [hdet]
    simp
  have horth : (A : Mat3) * (A : Mat3)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).1
  have horth' : (A : Mat3)ᵀ * (A : Mat3) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).1
  calc
    cofactor3 A = cofactor3 A * 1 := by simp
    _ = cofactor3 A * ((A : Mat3)ᵀ * A) := by rw [horth']
    _ = (cofactor3 A * (A : Mat3)ᵀ) * A := by noncomm_ring
    _ = A := by rw [hcof]; simp

lemma so3_cross_mulVec (A : SO3) (u v : Vec3) :
    ((A : Mat3) *ᵥ u) ⨯₃ ((A : Mat3) *ᵥ v) =
      (A : Mat3) *ᵥ (u ⨯₃ v) := by
  rw [cross_mulVec, cofactor3_eq_of_mem_SO3]

/-- The coordinate Lie bracket on `su(2) ⊕ su(2)`, with each summand represented
by the usual cross product on `ℝ³`. -/
def bracket (x y : LieVec) : LieVec
  | Sum.inl i => (fun j ↦ x (Sum.inl j)) ⨯₃ (fun j ↦ y (Sum.inl j)) $ i
  | Sum.inr i => (fun j ↦ x (Sum.inr j)) ⨯₃ (fun j ↦ y (Sum.inr j)) $ i

@[simp]
theorem bracket_apply_inl (x y : LieVec) (i : I3) :
    bracket x y (Sum.inl i) =
      ((fun j ↦ x (Sum.inl j)) ⨯₃ (fun j ↦ y (Sum.inl j))) i := rfl

@[simp]
theorem bracket_apply_inr (x y : LieVec) (i : I3) :
    bracket x y (Sum.inr i) =
      ((fun j ↦ x (Sum.inr j)) ⨯₃ (fun j ↦ y (Sum.inr j))) i := rfl

/-- A left-invariant metric, encoded by its Gram matrix at the identity. -/
structure LeftInvariantMetric where
  gram : Mat6
  posDef : gram.PosDef

namespace LeftInvariantMetric

theorem isHermitian (g : LeftInvariantMetric) : g.gram.IsHermitian :=
  g.posDef.isHermitian

end LeftInvariantMetric

/-! ## Metrics obtained from an orthonormal frame -/

/-- The metric for which the rows of an invertible coefficient matrix `C` are
orthonormal in the fixed background basis.  Its Gram matrix is
`(Cᵀ C)⁻¹`. -/
noncomputable def metricOfFrame (C : Mat6) (hC : C.det ≠ 0) :
    LeftInvariantMetric where
  gram := (Cᵀ * C)⁻¹
  posDef := by
    have hunitDet : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
    have hunit : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr hunitDet
    have hinj : Function.Injective C.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr hunit
    have hpd := Matrix.PosDef.conjTranspose_mul_self C hinj
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hpd
    exact hpd.inv

/-- Passing from an invertible frame to its metric does not introduce any
geometric assumption: the inverse co-metric is exactly `Cᵀ C`. -/
@[simp]
theorem metricOfFrame_gram (C : Mat6) (hC : C.det ≠ 0) :
    (metricOfFrame C hC).gram = (Cᵀ * C)⁻¹ := rfl

/-- The co-metric of a frame metric is the Gram matrix of the frame
coefficients.  This is the cancellation used throughout both coordinate
proofs. -/
@[simp]
theorem metricOfFrame_gram_inv (C : Mat6) (hC : C.det ≠ 0) :
    (metricOfFrame C hC).gram⁻¹ = Cᵀ * C := by
  have hunitDet : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  have hunitC : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr hunitDet
  have hunitCt : IsUnit Cᵀ := (Matrix.isUnit_transpose C).2 hunitC
  have hunitCtC : IsUnit (Cᵀ * C) := hunitCt.mul hunitC
  letI : Invertible (Cᵀ * C) := hunitCtC.invertible
  exact Matrix.inv_inv_of_invertible (Cᵀ * C)

@[ext]
theorem LeftInvariantMetric.ext {g h : LeftInvariantMetric}
    (hgram : g.gram = h.gram) : g = h := by
  cases g
  cases h
  simp_all

theorem LeftInvariantMetric.ext_of_inv_eq {g h : LeftInvariantMetric}
    (hinv : g.gram⁻¹ = h.gram⁻¹) : g = h := by
  apply LeftInvariantMetric.ext
  letI : Invertible g.gram := g.posDef.isUnit.invertible
  letI : Invertible h.gram := h.posDef.isUnit.invertible
  have hi := congrArg (fun M : Mat6 ↦ M⁻¹) hinv
  simpa using hi

/-- Evaluation of the metric at the identity on coordinate vectors. -/
def metricInner (g : LeftInvariantMetric) (x y : LieVec) : ℝ :=
  x ⬝ᵥ (g.gram *ᵥ y)

/-- Coordinate vector in the fixed basis of `ℝ³ ⊕ ℝ³`. -/
def basisVec (i : I6) : LieVec := fun j ↦ if j = i then 1 else 0

/-- Structure constants of the fixed `su(2) ⊕ su(2)` bracket. -/
def structureConstant (i j k : I6) : ℝ := bracket (basisVec i) (basisVec j) k

/-- The bracket with its output index lowered using the metric. -/
def loweredBracket (g : LeftInvariantMetric) (i j k : I6) : ℝ :=
  ∑ m, structureConstant i j m * g.gram m k

/-- Koszul's formula for left-invariant vector fields, with the last index lowered. -/
noncomputable def koszulLower (g : LeftInvariantMetric) (i j k : I6) : ℝ :=
  (loweredBracket g i j k - loweredBracket g j k i + loweredBracket g k i j) / 2

/-- Christoffel coefficients of the Levi-Civita connection in the fixed basis. -/
noncomputable def christoffel (g : LeftInvariantMetric) (i j k : I6) : ℝ :=
  ∑ l, (g.gram⁻¹) k l * koszulLower g i j l

/-- Curvature coefficients, using `R(X,Y)Z = ∇X∇Y Z - ∇Y∇X Z - ∇[X,Y] Z`. -/
noncomputable def curvatureComponent
    (g : LeftInvariantMetric) (i j k n : I6) : ℝ :=
  (∑ m, christoffel g j k m * christoffel g i m n) -
  (∑ m, christoffel g i k m * christoffel g j m n) -
  ∑ m, structureConstant i j m * christoffel g m k n

/-- Ricci tensor of the left-invariant metric, computed entirely at the Lie algebra level. -/
noncomputable def ricci (g : LeftInvariantMetric) : Mat6 :=
  fun j k ↦ ∑ i, curvatureComponent g i j k i

/-- The genuine Einstein equation in the algebraic model of a left-invariant metric. -/
def Einstein (g : LeftInvariantMetric) : Prop :=
  ∃ einsteinConstant : ℝ, ricci g = einsteinConstant • g.gram

/-- The block diagonal derivative of an inner automorphism. -/
def innerMatrix (a : InnerAction) : Mat6 :=
  Matrix.fromBlocks (a.1 : Mat3) 0 0 (a.2 : Mat3)

theorem innerMatrix_mul_transpose (a : InnerAction) :
    innerMatrix a * (innerMatrix a)ᵀ = 1 := by
  have ha : (a.1 : Mat3) * (a.1 : Mat3)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp a.1.property).1
  have hb : (a.2 : Mat3) * (a.2 : Mat3)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp a.2.property).1
  rw [innerMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp [ha, hb]

theorem innerMatrix_transpose_mul (a : InnerAction) :
    (innerMatrix a)ᵀ * innerMatrix a = 1 := by
  have ha : (a.1 : Mat3)ᵀ * (a.1 : Mat3) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp a.1.property).1
  have hb : (a.2 : Mat3)ᵀ * (a.2 : Mat3) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp a.2.property).1
  rw [innerMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp [ha, hb]

@[simp]
theorem innerMatrix_one : innerMatrix (1 : InnerAction) = 1 := by
  simp [innerMatrix]

@[simp]
theorem innerMatrix_mul (a b : InnerAction) :
    innerMatrix (a * b) = innerMatrix a * innerMatrix b := by
  ext i j
  cases i <;> cases j <;> simp [innerMatrix, Matrix.mul_apply]

/-- Pull a metric back by an inner automorphism.  The definition is entirely
at the identity, where the derivative is `innerMatrix a`. -/
noncomputable def pullbackMetric (a : InnerAction) (g : LeftInvariantMetric) :
    LeftInvariantMetric where
  gram := (innerMatrix a)ᵀ * g.gram * innerMatrix a
  posDef := by
    have hunit : IsUnit (innerMatrix a) :=
      IsUnit.of_mul_eq_one (innerMatrix a)ᵀ (innerMatrix_mul_transpose a)
    have hinj : Function.Injective (innerMatrix a).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr hunit
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      g.posDef.conjTranspose_mul_mul_same hinj

@[simp]
theorem pullbackMetric_gram (a : InnerAction) (g : LeftInvariantMetric) :
    (pullbackMetric a g).gram =
      (innerMatrix a)ᵀ * g.gram * innerMatrix a := rfl

@[simp]
theorem pullbackMetric_gram_inv (a : InnerAction) (g : LeftInvariantMetric) :
    (pullbackMetric a g).gram⁻¹ =
      (innerMatrix a)ᵀ * g.gram⁻¹ * innerMatrix a := by
  let T : Mat6 := innerMatrix a
  have hTT : T * Tᵀ = 1 := innerMatrix_mul_transpose a
  have hTtT : Tᵀ * T = 1 := innerMatrix_transpose_mul a
  have hinvT : T⁻¹ = Tᵀ := Matrix.inv_eq_right_inv hTT
  have hinvTt : Tᵀ⁻¹ = T := Matrix.inv_eq_right_inv hTtT
  change (Tᵀ * g.gram * T)⁻¹ = Tᵀ * g.gram⁻¹ * T
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hinvT, hinvTt]
  noncomm_ring

@[simp]
theorem pullbackMetric_one (g : LeftInvariantMetric) : pullbackMetric 1 g = g := by
  apply LeftInvariantMetric.ext
  simp [pullbackMetric]

/-- An inner action fixes a metric when its derivative is an isometry at the identity. -/
def Fixes (a : InnerAction) (g : LeftInvariantMetric) : Prop :=
  (innerMatrix a)ᵀ * g.gram * innerMatrix a = g.gram

/-- A fixed positive metric has a fixed co-metric. -/
theorem fixes_cometric {a : InnerAction} {g : LeftInvariantMetric}
    (hfix : Fixes a g) :
    (innerMatrix a)ᵀ * g.gram⁻¹ * innerMatrix a = g.gram⁻¹ := by
  let T : Mat6 := innerMatrix a
  have hTT : T * Tᵀ = 1 := innerMatrix_mul_transpose a
  have hTtT : Tᵀ * T = 1 := innerMatrix_transpose_mul a
  have hinvT : T⁻¹ = Tᵀ := Matrix.inv_eq_right_inv hTT
  have hinvTt : Tᵀ⁻¹ = T := Matrix.inv_eq_right_inv hTtT
  rw [Fixes] at hfix
  have hinv := congrArg (fun M : Mat6 ↦ M⁻¹) hfix
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hinvT, hinvTt] at hinv
  simpa only [T, Matrix.mul_assoc] using hinv

theorem fixes_conjugate_iff (a b : InnerAction) (g : LeftInvariantMetric) :
    Fixes (a * b * a⁻¹) g ↔ Fixes b (pullbackMetric a g) := by
  let A : Mat6 := innerMatrix a
  let B : Mat6 := innerMatrix b
  let Ai : Mat6 := innerMatrix a⁻¹
  have hAAi : A * Ai = 1 := by
    change innerMatrix a * innerMatrix a⁻¹ = 1
    rw [← innerMatrix_mul]
    simp
  have hAiA : Ai * A = 1 := by
    change innerMatrix a⁻¹ * innerMatrix a = 1
    rw [← innerMatrix_mul]
    simp
  have hAAit : Aiᵀ * Aᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose hAAi
  have hAiAt : Aᵀ * Aiᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose hAiA
  constructor
  · intro h
    rw [Fixes, innerMatrix_mul, innerMatrix_mul] at h
    change (A * B * Ai)ᵀ * g.gram * (A * B * Ai) = g.gram at h
    rw [Matrix.transpose_mul, Matrix.transpose_mul] at h
    rw [Fixes]
    change Bᵀ * (Aᵀ * g.gram * A) * B = Aᵀ * g.gram * A
    have hh := congrArg (fun X : Mat6 ↦ Aᵀ * X * A) h
    calc
      Bᵀ * (Aᵀ * g.gram * A) * B =
          Aᵀ * ((Aiᵀ * Bᵀ * Aᵀ) * g.gram * (A * B * Ai)) * A := by
            calc
              _ = (Aᵀ * Aiᵀ) * Bᵀ * (Aᵀ * g.gram * A) * B *
                    (Ai * A) := by rw [hAiAt, hAiA]; simp
              _ = _ := by noncomm_ring
      _ = Aᵀ * g.gram * A := by
        simpa only [Matrix.mul_assoc] using hh
  · intro h
    rw [Fixes] at h
    change Bᵀ * (Aᵀ * g.gram * A) * B = Aᵀ * g.gram * A at h
    rw [Fixes, innerMatrix_mul, innerMatrix_mul]
    change (A * B * Ai)ᵀ * g.gram * (A * B * Ai) = g.gram
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    have hh := congrArg (fun X : Mat6 ↦ Aiᵀ * X * Ai) h
    calc
      Aiᵀ * (Bᵀ * Aᵀ) * g.gram * (A * B * Ai) =
          Aiᵀ * (Bᵀ * (Aᵀ * g.gram * A) * B) * Ai := by
            noncomm_ring
      _ = Aiᵀ * (Aᵀ * g.gram * A) * Ai := by
        simpa only [Matrix.mul_assoc] using hh
      _ = g.gram := by
        calc
          _ = (Aiᵀ * Aᵀ) * g.gram * (A * Ai) := by noncomm_ring
          _ = g.gram := by rw [hAAit, hAAi]; simp

/-- An orthogonal congruence fixes an invertible co-metric exactly as it fixes
the inverse metric.  This is the algebraic bridge used when a normal-frame
calculation is carried out on `Cᵀ C`. -/
theorem fixes_metricOfFrame_of_fixes_cometric
    (a : InnerAction) (C : Mat6) (hC : C.det ≠ 0)
    (hfix : (innerMatrix a)ᵀ * (Cᵀ * C) * innerMatrix a = Cᵀ * C) :
    Fixes a (metricOfFrame C hC) := by
  let T : Mat6 := innerMatrix a
  have hTT : T * Tᵀ = 1 := innerMatrix_mul_transpose a
  have hTtT : Tᵀ * T = 1 := innerMatrix_transpose_mul a
  have hinvT : T⁻¹ = Tᵀ := Matrix.inv_eq_right_inv hTT
  have hinvTt : Tᵀ⁻¹ = T := Matrix.inv_eq_right_inv hTtT
  have hinv := congrArg (fun M : Mat6 ↦ M⁻¹) hfix
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hinvT, hinvTt] at hinv
  simpa only [Fixes, metricOfFrame_gram, T, Matrix.mul_assoc] using hinv

@[simp]
theorem fixes_one (g : LeftInvariantMetric) : Fixes 1 g := by
  simp [Fixes]

theorem fixes_mul {a b : InnerAction} {g : LeftInvariantMetric}
    (ha : Fixes a g) (hb : Fixes b g) : Fixes (a * b) g := by
  rw [Fixes, innerMatrix_mul, Matrix.transpose_mul]
  rw [Fixes] at ha hb
  change
    ((innerMatrix b)ᵀ * (innerMatrix a)ᵀ) * g.gram *
        (innerMatrix a * innerMatrix b) = g.gram
  calc
    ((innerMatrix b)ᵀ * (innerMatrix a)ᵀ) * g.gram *
          (innerMatrix a * innerMatrix b) =
        (innerMatrix b)ᵀ * ((innerMatrix a)ᵀ * g.gram * innerMatrix a) *
          innerMatrix b := by noncomm_ring
    _ = (innerMatrix b)ᵀ * g.gram * innerMatrix b := by rw [ha]
    _ = g.gram := hb

theorem fixes_inv {a : InnerAction} {g : LeftInvariantMetric} (ha : Fixes a g) :
    Fixes a⁻¹ g := by
  have hleft : innerMatrix a⁻¹ * innerMatrix a = 1 := by
    rw [← innerMatrix_mul]
    simp
  have hright : innerMatrix a * innerMatrix a⁻¹ = 1 := by
    rw [← innerMatrix_mul]
    simp
  have htranspose : (innerMatrix a⁻¹)ᵀ * (innerMatrix a)ᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose hright
  rw [Fixes] at ha ⊢
  calc
    (innerMatrix a⁻¹)ᵀ * g.gram * innerMatrix a⁻¹ =
        (innerMatrix a⁻¹)ᵀ *
          ((innerMatrix a)ᵀ * g.gram * innerMatrix a) * innerMatrix a⁻¹ := by
            rw [ha]
    _ = ((innerMatrix a⁻¹)ᵀ * (innerMatrix a)ᵀ) * g.gram *
          (innerMatrix a * innerMatrix a⁻¹) := by noncomm_ring
    _ = g.gram := by rw [htranspose, hright]; simp

/-- The inner isotropy `K(g)`, represented inside `SO(3) × SO(3)`. -/
def innerIsotropy (g : LeftInvariantMetric) : Subgroup InnerAction where
  carrier := {a | Fixes a g}
  one_mem' := fixes_one g
  mul_mem' := fixes_mul
  inv_mem' := fixes_inv

@[simp]
theorem mem_innerIsotropy_iff {g : LeftInvariantMetric} {a : InnerAction} :
    a ∈ innerIsotropy g ↔ Fixes a g := Iff.rfl

/-- The concrete formulation of `K(g) ≠ {e}` used by the first theorem. -/
def HasNontrivialInnerIsotropy (g : LeftInvariantMetric) : Prop :=
  ∃ a : InnerAction, a ≠ 1 ∧ Fixes a g

/-- `K(g)` contains a subgroup of order four and exponent two.  Mathlib's
`IsKleinFour` mixin makes the phrase “a Klein four subgroup” literal rather
than encoding it only by a list of four matrices. -/
def ContainsKleinFour (g : LeftInvariantMetric) : Prop :=
  ∃ H : Subgroup (innerIsotropy g), IsKleinFour H

theorem hasNontrivialInnerIsotropy_iff (g : LeftInvariantMetric) :
    HasNontrivialInnerIsotropy g ↔ innerIsotropy g ≠ ⊥ := by
  constructor
  · rintro ⟨a, ha, hfix⟩
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨a, hfix⟩, fun h ↦ ha (congrArg Subtype.val h)⟩
  · intro h
    rw [Subgroup.ne_bot_iff_exists_ne_one] at h
    obtain ⟨a, ha⟩ := h
    refine ⟨a, ?_, a.property⟩
    intro hav
    apply ha
    apply Subtype.ext
    exact hav

end S3xS3
