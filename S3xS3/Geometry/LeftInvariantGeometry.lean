import S3xS3.Geometry.MatrixLieAlgebra

/-!
# Left-invariant metrics, Ricci curvature, and inner isotropy

This is the end-to-end bridge between the concrete matrix group
`SU(2) × SU(2)` and the coordinate objects in `S3xS3.Core`.

* A left-invariant metric is a positive-definite symmetric bilinear form on
  the actual product Lie algebra.
* The metric field in left-trivialized tangent coordinates and its left
  invariance are explicit.
* Structure constants, Koszul coefficients, curvature, and Ricci are rebuilt
  from the actual matrix commutator and proved equal to the coordinate
  definitions.
* The literal conjugation range in `MulAut` is used for `Inn(G)`, and its
  metric stabilizer is proved equivalent to the coordinate `innerIsotropy`.
-/

open scoped Matrix BigOperators

namespace S3xS3.Geometry

noncomputable section

/-- The basis of the actual product Lie algebra transported from the six
fixed coordinate vectors. -/
def actualLieBasis : Module.Basis I6 ℝ MatrixS3xS3LieAlgebra :=
  (Pi.basisFun ℝ I6).map lieVecEquivMatrixProduct

lemma actualLieBasis_apply (i : I6) :
    actualLieBasis i = lieVecEquivMatrixProduct (basisVec i) := by
  apply lieVecEquivMatrixProduct.symm.injective
  funext j
  simp [actualLieBasis, basisVec, Pi.single_apply, eq_comm]

/-- A left-invariant Riemannian metric on matrix
`SU(2) × SU(2)`, represented intrinsically by its positive-definite inner
product on the actual Lie algebra at the identity. -/
structure MatrixGroupLeftInvariantMetric where
  inner : LinearMap.BilinForm ℝ MatrixS3xS3LieAlgebra
  symmetric : inner.IsSymm
  positive : inner.toQuadraticMap.PosDef

namespace MatrixGroupLeftInvariantMetric


lemma actualLieBasis_repr_apply (x : LieVec) (i : I6) :
    (actualLieBasis.repr (lieVecEquivMatrixProduct x)) i = x i := by
  rw [actualLieBasis, Module.Basis.map_repr]
  simp

/-- The Gram matrix in the rigorously identified product Lie-algebra basis. -/
def coordinateGram (g : MatrixGroupLeftInvariantMetric) : Mat6 :=
  g.inner.toMatrix actualLieBasis

theorem coordinateGram_posDef (g : MatrixGroupLeftInvariantMetric) :
    g.coordinateGram.PosDef :=
  (g.inner.posDef_toQuadraticMap_iff_matrix actualLieBasis g.symmetric).mp
    g.positive

/-- Send an actual left-invariant metric to the coordinate metric used by the
two algebraic proof files. -/
def toCoordinateMetric (g : MatrixGroupLeftInvariantMetric) :
    LeftInvariantMetric :=
  ⟨g.coordinateGram, g.coordinateGram_posDef⟩

theorem inner_eq_metricInner (g : MatrixGroupLeftInvariantMetric)
    (x y : LieVec) :
    g.inner (lieVecEquivMatrixProduct x)
        (lieVecEquivMatrixProduct y) =
      metricInner g.toCoordinateMetric x y := by
  rw [← Matrix.toBilin_toMatrix actualLieBasis g.inner]
  simp only [Matrix.toBilin_apply, actualLieBasis_repr_apply,
    metricInner, toCoordinateMetric, coordinateGram, Matrix.mulVec,
    dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Reconstruct the actual identity inner product from a coordinate Gram
matrix. -/
def ofCoordinateMetric (g : LeftInvariantMetric) :
    MatrixGroupLeftInvariantMetric where
  inner := Matrix.toBilin actualLieBasis g.gram
  symmetric := by
    rw [Matrix.isSymm_toBilin_iff_isSymm]
    exact Matrix.isHermitian_iff_isSymm.mp g.isHermitian
  positive := by
    let B : LinearMap.BilinForm ℝ MatrixS3xS3LieAlgebra :=
      Matrix.toBilin actualLieBasis g.gram
    have hsymm : B.IsSymm := by
      rw [Matrix.isSymm_toBilin_iff_isSymm]
      exact Matrix.isHermitian_iff_isSymm.mp g.isHermitian
    rw [B.posDef_toQuadraticMap_iff_matrix actualLieBasis hsymm]
    simpa [B] using g.posDef

@[simp] theorem toCoordinateMetric_ofCoordinateMetric (g : LeftInvariantMetric) :
    (ofCoordinateMetric g).toCoordinateMetric = g := by
  apply LeftInvariantMetric.ext
  exact LinearMap.BilinForm.toMatrix_toBilin actualLieBasis g.gram

@[ext] theorem ext {g h : MatrixGroupLeftInvariantMetric}
    (hinner : g.inner = h.inner) : g = h := by
  cases g
  cases h
  simp_all

@[simp] theorem ofCoordinateMetric_toCoordinateMetric
    (g : MatrixGroupLeftInvariantMetric) :
    ofCoordinateMetric g.toCoordinateMetric = g := by
  apply ext
  exact Matrix.toBilin_toMatrix actualLieBasis g.inner

/-- Actual left-invariant metrics and positive Gram matrices are equivalent,
not merely related by a one-way encoding. -/
def equivCoordinateMetric :
    MatrixGroupLeftInvariantMetric ≃ LeftInvariantMetric where
  toFun := toCoordinateMetric
  invFun := ofCoordinateMetric
  left_inv := ofCoordinateMetric_toCoordinateMetric
  right_inv := toCoordinateMetric_ofCoordinateMetric

/-! ## Left trivialization and left invariance -/

/-- Tangent vectors at a point, expressed by the differential of left
translation back to the identity. -/
abbrev TangentAt (_p : MatrixS3xS3) := MatrixS3xS3LieAlgebra

/-- In left-trivialized coordinates, the differential of left translation is
the identity on the Lie-algebra coordinate. -/
def leftTranslationDifferential (a p : MatrixS3xS3) :
    TangentAt p →ₗ[ℝ] TangentAt (a * p) := LinearMap.id

/-- The Riemannian metric at every point, obtained by left translating its
identity inner product. -/
def metricAt (g : MatrixGroupLeftInvariantMetric) (p : MatrixS3xS3)
    (X Y : TangentAt p) : ℝ := g.inner X Y

/-- The preceding metric field is left invariant, with no suppressed
change-of-tangent-coordinate step. -/
theorem metricAt_left_invariant (g : MatrixGroupLeftInvariantMetric)
    (a p : MatrixS3xS3) (X Y : TangentAt p) :
    g.metricAt (a * p) (leftTranslationDifferential a p X)
        (leftTranslationDifferential a p Y) = g.metricAt p X Y := rfl

/-! ## Koszul, curvature, and Ricci in the actual Lie algebra -/

/-- Structure constants computed from the actual matrix commutator in
the transported basis. -/
def actualStructureConstant (i j k : I6) : ℝ :=
  (actualLieBasis.repr
    (matrixProductLieBracket (actualLieBasis i) (actualLieBasis j))) k

theorem actualStructureConstant_eq_coordinate (i j k : I6) :
    actualStructureConstant i j k = structureConstant i j k := by
  rw [actualStructureConstant, actualLieBasis_apply, actualLieBasis_apply,
    lieVecEquivMatrixProduct_bracket,
    actualLieBasis_repr_apply]
  rfl

/-- The actual bracket with its last index lowered by the actual metric. -/
def actualLoweredBracket (g : MatrixGroupLeftInvariantMetric)
    (i j k : I6) : ℝ :=
  g.inner
    (matrixProductLieBracket (actualLieBasis i) (actualLieBasis j))
    (actualLieBasis k)

theorem actualLoweredBracket_eq_coordinate
    (g : MatrixGroupLeftInvariantMetric) (i j k : I6) :
    actualLoweredBracket g i j k =
      loweredBracket g.toCoordinateMetric i j k := by
  rw [actualLoweredBracket, actualLieBasis_apply, actualLieBasis_apply,
    actualLieBasis_apply,
    lieVecEquivMatrixProduct_bracket, inner_eq_metricInner]
  simp [metricInner, loweredBracket, structureConstant, basisVec,
    Matrix.mulVec, dotProduct]

/-- Koszul's formula with the last index lowered, now stated solely using the
actual Lie bracket and actual inner product. -/
noncomputable def actualKoszulLower (g : MatrixGroupLeftInvariantMetric)
    (i j k : I6) : ℝ :=
  (actualLoweredBracket g i j k - actualLoweredBracket g j k i +
    actualLoweredBracket g k i j) / 2

theorem actualKoszulLower_eq_coordinate
    (g : MatrixGroupLeftInvariantMetric) (i j k : I6) :
    actualKoszulLower g i j k =
      koszulLower g.toCoordinateMetric i j k := by
  simp [actualKoszulLower, koszulLower, actualLoweredBracket_eq_coordinate]

/-- Levi-Civita connection coefficients obtained by raising the last Koszul
index with the inverse actual Gram matrix. -/
noncomputable def actualChristoffel (g : MatrixGroupLeftInvariantMetric)
    (i j k : I6) : ℝ :=
  ∑ l, g.coordinateGram⁻¹ k l * actualKoszulLower g i j l

theorem actualChristoffel_eq_coordinate
    (g : MatrixGroupLeftInvariantMetric) (i j k : I6) :
    actualChristoffel g i j k =
      christoffel g.toCoordinateMetric i j k := by
  simp [actualChristoffel, christoffel, actualKoszulLower_eq_coordinate,
    toCoordinateMetric, coordinateGram]

/-- Curvature coefficients obtained from the actual connection and actual
structure constants. -/
noncomputable def actualCurvatureComponent
    (g : MatrixGroupLeftInvariantMetric) (i j k n : I6) : ℝ :=
  (∑ m, actualChristoffel g j k m * actualChristoffel g i m n) -
  (∑ m, actualChristoffel g i k m * actualChristoffel g j m n) -
  ∑ m, actualStructureConstant i j m * actualChristoffel g m k n

theorem actualCurvatureComponent_eq_coordinate
    (g : MatrixGroupLeftInvariantMetric) (i j k n : I6) :
    actualCurvatureComponent g i j k n =
      curvatureComponent g.toCoordinateMetric i j k n := by
  simp [actualCurvatureComponent, curvatureComponent,
    actualChristoffel_eq_coordinate, actualStructureConstant_eq_coordinate]

/-- Ricci matrix of the actual left-invariant metric, obtained by tracing the
actual curvature tensor. -/
noncomputable def actualRicciMatrix
    (g : MatrixGroupLeftInvariantMetric) : Mat6 :=
  fun j k ↦ ∑ i, actualCurvatureComponent g i j k i

theorem actualRicciMatrix_eq_coordinate
    (g : MatrixGroupLeftInvariantMetric) :
    actualRicciMatrix g = ricci g.toCoordinateMetric := by
  ext j k
  simp [actualRicciMatrix, ricci, actualCurvatureComponent_eq_coordinate]

/-- The Ricci bilinear form on the actual Lie algebra. -/
noncomputable def actualRicciForm
    (g : MatrixGroupLeftInvariantMetric) :
    LinearMap.BilinForm ℝ MatrixS3xS3LieAlgebra :=
  Matrix.toBilin actualLieBasis g.actualRicciMatrix

theorem actualRicciForm_toMatrix (g : MatrixGroupLeftInvariantMetric) :
    g.actualRicciForm.toMatrix actualLieBasis =
      ricci g.toCoordinateMetric := by
  rw [actualRicciForm, LinearMap.BilinForm.toMatrix_toBilin,
    actualRicciMatrix_eq_coordinate]

/-- The genuine Einstein equation for the actual matrix group: equality of
the Ricci and metric bilinear forms on its Lie algebra. -/
def Einstein (g : MatrixGroupLeftInvariantMetric) : Prop :=
  ∃ einsteinConstant : ℝ,
    g.actualRicciForm = einsteinConstant • g.inner

theorem einstein_iff_coordinate (g : MatrixGroupLeftInvariantMetric) :
    g.Einstein ↔ S3xS3.Einstein g.toCoordinateMetric := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h := congrArg
      (fun B : LinearMap.BilinForm ℝ MatrixS3xS3LieAlgebra ↦
        B.toMatrix actualLieBasis) hc
    simpa [actualRicciForm_toMatrix, toCoordinateMetric, coordinateGram] using h
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply (LinearMap.BilinForm.toMatrix actualLieBasis).injective
    simpa [actualRicciForm_toMatrix, toCoordinateMetric, coordinateGram] using hc

/-! ## Literal inner automorphisms and the inner-isometry intersection -/

/-- Differential on the actual Lie algebra of an element of the literal
inner-automorphism group.  The defining action is transported through the
proved equivalence `Inn(SU(2) × SU(2)) ≃ SO(3) × SO(3)`. -/
def innerAutomorphismDerivative
    (phi : MatrixS3xS3InnerAutomorphismGroup) :
    MatrixS3xS3LieAlgebra →ₗ[ℝ] MatrixS3xS3LieAlgebra :=
  lieVecEquivMatrixProduct.toLinearMap.comp
    ((Matrix.toLin'
      (innerMatrix (matrixS3xS3InnerAutomorphismEquivInnerAction phi))).comp
        lieVecEquivMatrixProduct.symm.toLinearMap)

@[simp] theorem innerAutomorphismDerivative_apply_coordinate
    (phi : MatrixS3xS3InnerAutomorphismGroup) (x : LieVec) :
    innerAutomorphismDerivative phi (lieVecEquivMatrixProduct x) =
      lieVecEquivMatrixProduct
        (innerMatrix (matrixS3xS3InnerAutomorphismEquivInnerAction phi) *ᵥ x) := by
  simp [innerAutomorphismDerivative, Matrix.toLin'_apply]

/-- For a specified conjugating element, the abstract derivative attached to
the literal conjugation range is exactly componentwise matrix conjugation on
the traceless skew-Hermitian Lie algebra. -/
theorem innerAutomorphismDerivative_conjugationRangeElement
    (U : MatrixS3xS3) (X : MatrixS3xS3LieAlgebra) :
    innerAutomorphismDerivative
        (matrixS3xS3ConjugationRangeElement U) X =
      matrixProductConjugationDerivativeLie U X := by
  let x : LieVec := lieVecEquivMatrixProduct.symm X
  have hx : lieVecEquivMatrixProduct x = X := by simp [x]
  rw [← hx, innerAutomorphismDerivative_apply_coordinate,
    matrixProductConjugationDerivativeLie_equivariant,
    matrixS3xS3InnerAutomorphismEquivInnerAction_conjugationRangeElement]

/-- Every literal inner automorphism has a concrete conjugating matrix, and
its derivative is the corresponding literal matrix-conjugation map. -/
theorem innerAutomorphismDerivative_is_matrix_conjugation
    (phi : MatrixS3xS3InnerAutomorphismGroup) :
    ∃ U : MatrixS3xS3,
      (phi : MulAut MatrixS3xS3) = MulAut.conj U ∧
      ∀ X : MatrixS3xS3LieAlgebra,
        innerAutomorphismDerivative phi X =
          matrixProductConjugationDerivativeLie U X := by
  obtain ⟨U, hU⟩ := phi.property
  have hphi : phi = matrixS3xS3ConjugationRangeElement U := by
    apply Subtype.ext
    exact hU.symm
  refine ⟨U, hU.symm, ?_⟩
  intro X
  rw [hphi]
  exact innerAutomorphismDerivative_conjugationRangeElement U X

theorem innerAutomorphismDerivative_toMatrix
    (phi : MatrixS3xS3InnerAutomorphismGroup) :
    LinearMap.toMatrix actualLieBasis actualLieBasis
      (innerAutomorphismDerivative phi) =
        innerMatrix (matrixS3xS3InnerAutomorphismEquivInnerAction phi) := by
  ext i j
  rw [LinearMap.toMatrix_apply, actualLieBasis_apply,
    innerAutomorphismDerivative_apply_coordinate,
    actualLieBasis_repr_apply]
  simp only [Matrix.mulVec, dotProduct]
  simp [basisVec]

/-- Differential of an inner automorphism at an arbitrary point, written in
left-trivialized tangent coordinates.  For a group automorphism this is the
same Lie-algebra map at every point. -/
def innerAutomorphismDifferentialAt
    (phi : MatrixS3xS3InnerAutomorphismGroup) (p : MatrixS3xS3) :
    TangentAt p →ₗ[ℝ]
      TangentAt ((phi : MulAut MatrixS3xS3) p) :=
  innerAutomorphismDerivative phi

/-- The literal global isometry condition for an inner automorphism, stated
at every group point and on every pair of tangent vectors in the explicit
left trivialization. -/
def IsInnerIsometry (phi : MatrixS3xS3InnerAutomorphismGroup)
    (g : MatrixGroupLeftInvariantMetric) : Prop :=
  ∀ (p : MatrixS3xS3) (X Y : TangentAt p),
    g.metricAt ((phi : MulAut MatrixS3xS3) p)
        (innerAutomorphismDifferentialAt phi p X)
        (innerAutomorphismDifferentialAt phi p Y) =
      g.metricAt p X Y

/-- A literal inner automorphism is an isometry exactly when its differential
preserves the actual identity inner product. -/
def Fixes (phi : MatrixS3xS3InnerAutomorphismGroup)
    (g : MatrixGroupLeftInvariantMetric) : Prop :=
  g.inner.comp (innerAutomorphismDerivative phi)
      (innerAutomorphismDerivative phi) = g.inner

/-- For a left-invariant metric, an inner automorphism is a global isometry
if and only if its derivative preserves the identity inner product. -/
theorem isInnerIsometry_iff_fixes
    (phi : MatrixS3xS3InnerAutomorphismGroup)
    (g : MatrixGroupLeftInvariantMetric) :
    IsInnerIsometry phi g ↔ Fixes phi g := by
  constructor
  · intro h
    rw [Fixes]
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro Y
    simpa [IsInnerIsometry, metricAt,
      innerAutomorphismDifferentialAt] using h 1 X Y
  · intro h p X Y
    rw [Fixes] at h
    have hXY := congrArg
      (fun B : LinearMap.BilinForm ℝ MatrixS3xS3LieAlgebra ↦ B X Y) h
    simpa [metricAt, innerAutomorphismDifferentialAt] using hXY

theorem fixes_iff_coordinate
    (phi : MatrixS3xS3InnerAutomorphismGroup)
    (g : MatrixGroupLeftInvariantMetric) :
    Fixes phi g ↔
      S3xS3.Fixes
        (matrixS3xS3InnerAutomorphismEquivInnerAction phi)
        g.toCoordinateMetric := by
  constructor
  · intro h
    have hm := congrArg
      (fun B : LinearMap.BilinForm ℝ MatrixS3xS3LieAlgebra ↦
        B.toMatrix actualLieBasis) h
    rw [LinearMap.BilinForm.toMatrix_comp
        (b := actualLieBasis) (c := actualLieBasis),
      innerAutomorphismDerivative_toMatrix] at hm
    exact hm
  · intro h
    apply (LinearMap.BilinForm.toMatrix actualLieBasis).injective
    rw [LinearMap.BilinForm.toMatrix_comp
        (b := actualLieBasis) (c := actualLieBasis),
      innerAutomorphismDerivative_toMatrix]
    exact h

/-- The literal intersection `K(g) = Isom(G,g) ∩ Inn(G)`, represented as
a subgroup of the literal conjugation range.  The preceding theorem proves
the usual identity-differential isometry criterion used in this definition. -/
def innerIsotropy (g : MatrixGroupLeftInvariantMetric) :
    Subgroup MatrixS3xS3InnerAutomorphismGroup :=
  (S3xS3.innerIsotropy g.toCoordinateMetric).comap
    matrixS3xS3InnerAutomorphismEquivInnerAction.toMonoidHom

@[simp] theorem mem_innerIsotropy_iff
    {g : MatrixGroupLeftInvariantMetric}
    {phi : MatrixS3xS3InnerAutomorphismGroup} :
    phi ∈ g.innerIsotropy ↔ Fixes phi g := by
  change S3xS3.Fixes
      (matrixS3xS3InnerAutomorphismEquivInnerAction phi)
        g.toCoordinateMetric ↔ Fixes phi g
  exact (fixes_iff_coordinate phi g).symm

/-- Membership in `K(g)` is exactly the global isometry condition, so the
subgroup really is `Isom(G,g) ∩ Inn(G)` viewed inside `Inn(G)`. -/
theorem mem_innerIsotropy_iff_isInnerIsometry
    {g : MatrixGroupLeftInvariantMetric}
    {phi : MatrixS3xS3InnerAutomorphismGroup} :
    phi ∈ g.innerIsotropy ↔ IsInnerIsometry phi g := by
  exact mem_innerIsotropy_iff.trans
    (isInnerIsometry_iff_fixes phi g).symm

theorem innerIsotropy_carrier_eq_isometry_intersection
    (g : MatrixGroupLeftInvariantMetric) :
    (g.innerIsotropy : Set MatrixS3xS3InnerAutomorphismGroup) =
      {phi | IsInnerIsometry phi g} := by
  ext phi
  exact mem_innerIsotropy_iff_isInnerIsometry

/-- The actual inner-isotropy subgroup is isomorphic to the coordinate
stabilizer; no elements are added or lost by the coordinate model. -/
def innerIsotropyEquivCoordinate (g : MatrixGroupLeftInvariantMetric) :
    g.innerIsotropy ≃* S3xS3.innerIsotropy g.toCoordinateMetric where
  toFun phi := ⟨matrixS3xS3InnerAutomorphismEquivInnerAction phi,
    phi.property⟩
  invFun a := ⟨matrixS3xS3InnerAutomorphismEquivInnerAction.symm a, by
    simp [innerIsotropy]⟩
  map_mul' phi psi := by
    apply Subtype.ext
    exact matrixS3xS3InnerAutomorphismEquivInnerAction.map_mul phi psi
  left_inv phi := by
    apply Subtype.ext
    exact matrixS3xS3InnerAutomorphismEquivInnerAction.symm_apply_apply phi
  right_inv a := by
    apply Subtype.ext
    exact matrixS3xS3InnerAutomorphismEquivInnerAction.apply_symm_apply a

/-- Nontriviality of the literal intersection `K(g)`. -/
def HasNontrivialInnerIsotropy (g : MatrixGroupLeftInvariantMetric) : Prop :=
  g.innerIsotropy ≠ ⊥

/-- The literal inner-isotropy contains a subgroup of order four and exponent
two. -/
def ContainsKleinFour (g : MatrixGroupLeftInvariantMetric) : Prop :=
  ∃ H : Subgroup g.innerIsotropy, IsKleinFour H

private theorem isKleinFour_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (hG : IsKleinFour G) : IsKleinFour H := by
  letI : IsKleinFour G := hG
  constructor
  · rw [← Nat.card_congr e.toEquiv]
    exact IsKleinFour.card_four
  · rw [← Monoid.exponent_eq_of_mulEquiv e]
    exact IsKleinFour.exponent_two

theorem hasNontrivialInnerIsotropy_iff_coordinate
    (g : MatrixGroupLeftInvariantMetric) :
    g.HasNontrivialInnerIsotropy ↔
      S3xS3.HasNontrivialInnerIsotropy g.toCoordinateMetric := by
  rw [S3xS3.hasNontrivialInnerIsotropy_iff]
  change (g.innerIsotropy ≠ ⊥) ↔
    (S3xS3.innerIsotropy g.toCoordinateMetric ≠ ⊥)
  constructor
  · intro h
    rw [Subgroup.ne_bot_iff_exists_ne_one] at h ⊢
    obtain ⟨phi, hphi⟩ := h
    refine ⟨g.innerIsotropyEquivCoordinate phi, ?_⟩
    intro heq
    apply hphi
    exact g.innerIsotropyEquivCoordinate.injective (by simpa using heq)
  · intro h
    rw [Subgroup.ne_bot_iff_exists_ne_one] at h ⊢
    obtain ⟨a, ha⟩ := h
    refine ⟨g.innerIsotropyEquivCoordinate.symm a, ?_⟩
    intro heq
    apply ha
    exact g.innerIsotropyEquivCoordinate.symm.injective (by simpa using heq)

theorem containsKleinFour_of_coordinate
    (g : MatrixGroupLeftInvariantMetric)
    (h : S3xS3.ContainsKleinFour g.toCoordinateMetric) :
    g.ContainsKleinFour := by
  obtain ⟨H, hH⟩ := h
  let e := g.innerIsotropyEquivCoordinate
  let H' : Subgroup g.innerIsotropy := H.map e.symm.toMonoidHom
  let eH : H ≃* H' := e.symm.subgroupMap H
  refine ⟨H', ?_⟩
  exact isKleinFour_transport eH hH

end MatrixGroupLeftInvariantMetric

end

end S3xS3.Geometry
