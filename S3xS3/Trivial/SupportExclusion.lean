import S3xS3.Trivial.AlgebraicCertificate

open scoped Matrix BigOperators

namespace S3xS3.Trivial.Support

def jIndex : I3 → I3 := ![1, 0, 0]
def kIndex : I3 → I3 := ![2, 2, 1]

def symm3 (d x : I3 → ℝ) : Mat3 :=
  !![d 0, x 2, x 1; x 2, d 1, x 0; x 1, x 0, d 2]

def edgeCof (H : Mat3) : I3 → ℝ := ![cofEdge0 H, cofEdge1 H, cofEdge2 H]

noncomputable def edgeResidual (H : Mat3) : I3 → ℝ :=
  ![residual0 H, residual1 H, residual2 H]

def aCoeff (m : I3 → ℝ) (i : I3) : ℝ := m i ^ 2
def bCoeff (m : I3 → ℝ) (i : I3) : ℝ := 1 + aCoeff m i
def sCoeff (m : I3 → ℝ) (i : I3) : ℝ :=
  aCoeff m (jIndex i) + aCoeff m (kIndex i)
def deltaCoeff (m : I3 → ℝ) (i : I3) : ℝ := sCoeff m i + 4

def AllNonzero (x : I3 → ℝ) : Prop := ∀ i, x i ≠ 0

def TwoOfThree (P : I3 → Prop) : Prop :=
  (P 0 ∧ P 1) ∨ (P 0 ∧ P 2) ∨ (P 1 ∧ P 2)

structure CriticalData where
  m : I3 → ℝ
  p : I3 → ℝ
  q : I3 → ℝ
  x : I3 → ℝ
  y : I3 → ℝ
  sigma : ℝ
  m_ne_zero : ∀ i, m i ≠ 0
  sigma_pos : 0 < sigma
  offP : ∀ i,
    -bCoeff m i * deltaCoeff m i * x i +
        m i * sCoeff m i * y i = edgeCof (symm3 p x) i
  offQ : ∀ i,
    m i * sCoeff m i * x i - deltaCoeff m i * y i =
      sigma * edgeCof (symm3 q y) i
  noCommonAxis : ∀ i,
    ¬(x (jIndex i) = 0 ∧ x (kIndex i) = 0 ∧
      y (jIndex i) = 0 ∧ y (kIndex i) = 0)
  firstDiag : ∀ i, sigma * q i < 4
  secondDiag : ∀ i, p i / bCoeff m i < 4
  firstResidual : AllNonzero y →
    TwoOfThree (fun i ↦ sigma * edgeResidual (symm3 q y) i < 4)
  secondResidual : AllNonzero x →
    TwoOfThree (fun i ↦ edgeResidual (symm3 p x) i / bCoeff m i < 4)

lemma aCoeff_pos (d : CriticalData) (i : I3) : 0 < aCoeff d.m i := by
  exact sq_pos_of_ne_zero (d.m_ne_zero i)

lemma bCoeff_pos (d : CriticalData) (i : I3) : 0 < bCoeff d.m i := by
  dsimp [bCoeff, aCoeff]
  nlinarith [sq_nonneg (d.m i)]

lemma sCoeff_pos (d : CriticalData) (i : I3) : 0 < sCoeff d.m i := by
  dsimp [sCoeff]
  have h1 := aCoeff_pos d (jIndex i)
  have h2 := aCoeff_pos d (kIndex i)
  linarith

@[simp] lemma edgeCof_symm3 (p x : I3 → ℝ) (i : I3) :
    edgeCof (symm3 p x) i =
      x (jIndex i) * x (kIndex i) - p i * x i := by
  fin_cases i <;>
    simp [edgeCof, symm3, cofEdge0, cofEdge1, cofEdge2,
      jIndex, kIndex] <;> ring

lemma edgeCof_eq_neg_residual (p x : I3 → ℝ) (i : I3)
    (hxi : x i ≠ 0) :
    edgeCof (symm3 p x) i =
      -edgeResidual (symm3 p x) i * x i := by
  fin_cases i
  · simpa [edgeCof, edgeResidual, symm3, off0] using
      cofEdge0_eq_neg_residual (symm3 p x) hxi
  · simpa [edgeCof, edgeResidual, symm3, off1] using
      cofEdge1_eq_neg_residual (symm3 p x) hxi
  · simpa [edgeCof, edgeResidual, symm3, off2] using
      cofEdge2_eq_neg_residual (symm3 p x) hxi

noncomputable def theta (d : CriticalData) (i : I3) : ℝ :=
  d.y i / (d.m i * d.x i)

lemma theta_ne_zero (d : CriticalData) (i : I3)
    (hx : d.x i ≠ 0) (hy : d.y i ≠ 0) : theta d i ≠ 0 := by
  exact div_ne_zero hy (mul_ne_zero (d.m_ne_zero i) hx)

lemma delta_sub_four (d : CriticalData) (i : I3) :
    deltaCoeff d.m i - 4 = sCoeff d.m i := by
  simp [deltaCoeff]

lemma one_lt_b_div_a (d : CriticalData) (i : I3) :
    1 < bCoeff d.m i / aCoeff d.m i := by
  rw [lt_div_iff₀ (aCoeff_pos d i)]
  simp [bCoeff]

lemma q_residual_identity (d : CriticalData) (i : I3)
    (_hx : d.x i ≠ 0) (hy : d.y i ≠ 0) :
    d.sigma * edgeResidual (symm3 d.q d.y) i =
      deltaCoeff d.m i - sCoeff d.m i / theta d i := by
  have hcof := edgeCof_eq_neg_residual d.q d.y i hy
  have hoff := d.offQ i
  rw [hcof] at hoff
  dsimp [theta]
  field_simp [_hx, hy, d.m_ne_zero i]
  nlinarith [hoff]

lemma p_residual_identity (d : CriticalData) (i : I3)
    (hx : d.x i ≠ 0) :
    edgeResidual (symm3 d.p d.x) i / bCoeff d.m i =
      deltaCoeff d.m i -
        (aCoeff d.m i * sCoeff d.m i / bCoeff d.m i) * theta d i := by
  have hcof := edgeCof_eq_neg_residual d.p d.x i hx
  have hoff := d.offP i
  rw [hcof] at hoff
  dsimp [theta, aCoeff]
  field_simp [hx, d.m_ne_zero i, ne_of_gt (bCoeff_pos d i)]
  nlinarith [hoff]

lemma q_residual_lt_four_iff (d : CriticalData) (i : I3)
    (hx : d.x i ≠ 0) (hy : d.y i ≠ 0) :
    d.sigma * edgeResidual (symm3 d.q d.y) i < 4 ↔
      0 < theta d i ∧ theta d i < 1 := by
  rw [q_residual_identity d i hx hy]
  have htheta := theta_ne_zero d i hx hy
  have hsmall := theta_small_iff (sCoeff_pos d i) htheta
  have heq :
      (deltaCoeff d.m i - sCoeff d.m i / theta d i) - 4 =
        sCoeff d.m i * (theta d i - 1) / theta d i := by
    rw [show deltaCoeff d.m i = sCoeff d.m i + 4 by rfl]
    field_simp [htheta]
    ring
  constructor
  · intro h
    apply hsmall.mp
    rw [← heq]
    linarith
  · intro h
    have := hsmall.mpr h
    rw [← heq] at this
    linarith

lemma p_residual_lt_four_iff (d : CriticalData) (i : I3)
    (hx : d.x i ≠ 0) :
    edgeResidual (symm3 d.p d.x) i / bCoeff d.m i < 4 ↔
      bCoeff d.m i / aCoeff d.m i < theta d i := by
  rw [p_residual_identity d i hx]
  have hlarge := theta_large_iff (aCoeff_pos d i) (bCoeff_pos d i)
    (sCoeff_pos d i) (theta := theta d i)
  have heq :
      (deltaCoeff d.m i -
          (aCoeff d.m i * sCoeff d.m i / bCoeff d.m i) * theta d i) - 4 =
        sCoeff d.m i / bCoeff d.m i *
          (bCoeff d.m i - aCoeff d.m i * theta d i) := by
    rw [show deltaCoeff d.m i = sCoeff d.m i + 4 by rfl]
    field_simp [ne_of_gt (bCoeff_pos d i)]
    ring
  constructor
  · intro h
    apply hlarge.mp
    rw [← heq]
    linarith
  · intro h
    have := hlarge.mpr h
    rw [← heq] at this
    linarith

lemma y_support_of_x_zero (d : CriticalData) (i : I3)
    (hx : d.x i = 0) :
    d.y i ≠ 0 ↔ d.x (jIndex i) ≠ 0 ∧ d.x (kIndex i) ≠ 0 := by
  have hoff := d.offP i
  rw [edgeCof_symm3] at hoff
  simp [hx] at hoff
  have hcoef : d.m i * sCoeff d.m i ≠ 0 :=
    mul_ne_zero (d.m_ne_zero i) (ne_of_gt (sCoeff_pos d i))
  constructor
  · intro hy
    have hp : d.x (jIndex i) * d.x (kIndex i) ≠ 0 := by
      rw [← hoff]
      exact mul_ne_zero hcoef hy
    exact ⟨fun h ↦ hp (by simp [h]), fun h ↦ hp (by simp [h])⟩
  · rintro ⟨hj, hk⟩ hy
    have hp : d.x (jIndex i) * d.x (kIndex i) ≠ 0 := mul_ne_zero hj hk
    apply hp
    rw [← hoff, hy]
    ring

lemma x_support_of_y_zero (d : CriticalData) (i : I3)
    (hy : d.y i = 0) :
    d.x i ≠ 0 ↔ d.y (jIndex i) ≠ 0 ∧ d.y (kIndex i) ≠ 0 := by
  have hoff := d.offQ i
  rw [edgeCof_symm3] at hoff
  simp [hy] at hoff
  have hleft : d.m i * sCoeff d.m i ≠ 0 :=
    mul_ne_zero (d.m_ne_zero i) (ne_of_gt (sCoeff_pos d i))
  have hright : d.sigma ≠ 0 := ne_of_gt d.sigma_pos
  constructor
  · intro hx
    have hp : d.y (jIndex i) * d.y (kIndex i) ≠ 0 := by
      intro hpzero
      have : d.m i * sCoeff d.m i * d.x i = 0 := by
        rw [hoff, hpzero]
        ring
      exact (mul_ne_zero hleft hx) this
    exact ⟨fun h ↦ hp (by simp [h]), fun h ↦ hp (by simp [h])⟩
  · rintro ⟨hj, hk⟩ hx
    have hp : d.y (jIndex i) * d.y (kIndex i) ≠ 0 := mul_ne_zero hj hk
    apply hp
    have : d.sigma * (d.y (jIndex i) * d.y (kIndex i)) = 0 := by
      rw [← hoff, hx]
      ring
    exact (mul_eq_zero.mp this).resolve_left hright

lemma not_both_zero (d : CriticalData) (i : I3) :
    ¬(d.x i = 0 ∧ d.y i = 0) := by
  rintro ⟨hx, hy⟩
  fin_cases i
  · have hsplit : d.y 1 = 0 ∨ d.y 2 = 0 := by
      by_contra h
      push Not at h
      exact ((x_support_of_y_zero d 0 hy).mpr
        (by simpa [jIndex, kIndex] using h)) hx
    rcases hsplit with hy1 | hy2
    · have hx1 : d.x 1 = 0 := by
        by_contra hx1
        have h := (x_support_of_y_zero d 1 hy1).mp hx1
        exact h.1 (by simpa [jIndex, kIndex] using hy)
      exact (d.noCommonAxis 2) (by simpa [jIndex, kIndex] using ⟨hx, hx1, hy, hy1⟩)
    · have hx2 : d.x 2 = 0 := by
        by_contra hx2
        have h := (x_support_of_y_zero d 2 hy2).mp hx2
        exact h.1 (by simpa [jIndex, kIndex] using hy)
      exact (d.noCommonAxis 1) (by simpa [jIndex, kIndex] using ⟨hx, hx2, hy, hy2⟩)
  · have hsplit : d.y 0 = 0 ∨ d.y 2 = 0 := by
      by_contra h
      push Not at h
      exact ((x_support_of_y_zero d 1 hy).mpr
        (by simpa [jIndex, kIndex] using h)) hx
    rcases hsplit with hy0 | hy2
    · have hx0 : d.x 0 = 0 := by
        by_contra hx0
        have h := (x_support_of_y_zero d 0 hy0).mp hx0
        exact h.1 (by simpa [jIndex, kIndex] using hy)
      exact (d.noCommonAxis 2) (by simpa [jIndex, kIndex] using ⟨hx0, hx, hy0, hy⟩)
    · have hx2 : d.x 2 = 0 := by
        by_contra hx2
        have h := (x_support_of_y_zero d 2 hy2).mp hx2
        exact h.2 (by simpa [jIndex, kIndex] using hy)
      exact (d.noCommonAxis 0) (by simpa [jIndex, kIndex] using ⟨hx, hx2, hy, hy2⟩)
  · have hsplit : d.y 0 = 0 ∨ d.y 1 = 0 := by
      by_contra h
      push Not at h
      exact ((x_support_of_y_zero d 2 hy).mpr
        (by simpa [jIndex, kIndex] using h)) hx
    rcases hsplit with hy0 | hy1
    · have hx0 : d.x 0 = 0 := by
        by_contra hx0
        have h := (x_support_of_y_zero d 0 hy0).mp hx0
        exact h.2 (by simpa [jIndex, kIndex] using hy)
      exact (d.noCommonAxis 1) (by simpa [jIndex, kIndex] using ⟨hx0, hx, hy0, hy⟩)
    · have hx1 : d.x 1 = 0 := by
        by_contra hx1
        have h := (x_support_of_y_zero d 1 hy1).mp hx1
        exact h.2 (by simpa [jIndex, kIndex] using hy)
      exact (d.noCommonAxis 0) (by simpa [jIndex, kIndex] using ⟨hx1, hx, hy1, hy⟩)

def MissingOnly (x : I3 → ℝ) (i : I3) : Prop :=
  x i = 0 ∧ ∀ r, r ≠ i → x r ≠ 0

lemma missingOnly_of_zero (d : CriticalData) (i : I3) (hx : d.x i = 0) :
    MissingOnly d.x i := by
  refine ⟨hx, ?_⟩
  have hyi : d.y i ≠ 0 := fun hy ↦ not_both_zero d i ⟨hx, hy⟩
  have hsupp := (y_support_of_x_zero d i hx).mp hyi
  intro r hri
  fin_cases i <;> fin_cases r <;>
    simp [jIndex, kIndex] at hri hsupp ⊢ <;> tauto

lemma missingOnly_y_of_zero (d : CriticalData) (i : I3) (hy : d.y i = 0) :
    MissingOnly d.y i := by
  refine ⟨hy, ?_⟩
  have hxi : d.x i ≠ 0 := fun hx ↦ not_both_zero d i ⟨hx, hy⟩
  have hsupp := (x_support_of_y_zero d i hy).mp hxi
  intro r hri
  fin_cases i <;> fin_cases r <;>
    simp [jIndex, kIndex] at hri hsupp ⊢ <;> tauto

lemma support_classification (d : CriticalData) :
    (AllNonzero d.x ∧ AllNonzero d.y) ∨
    (∃ i, MissingOnly d.x i ∧ AllNonzero d.y) ∨
    (∃ i, AllNonzero d.x ∧ MissingOnly d.y i) ∨
    (∃ i j, i ≠ j ∧ MissingOnly d.x i ∧ MissingOnly d.y j) := by
  classical
  by_cases hx : AllNonzero d.x
  · by_cases hy : AllNonzero d.y
    · exact Or.inl ⟨hx, hy⟩
    · have : ∃ i, d.y i = 0 := by
        simpa [AllNonzero] using hy
      obtain ⟨i, hi⟩ := this
      exact Or.inr (Or.inr (Or.inl ⟨i, hx, missingOnly_y_of_zero d i hi⟩))
  · have hxzero : ∃ i, d.x i = 0 := by
      simpa [AllNonzero] using hx
    obtain ⟨i, hi⟩ := hxzero
    have hmi := missingOnly_of_zero d i hi
    by_cases hy : AllNonzero d.y
    · exact Or.inr (Or.inl ⟨i, hmi, hy⟩)
    · have hyzero : ∃ j, d.y j = 0 := by
        simpa [AllNonzero] using hy
      obtain ⟨j, hj⟩ := hyzero
      have hmj := missingOnly_y_of_zero d j hj
      have hij : i ≠ j := by
        intro hij
        subst j
        exact (not_both_zero d i) ⟨hi, hj⟩
      exact Or.inr (Or.inr (Or.inr ⟨i, j, hij, hmi, hmj⟩))

lemma twoOfThree_intersection {A B : I3 → Prop}
    (hA : TwoOfThree A) (hB : TwoOfThree B) :
    ∃ i, A i ∧ B i := by
  rcases hA with hA | hA | hA <;>
    rcases hB with hB | hB | hB
  all_goals first
    | exact ⟨0, hA.1, hB.1⟩
    | exact ⟨0, hA.1, hB.2⟩
    | exact ⟨1, hA.2, hB.1⟩
    | exact ⟨1, hA.1, hB.2⟩
    | exact ⟨2, hA.2, hB.2⟩

lemma twoOfThree_has_off_missing {P : I3 → Prop} {i : I3}
    (hP : TwoOfThree P) : ∃ r, r ≠ i ∧ P r := by
  fin_cases i
  · rcases hP with h | h | h
    · exact ⟨1, by decide, h.2⟩
    · exact ⟨2, by decide, h.2⟩
    · exact ⟨1, by decide, h.1⟩
  · rcases hP with h | h | h
    · exact ⟨0, by decide, h.1⟩
    · exact ⟨0, by decide, h.1⟩
    · exact ⟨2, by decide, h.2⟩
  · rcases hP with h | h | h
    · exact ⟨0, by decide, h.1⟩
    · exact ⟨0, by decide, h.1⟩
    · exact ⟨1, by decide, h.1⟩

lemma edge_product_zero_of_missing {x : I3 → ℝ} {i r : I3}
    (hmiss : MissingOnly x i) (hri : r ≠ i) :
    x (jIndex r) * x (kIndex r) = 0 := by
  fin_cases i <;> fin_cases r <;>
    simp [MissingOnly, jIndex, kIndex] at hmiss hri ⊢ <;>
    simp [hmiss.1]

lemma residual_eq_diag_of_missing {p x : I3 → ℝ} {i r : I3}
    (hmiss : MissingOnly x i) (hri : r ≠ i) :
    edgeResidual (symm3 p x) r = p r := by
  have hxr := hmiss.2 r hri
  have hprod := edge_product_zero_of_missing hmiss hri
  have hcof := edgeCof_eq_neg_residual p x r hxr
  rw [edgeCof_symm3, hprod] at hcof
  have hmul : (-p r) * x r =
      (-edgeResidual (symm3 p x) r) * x r := by
    simpa using hcof
  have hneg := mul_right_cancel₀ hxr hmul
  linarith

lemma exclude_fully_mixed (d : CriticalData)
    (hx : AllNonzero d.x) (hy : AllNonzero d.y) : False := by
  have hq := d.firstResidual hy
  have hp := d.secondResidual hx
  obtain ⟨i, hqi, hpi⟩ := twoOfThree_intersection hq hp
  have hsmall := (q_residual_lt_four_iff d i (hx i) (hy i)).mp hqi
  have hlarge := (p_residual_lt_four_iff d i (hx i)).mp hpi
  have hone := one_lt_b_div_a d i
  linarith

lemma exclude_two_three (d : CriticalData) (i : I3)
    (hx : MissingOnly d.x i) (hy : AllNonzero d.y) : False := by
  have hq := d.firstResidual hy
  obtain ⟨r, hri, hqr⟩ := twoOfThree_has_off_missing hq
  have hxr := hx.2 r hri
  have hpdiag := residual_eq_diag_of_missing (p := d.p) hx hri
  have hpr : edgeResidual (symm3 d.p d.x) r / bCoeff d.m r < 4 := by
    rw [hpdiag]
    exact d.secondDiag r
  have hsmall := (q_residual_lt_four_iff d r hxr (hy r)).mp hqr
  have hlarge := (p_residual_lt_four_iff d r hxr).mp hpr
  have hone := one_lt_b_div_a d r
  linarith

lemma exclude_three_two (d : CriticalData) (i : I3)
    (hx : AllNonzero d.x) (hy : MissingOnly d.y i) : False := by
  have hp := d.secondResidual hx
  obtain ⟨r, hri, hpr⟩ := twoOfThree_has_off_missing hp
  have hyr := hy.2 r hri
  have hqdiag := residual_eq_diag_of_missing (p := d.q) hy hri
  have hqr : d.sigma * edgeResidual (symm3 d.q d.y) r < 4 := by
    rw [hqdiag]
    exact d.firstDiag r
  have hsmall := (q_residual_lt_four_iff d r (hx r) hyr).mp hqr
  have hlarge := (p_residual_lt_four_iff d r (hx r)).mp hpr
  have hone := one_lt_b_div_a d r
  linarith

lemma exclude_two_two (d : CriticalData) (i j : I3) (hij : i ≠ j)
    (hx : MissingOnly d.x i) (hy : MissingOnly d.y j) : False := by
  have hxj := hx.2 j (Ne.symm hij)
  have hyj := hy.1
  have hprod := edge_product_zero_of_missing hx (Ne.symm hij)
  have hoff := d.offP j
  rw [edgeCof_symm3, hprod] at hoff
  simp [hyj] at hoff
  have hp : d.p j = bCoeff d.m j * deltaCoeff d.m j := by
    exact (hoff.resolve_right hxj).symm
  have hdiag := d.secondDiag j
  rw [hp] at hdiag
  have hb := bCoeff_pos d j
  have hdelta : 4 < deltaCoeff d.m j := by
    change 4 < sCoeff d.m j + 4
    exact lt_add_of_pos_left 4 (sCoeff_pos d j)
  field_simp [ne_of_gt hb] at hdiag
  nlinarith

theorem criticalData_false (d : CriticalData) : False := by
  rcases support_classification d with h | h | h | h
  · exact exclude_fully_mixed d h.1 h.2
  · obtain ⟨i, hx, hy⟩ := h
    exact exclude_two_three d i hx hy
  · obtain ⟨i, hx, hy⟩ := h
    exact exclude_three_two d i hx hy
  · obtain ⟨i, j, hij, hx, hy⟩ := h
    exact exclude_two_two d i j hij hx hy

end S3xS3.Trivial.Support
