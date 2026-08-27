import S3xS3.Trivial.IsotropyGeometry

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.Preparation

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.EinsteinBridge
open S3xS3.Trivial.PositiveEinstein
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge
open S3xS3.Trivial.Normalize
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.IsotropyGeometry
open S3xS3.Trivial.Support

lemma cofactor3_ne_zero_of_det_ne_zero {M : Mat3} (hdet : M.det ≠ 0) :
    cofactor3 M ≠ 0 := by
  intro hC
  have h := cofactor3_mul_transpose M
  rw [hC] at h
  have h00 := congrFun (congrFun h 0) 0
  simp at h00
  exact hdet h00.symm

lemma diagonal_det_ne_zero {m : I3 → ℝ} (hm : ∀ i, m i ≠ 0) :
    (Matrix.diagonal m : Mat3).det ≠ 0 := by
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_succ, hm]

lemma euler_M_zero_or_invertible (d : EulerData) :
    d.M = 0 ∨ d.M.det ≠ 0 := by
  by_cases hM : d.M = 0
  · exact Or.inl hM
  · right
    intro hdet
    by_cases hC : cofactor3 d.M = 0
    · exact no_eulerData_cofactor_zero_nonzero d hC hM
    · exact no_eulerData_singular_cofactor_ne d hC hdet

lemma rotate_scale_graph_P {g : LeftInvariantMetric} (d : GraphData g)
    (e : EulerData) (t : ℝ) (U V : SO3)
    (hP : e.P = t • d.P) :
    (EulerData.rotate e U V).P =
      t • (d.pullback U V).P := by
  change (U : Mat3)ᵀ * e.P * U =
    t • ((U : Mat3)ᵀ * d.P * U)
  rw [hP, Matrix.mul_smul, Matrix.smul_mul]

lemma rotate_scale_graph_Q {g : LeftInvariantMetric} (d : GraphData g)
    (e : EulerData) (t : ℝ) (U V : SO3)
    (hQ : e.Q = t • d.Q) :
    (EulerData.rotate e U V).Q =
      t • (d.pullback U V).Q := by
  change (V : Mat3)ᵀ * e.Q * V =
    t • ((V : Mat3)ᵀ * d.Q * V)
  rw [hQ, Matrix.mul_smul, Matrix.smul_mul]

lemma rotate_graph_M {g : LeftInvariantMetric} (d : GraphData g)
    (e : EulerData) (U V : SO3) (hM : e.M = d.M) :
    (EulerData.rotate e U V).M = (d.pullback U V).M := by
  change (V : Mat3)ᵀ * e.M * U = (V : Mat3)ᵀ * d.M * U
  rw [hM]

lemma edge_zero_of_scaled_edge_zero {A B : Mat3} {t : ℝ}
    (ht : t ≠ 0) (hAB : A = t • B) (i : I3)
    (hA : edgeOf A i = 0) : edgeOf B i = 0 := by
  fin_cases i
  · change A 1 2 = 0 at hA
    change B 1 2 = 0
    have h := congrFun (congrFun hAB 1) 2
    simp only [real_smul_apply] at h
    rw [hA] at h
    exact (mul_eq_zero.mp h.symm).resolve_left ht
  · change A 0 2 = 0 at hA
    change B 0 2 = 0
    have h := congrFun (congrFun hAB 0) 2
    simp only [real_smul_apply] at h
    rw [hA] at h
    exact (mul_eq_zero.mp h.symm).resolve_left ht
  · change A 0 1 = 0 at hA
    change B 0 1 = 0
    have h := congrFun (congrFun hAB 0) 1
    simp only [real_smul_apply] at h
    rw [hA] at h
    exact (mul_eq_zero.mp h.symm).resolve_left ht

lemma edges_zero_of_scalar (A : Mat3) {p : ℝ}
    (hA : A = p • (1 : Mat3)) (i : I3) : edgeOf A i = 0 := by
  fin_cases i <;> simp [edgeOf, hA]

lemma edges_zero_of_diagonal (A : Mat3) (q : I3 → ℝ)
    (hA : A = Matrix.diagonal q) (i : I3) : edgeOf A i = 0 := by
  fin_cases i <;> simp [edgeOf, hA]

theorem nontrivial_of_scaled_diagonal_ell_zero
    {g : LeftInvariantMetric} (graph : GraphData g) (d : EulerData)
    (t : ℝ) (ht : 0 < t) (m : I3 → ℝ)
    (hm : ∀ i, m i ≠ 0)
    (hP : d.P = t • graph.P) (hQ : d.Q = t • graph.Q)
    (hM : d.M = graph.M) (hdiagM : d.M = Matrix.diagonal m)
    (hell : ell d = 0) : HasNontrivialInnerIsotropy g := by
  obtain ⟨p, hp, hdP, hdQ⟩ := full_ell_zero_diagonal_Q d hdiagM hm hell
  have hgM : graph.M = Matrix.diagonal m := by rw [← hM, hdiagM]
  have hPedge : ∀ i, edgeOf graph.P i = 0 := by
    intro i
    apply edge_zero_of_scaled_edge_zero (ne_of_gt ht) hP i
    exact edges_zero_of_scalar d.P hdP i
  have hQedge : ∀ i, edgeOf graph.Q i = 0 := by
    intro i
    apply edge_zero_of_scaled_edge_zero (ne_of_gt ht) hQ i
    exact edges_zero_of_diagonal d.Q (fun i ↦ d.Q i i) hdQ i
  exact nontrivial_of_common_axis graph m hgM 0
    (hPedge _) (hPedge _) (hQedge _) (hQedge _)

lemma noCommonAxis_of_no_isotropy_scaled
    {g : LeftInvariantMetric} (graph : GraphData g) (d : EulerData)
    (t : ℝ) (ht : 0 < t) (m : I3 → ℝ)
    (hP : d.P = t • graph.P) (hQ : d.Q = t • graph.Q)
    (_hM : d.M = Matrix.diagonal m) (hgM : graph.M = Matrix.diagonal m)
    (htriv : ¬ HasNontrivialInnerIsotropy g) :
    ∀ i, ¬(edgeOf d.P (jIndex i) = 0 ∧
      edgeOf d.P (kIndex i) = 0 ∧
      edgeOf d.Q (jIndex i) = 0 ∧
      edgeOf d.Q (kIndex i) = 0) := by
  intro i haxis
  apply htriv
  apply nontrivial_of_common_axis graph m hgM i
  · exact edge_zero_of_scaled_edge_zero (ne_of_gt ht) hP _ haxis.1
  · exact edge_zero_of_scaled_edge_zero (ne_of_gt ht) hP _ haxis.2.1
  · exact edge_zero_of_scaled_edge_zero (ne_of_gt ht) hQ _ haxis.2.2.1
  · exact edge_zero_of_scaled_edge_zero (ne_of_gt ht) hQ _ haxis.2.2.2

structure PreparedEinstein (g : LeftInvariantMetric) where
  action : InnerAction
  graph : GraphData (pullbackMetric action g)
  euler : EulerData
  P_eq : euler.P = graph.P
  Q_eq : euler.Q = graph.Q
  M_eq : euler.M = graph.M

theorem prepareEinstein_nonempty {g : LeftInvariantMetric}
    (hg : Einstein g) : Nonempty (PreparedEinstein g) := by
  let d0 := canonicalGraphData g
  obtain ⟨U, p, hp, hP⟩ := diagonalize_posDef_three d0.P_pos
  obtain ⟨V, q, hq, hQ⟩ := diagonalize_posDef_three d0.Q_pos
  let a : InnerAction := (U, V)
  let d1 : GraphData (pullbackMetric a g) := d0.pullback U V
  have hd1P : d1.P = Matrix.diagonal p := by exact hP
  have hd1Q : d1.Q = Matrix.diagonal q := by exact hQ
  let r : RawGraph := rawOfDiagonalGraph d1 p q
  let hr : RawPositive r := rawOfDiagonalGraph_positive d1 p q hp hq
  have hmetric : r.metric hr = pullbackMetric a g :=
    rawOfDiagonalGraph_metric_eq d1 p q hp hq hd1P hd1Q
  obtain ⟨lambda, hlambda⟩ :=
    S3xS3.Naturality.Einstein.pullback hg a
  have hraw : ricci (r.metric hr) = lambda • (r.metric hr).gram := by
    rw [hmetric]
    exact hlambda
  let e : EulerData := eulerDataOfEinstein r hr hraw
  refine ⟨⟨a, d1, e, ?_, ?_, ?_⟩⟩
  · change r.P = d1.P
    rw [rawOfDiagonalGraph_P d1 p q hp, hd1P]
  · change r.Q = d1.Q
    rw [rawOfDiagonalGraph_Q d1 p q hq, hd1Q]
  · rfl

noncomputable def prepareEinstein {g : LeftInvariantMetric}
    (hg : Einstein g) : PreparedEinstein g :=
  Classical.choice (prepareEinstein_nonempty hg)

end S3xS3.Trivial.Preparation
