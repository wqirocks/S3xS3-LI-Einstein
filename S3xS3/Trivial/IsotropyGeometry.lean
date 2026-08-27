import S3xS3.Trivial.FullRankExclusion

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.IsotropyGeometry

open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.Support

def coordinateSigns : I3 → I3 → ℝ :=
  ![![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

def coordinateTurn (i : I3) : SO3 := by
  let T : Mat3 := Matrix.diagonal (coordinateSigns i)
  refine ⟨T, (Matrix.mem_specialOrthogonalGroup_iff).2 ⟨?_, ?_⟩⟩
  · apply (Matrix.mem_orthogonalGroup_iff' I3 ℝ).2
    ext r s
    fin_cases i <;> fin_cases r <;> fin_cases s <;>
      simp [T, coordinateSigns, Matrix.mul_apply, Fin.sum_univ_succ]
  · change (Matrix.diagonal (coordinateSigns i)).det = 1
    rw [Matrix.det_diagonal]
    fin_cases i <;> simp [coordinateSigns, Fin.prod_univ_succ]

lemma coordinateTurn_coe (i : I3) :
    (coordinateTurn i : Mat3) = Matrix.diagonal (coordinateSigns i) := rfl

lemma coordinateTurn_transpose (i : I3) :
    (coordinateTurn i : Mat3)ᵀ = coordinateTurn i := by
  rw [coordinateTurn_coe]
  simp

lemma coordinateTurn_ne_one (i : I3) : coordinateTurn i ≠ 1 := by
  intro h
  have hc := congrArg (fun U : SO3 ↦ (U : Mat3)) h
  fin_cases i
  · have he := congrFun (congrFun hc 1) 1
    norm_num [coordinateTurn, coordinateSigns] at he
  · have he := congrFun (congrFun hc 0) 0
    norm_num [coordinateTurn, coordinateSigns] at he
  · have he := congrFun (congrFun hc 0) 0
    norm_num [coordinateTurn, coordinateSigns] at he

lemma coordinateTurn_diagonal (i : I3) (a : I3 → ℝ) :
    (coordinateTurn i : Mat3)ᵀ * Matrix.diagonal a * coordinateTurn i =
      Matrix.diagonal a := by
  rw [coordinateTurn_transpose]
  ext r s
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    simp [coordinateTurn, coordinateSigns, Matrix.mul_apply,
      Fin.sum_univ_succ]

lemma coordinateTurn_axis (A : Mat3) (hA : A.IsHermitian) (i : I3)
    (h1 : edgeOf A (jIndex i) = 0)
    (h2 : edgeOf A (kIndex i) = 0) :
    (coordinateTurn i : Mat3)ᵀ * A * coordinateTurn i = A := by
  have hAt : Aᵀ = A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  have h10 : A 1 0 = A 0 1 := by
    have h := congrFun (congrFun hAt 0) 1
    simpa using h
  have h20 : A 2 0 = A 0 2 := by
    have h := congrFun (congrFun hAt 0) 2
    simpa using h
  have h21 : A 2 1 = A 1 2 := by
    have h := congrFun (congrFun hAt 1) 2
    simpa using h
  rw [coordinateTurn_transpose]
  ext r s
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    simp [coordinateTurn, coordinateSigns, Matrix.mul_apply,
      Fin.sum_univ_succ, edgeOf, jIndex, kIndex] at h1 h2 ⊢ <;>
    simp_all

lemma fixes_of_common_axis {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = Matrix.diagonal m) (i : I3)
    (hP1 : edgeOf d.P (jIndex i) = 0)
    (hP2 : edgeOf d.P (kIndex i) = 0)
    (hQ1 : edgeOf d.Q (jIndex i) = 0)
    (hQ2 : edgeOf d.Q (kIndex i) = 0) :
    Fixes (coordinateTurn i, coordinateTurn i) g := by
  apply d.fixes_of_stabilizes
  · exact coordinateTurn_axis d.P d.P_pos.isHermitian i hP1 hP2
  · exact coordinateTurn_axis d.Q d.Q_pos.isHermitian i hQ1 hQ2
  · rw [hM]
    exact coordinateTurn_diagonal i m

lemma commonAxis_action_ne_one (i : I3) :
    (coordinateTurn i, coordinateTurn i) ≠ (1 : InnerAction) := by
  intro h
  have hfst := congrArg Prod.fst h
  exact coordinateTurn_ne_one i hfst

theorem nontrivial_of_common_axis {g : LeftInvariantMetric} (d : GraphData g)
    (m : I3 → ℝ) (hM : d.M = Matrix.diagonal m) (i : I3)
    (hP1 : edgeOf d.P (jIndex i) = 0)
    (hP2 : edgeOf d.P (kIndex i) = 0)
    (hQ1 : edgeOf d.Q (jIndex i) = 0)
    (hQ2 : edgeOf d.Q (kIndex i) = 0) :
    HasNontrivialInnerIsotropy g := by
  exact ⟨(coordinateTurn i, coordinateTurn i), commonAxis_action_ne_one i,
    fixes_of_common_axis d m hM i hP1 hP2 hQ1 hQ2⟩

lemma pullback_nontrivial {g : LeftInvariantMetric} (a : InnerAction)
    (h : HasNontrivialInnerIsotropy (pullbackMetric a g)) :
    HasNontrivialInnerIsotropy g := by
  obtain ⟨b, hb, hfix⟩ := h
  refine ⟨a * b * a⁻¹, ?_, (fixes_conjugate_iff a b g).2 hfix⟩
  intro heq
  apply hb
  calc
    b = a⁻¹ * (a * b * a⁻¹) * a := by group
    _ = 1 := by rw [heq]; simp

lemma fixes_zeroM_diagonalP {g : LeftInvariantMetric} (d : GraphData g)
    (p : I3 → ℝ) (hP : d.P = Matrix.diagonal p) (hM : d.M = 0)
    (i : I3) : Fixes (coordinateTurn i, 1) g := by
  apply d.fixes_of_stabilizes
  · rw [hP]
    exact coordinateTurn_diagonal i p
  · simp
  · rw [hM]
    simp

lemma leftTurn_action_ne_one (i : I3) :
    (coordinateTurn i, 1) ≠ (1 : InnerAction) := by
  intro h
  exact coordinateTurn_ne_one i (congrArg Prod.fst h)

theorem nontrivial_of_zeroM {g : LeftInvariantMetric} (d : GraphData g)
    (hM : d.M = 0) : HasNontrivialInnerIsotropy g := by
  obtain ⟨U, p, hp, hP⟩ := diagonalize_posDef_three d.P_pos
  let d' := d.pullback U 1
  have hP' : d'.P = Matrix.diagonal p := by
    exact hP
  have hM' : d'.M = 0 := by
    change (1 : Mat3)ᵀ * d.M * (U : Mat3) = 0
    rw [hM]
    simp
  have hfix := fixes_zeroM_diagonalP d' p hP' hM' 0
  apply pullback_nontrivial (U, 1)
  exact ⟨(coordinateTurn 0, 1), leftTurn_action_ne_one 0, hfix⟩

end S3xS3.Trivial.IsotropyGeometry
