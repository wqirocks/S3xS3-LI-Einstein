import S3xS3.Trivial.FactorSwapFormulas

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.SwappedEuler

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.EinsteinBridge
open S3xS3.Trivial.PositiveEinstein
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge
open S3xS3.Trivial.Preparation
open S3xS3.Trivial.FactorSwap
open S3xS3.Trivial.FactorSwapFormulas
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.IsotropyGeometry

structure EulerForGraph {g : LeftInvariantMetric} (d : GraphData g)
    (lambda : ℝ) where
  U : SO3
  V : SO3
  euler : EulerData
  P_eq : euler.P = (d.pullback U V).P
  Q_eq : euler.Q = (d.pullback U V).Q
  M_eq : euler.M = (d.pullback U V).M
  kappa_eq : euler.kappa = 2 * lambda

theorem eulerForGraph_nonempty {g : LeftInvariantMetric} (d : GraphData g)
    {lambda : ℝ} (hEin : ricci g = lambda • g.gram) :
    Nonempty (EulerForGraph d lambda) := by
  obtain ⟨U, p, hp, hP⟩ := diagonalize_posDef_three d.P_pos
  obtain ⟨V, q, hq, hQ⟩ := diagonalize_posDef_three d.Q_pos
  let a : InnerAction := (U, V)
  let d1 : GraphData (pullbackMetric a g) := d.pullback U V
  have hd1P : d1.P = Matrix.diagonal p := hP
  have hd1Q : d1.Q = Matrix.diagonal q := hQ
  let r : RawGraph := rawOfDiagonalGraph d1 p q
  let hr : RawPositive r := rawOfDiagonalGraph_positive d1 p q hp hq
  have hmetric : r.metric hr = pullbackMetric a g :=
    rawOfDiagonalGraph_metric_eq d1 p q hp hq hd1P hd1Q
  have hpull : ricci (pullbackMetric a g) =
      lambda • (pullbackMetric a g).gram :=
    by
      rw [ricci_pullback, hEin]
      change (innerMatrix a)ᵀ * (lambda • g.gram) * innerMatrix a =
        lambda • ((innerMatrix a)ᵀ * g.gram * innerMatrix a)
      simp
  have hraw : ricci (r.metric hr) = lambda • (r.metric hr).gram := by
    rw [hmetric]
    exact hpull
  let e := eulerDataOfEinstein r hr hraw
  refine ⟨⟨U, V, e, ?_, ?_, ?_, rfl⟩⟩
  · change r.P = d1.P
    rw [rawOfDiagonalGraph_P d1 p q hp, hd1P]
  · change r.Q = d1.Q
    rw [rawOfDiagonalGraph_Q d1 p q hq, hd1Q]
  · rfl

noncomputable def eulerForGraph {g : LeftInvariantMetric}
    (d : GraphData g) {lambda : ℝ}
    (hEin : ricci g = lambda • g.gram) : EulerForGraph d lambda :=
  Classical.choice (eulerForGraph_nonempty d hEin)

lemma det_rotateP (P : Mat3) (U : SO3) :
    (rotateP P U).det = P.det := by
  rw [rotateP, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hdet := (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).2
  rw [hdet]
  ring

lemma det_rotateQ (Q : Mat3) (V : SO3) :
    (rotateQ Q V).det = Q.det := det_rotateP Q V

lemma rhoQ_eulerForGraph {g : LeftInvariantMetric} (d : GraphData g)
    {lambda : ℝ} (hEin : ricci g = lambda • g.gram) :
    rhoQ (eulerForGraph d hEin).euler = 4 * lambda / d.Q.det := by
  let p := eulerForGraph d hEin
  rw [rhoQ, p.kappa_eq, p.Q_eq]
  change 2 * (2 * lambda) / (rotateQ d.Q p.V).det = _
  rw [det_rotateQ]
  ring

lemma rhoP_eulerForGraph {g : LeftInvariantMetric} (d : GraphData g)
    {lambda : ℝ} (hEin : ricci g = lambda • g.gram) :
    rhoP (eulerForGraph d hEin).euler = 4 * lambda / d.P.det := by
  let p := eulerForGraph d hEin
  rw [rhoP, p.kappa_eq, p.P_eq]
  change 2 * (2 * lambda) / (rotateP d.P p.U).det = _
  rw [det_rotateP]
  ring

lemma ell_rotate (d : EulerData) (U V : SO3) :
    ell (EulerData.rotate d U V) = ell d := by
  change (((rotateM d.M U V)ᵀ * rotateM d.M U V) *
      lop' (rotateP d.P U)).trace = ((d.Mᵀ * d.M) * lop' d.P).trace
  rw [rotateM_transpose_mul]
  change (((U : Mat3)ᵀ * (d.Mᵀ * d.M) * U) *
      lop' ((U : Mat3)ᵀ * d.P * U)).trace = _
  rw [lop'_conjugate_so3]
  have hconj :
      ((U : Mat3)ᵀ * (d.Mᵀ * d.M) * U) *
          ((U : Mat3)ᵀ * lop' d.P * U) =
        (U : Mat3)ᵀ * ((d.Mᵀ * d.M) * lop' d.P) * U := by
    rw [show ((U : Mat3)ᵀ * (d.Mᵀ * d.M) * U) *
          ((U : Mat3)ᵀ * lop' d.P * U) =
        (U : Mat3)ᵀ * (d.Mᵀ * d.M) *
          ((U : Mat3) * (U : Mat3)ᵀ) * lop' d.P * U by
            noncomm_ring,
      so3_mul_transpose]
    simp
    noncomm_ring
  rw [hconj, trace_so3_conjugate]

lemma quad3_conjugate_so3 (A : Mat3) (U : SO3) (v : Vec3) :
    S3xS3.Trivial.quad3 ((U : Mat3)ᵀ * A * U) v =
      S3xS3.Trivial.quad3 A ((U : Mat3) *ᵥ v) := by
  simp [S3xS3.Trivial.quad3, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring

lemma normSq3_mulVec_so3 (U : SO3) (v : Vec3) :
    S3xS3.Trivial.normSq3 ((U : Mat3) *ᵥ v) =
      S3xS3.Trivial.normSq3 v := by
  have h := quad3_conjugate_so3 (1 : Mat3) U v
  have hc : (U : Mat3)ᵀ * (1 : Mat3) * U = 1 := by
    rw [Matrix.mul_one, so3_transpose_mul]
  rw [hc] at h
  simpa [S3xS3.Trivial.quad3, S3xS3.Trivial.normSq3,
    Matrix.mul_apply, Matrix.mulVec, Fin.sum_univ_succ, pow_two] using h.symm

lemma transpose_mulVec_ne_zero (U : SO3) {v : Vec3} (hv : v ≠ 0) :
    (U : Mat3)ᵀ *ᵥ v ≠ 0 := by
  intro hz
  apply hv
  have h := congrArg (fun w : Vec3 ↦ (U : Mat3) *ᵥ w) hz
  rw [Matrix.mulVec_mulVec, so3_mul_transpose] at h
  simpa using h

lemma strictBelowFour_of_conjugate (A : Mat3) (U : SO3)
    (h : S3xS3.Trivial.StrictBelowFour
      ((U : Mat3)ᵀ * A * U)) :
    S3xS3.Trivial.StrictBelowFour A := by
  intro v hv
  let w : Vec3 := (U : Mat3)ᵀ *ᵥ v
  have hw : w ≠ 0 := transpose_mulVec_ne_zero U hv
  have hb := h w hw
  have hUw : (U : Mat3) *ᵥ w = v := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, so3_mul_transpose]
    simp
  rw [quad3_conjugate_so3, hUw, ← normSq3_mulVec_so3 U w, hUw] at hb
  exact hb

lemma strictBelowFour_smul_pullback {g : LeftInvariantMetric}
    (d : GraphData g) (U V : SO3) (c : ℝ)
    (h : S3xS3.Trivial.StrictBelowFour
      (c • (d.pullback U V).Q)) :
    S3xS3.Trivial.StrictBelowFour (c • d.Q) := by
  apply strictBelowFour_of_conjugate (c • d.Q) V
  have heq : (V : Mat3)ᵀ * (c • d.Q) * V =
      c • (d.pullback U V).Q := by
    change (V : Mat3)ᵀ * (c • d.Q) * V =
      c • ((V : Mat3)ᵀ * d.Q * V)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [heq]
  exact h

lemma det_rotateM (M : Mat3) (U V : SO3) :
    (rotateM M U V).det = M.det := by
  rw [rotateM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hU := (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).2
  have hV := (Matrix.mem_specialOrthogonalGroup_iff.mp V.property).2
  rw [hU, hV]
  ring

lemma eulerForGraph_M_det_ne_zero {g : LeftInvariantMetric}
    (d : GraphData g) {lambda : ℝ}
    (hEin : ricci g = lambda • g.gram) (hMdet : d.M.det ≠ 0) :
    (eulerForGraph d hEin).euler.M.det ≠ 0 := by
  let p := eulerForGraph d hEin
  rw [p.M_eq]
  change (rotateM d.M p.U p.V).det ≠ 0
  rw [det_rotateM]
  exact hMdet

lemma nontrivial_of_eulerForGraph_ell_zero {g : LeftInvariantMetric}
    (d : GraphData g) {lambda : ℝ}
    (hEin : ricci g = lambda • g.gram)
    (hMdet : d.M.det ≠ 0)
    (hell : ell (eulerForGraph d hEin).euler = 0) :
    HasNontrivialInnerIsotropy g := by
  let p := eulerForGraph d hEin
  let d1 := d.pullback p.U p.V
  have hpMdet : p.euler.M.det ≠ 0 :=
    eulerForGraph_M_det_ne_zero d hEin hMdet
  obtain ⟨U, V, m, hm, hdiag⟩ :=
    signedSVD_of_invertible p.euler.M hpMdet
  let e2 := EulerData.rotate p.euler U V
  let d2 := d1.pullback U V
  have hPbase : p.euler.P = (1 : ℝ) • d1.P := by
    simpa [d1] using p.P_eq
  have hQbase : p.euler.Q = (1 : ℝ) • d1.Q := by
    simpa [d1] using p.Q_eq
  have hMbase : p.euler.M = d1.M := by simpa [d1] using p.M_eq
  have hP2 : e2.P = (1 : ℝ) • d2.P := by
    exact rotate_scale_graph_P d1 p.euler (1 : ℝ) U V hPbase
  have hQ2 : e2.Q = (1 : ℝ) • d2.Q := by
    exact rotate_scale_graph_Q d1 p.euler (1 : ℝ) U V hQbase
  have hM2 : e2.M = d2.M := by
    exact rotate_graph_M d1 p.euler U V hMbase
  have hdiag2 : e2.M = Matrix.diagonal m := by exact hdiag
  have hell2 : ell e2 = 0 := by
    rw [ell_rotate]
    exact hell
  have hnon2 : HasNontrivialInnerIsotropy
      (pullbackMetric (U, V) (pullbackMetric (p.U, p.V) g)) := by
    exact nontrivial_of_scaled_diagonal_ell_zero d2 e2 (1 : ℝ) one_pos m hm
      hP2 hQ2 hM2 hdiag2 hell2
  have hnon1 : HasNontrivialInnerIsotropy
      (pullbackMetric (p.U, p.V) g) :=
    pullback_nontrivial (U, V) hnon2
  exact pullback_nontrivial (p.U, p.V) hnon1

theorem first_barrier_for_graph_of_trivial {g : LeftInvariantMetric}
    (d : GraphData g) {lambda : ℝ}
    (hEin : ricci g = lambda • g.gram)
    (hMdet : d.M.det ≠ 0)
    (htriv : ¬ HasNontrivialInnerIsotropy g) :
    S3xS3.Trivial.StrictBelowFour
      ((4 * lambda / d.Q.det) • d.Q) := by
  let p := eulerForGraph d hEin
  have hpMdet : p.euler.M.det ≠ 0 :=
    eulerForGraph_M_det_ne_zero d hEin hMdet
  have hcof : cofactor3 p.euler.M ≠ 0 :=
    cofactor3_ne_zero_of_det_ne_zero hpMdet
  have hell : 0 < ell p.euler := by
    have hn := ell_nonneg p.euler
    apply lt_of_le_of_ne hn
    intro hz
    apply htriv
    apply nontrivial_of_eulerForGraph_ell_zero d hEin hMdet
    exact hz.symm
  have hb := first_barrier p.euler hcof hell
  have hrho : rhoQ p.euler = 4 * lambda / d.Q.det :=
    rhoQ_eulerForGraph d hEin
  rw [hrho, p.Q_eq] at hb
  exact strictBelowFour_smul_pullback d p.U p.V
    (4 * lambda / d.Q.det) hb

end S3xS3.Trivial.SwappedEuler
