import S3xS3.Trivial.SecondBarrier

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.MainTheorem

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge
open S3xS3.Trivial.Normalize
open S3xS3.Trivial.FullRank
open S3xS3.Trivial.IsotropyGeometry
open S3xS3.Trivial.Preparation
open S3xS3.Trivial.SwappedEuler
open S3xS3.Trivial.SecondBarrier
open S3xS3.Trivial.FactorSwap

lemma ricci_pullback_of_einstein_constant {g : LeftInvariantMetric}
    {lambda : ℝ} (hEin : ricci g = lambda • g.gram)
    (a : InnerAction) :
    ricci (pullbackMetric a g) = lambda • (pullbackMetric a g).gram := by
  rw [ricci_pullback, hEin]
  change (innerMatrix a)ᵀ * (lambda • g.gram) * innerMatrix a =
    lambda • ((innerMatrix a)ᵀ * g.gram * innerMatrix a)
  simp

lemma pullback_P_det {g : LeftInvariantMetric} (d : GraphData g)
    (U V : SO3) : (d.pullback U V).P.det = d.P.det := by
  change (rotateP d.P U).det = d.P.det
  exact det_rotateP d.P U

lemma pullback_Q_det {g : LeftInvariantMetric} (d : GraphData g)
    (U V : SO3) : (d.pullback U V).Q.det = d.Q.det := by
  change (rotateQ d.Q V).det = d.Q.det
  exact det_rotateQ d.Q V

lemma rhoP_rotate (d : EulerData) (U V : SO3) :
    rhoP (EulerData.rotate d U V) = rhoP d := by
  rw [rhoP, rhoP]
  change 2 * d.kappa / (rotateP d.P U).det = 2 * d.kappa / d.P.det
  rw [det_rotateP]

lemma rhoQ_rotate (d : EulerData) (U V : SO3) :
    rhoQ (EulerData.rotate d U V) = rhoQ d := by
  rw [rhoQ, rhoQ]
  change 2 * d.kappa / (rotateQ d.Q V).det = 2 * d.kappa / d.Q.det
  rw [det_rotateQ]

theorem einstein_has_nontrivial_inner_isotropy
    (g : LeftInvariantMetric) :
    Einstein g → HasNontrivialInnerIsotropy g := by
  intro hg
  by_contra htriv
  obtain ⟨lambda, hEin⟩ := hg
  let d0 : GraphData g := canonicalGraphData g
  let prep := eulerForGraph d0 hEin
  let d1 := d0.pullback prep.U prep.V
  have hPprep : prep.euler.P = d1.P := by
    simpa [d1] using prep.P_eq
  have hQprep : prep.euler.Q = d1.Q := by
    simpa [d1] using prep.Q_eq
  have hMprep : prep.euler.M = d1.M := by
    simpa [d1] using prep.M_eq
  rcases euler_M_zero_or_invertible prep.euler with hMzero | hMdet
  · have hd1zero : d1.M = 0 := by rw [← hMprep, hMzero]
    apply htriv
    exact pullback_nontrivial (prep.U, prep.V)
      (nontrivial_of_zeroM d1 hd1zero)
  · let t := rhoP prep.euler
    have ht : 0 < t := rhoP_pos prep.euler
    let en := EulerData.normalize prep.euler
    have henMdet : en.M.det ≠ 0 := by
      change prep.euler.M.det ≠ 0
      exact hMdet
    obtain ⟨U, V, m, hm, hdiag⟩ :=
      signedSVD_of_invertible en.M henMdet
    let er := EulerData.rotate en U V
    let d2 := d1.pullback U V
    have hPen : en.P = t • d1.P := by
      change t • prep.euler.P = t • d1.P
      rw [hPprep]
    have hQen : en.Q = t • d1.Q := by
      change t • prep.euler.Q = t • d1.Q
      rw [hQprep]
    have hMen : en.M = d1.M := by
      change prep.euler.M = d1.M
      exact hMprep
    have hPer : er.P = t • d2.P :=
      rotate_scale_graph_P d1 en t U V hPen
    have hQer : er.Q = t • d2.Q :=
      rotate_scale_graph_Q d1 en t U V hQen
    have hMer : er.M = d2.M :=
      rotate_graph_M d1 en U V hMen
    have hdiagEr : er.M = Matrix.diagonal m := hdiag
    have hdiagGraph : d2.M = Matrix.diagonal m := by
      rw [← hMer, hdiagEr]
    have hMdetGraph : d2.M.det ≠ 0 := by
      rw [hdiagGraph]
      exact diagonal_det_ne_zero hm
    have hEin1 : ricci (pullbackMetric (prep.U, prep.V) g) =
        lambda • (pullbackMetric (prep.U, prep.V) g).gram :=
      ricci_pullback_of_einstein_constant hEin (prep.U, prep.V)
    have hEin2 :
        ricci (pullbackMetric (U, V) (pullbackMetric (prep.U, prep.V) g)) =
          lambda •
            (pullbackMetric (U, V) (pullbackMetric (prep.U, prep.V) g)).gram :=
      ricci_pullback_of_einstein_constant hEin1 (U, V)
    have htriv1 :
        ¬ HasNontrivialInnerIsotropy (pullbackMetric (prep.U, prep.V) g) := by
      intro hnon
      exact htriv (pullback_nontrivial (prep.U, prep.V) hnon)
    have htriv2 :
        ¬ HasNontrivialInnerIsotropy
          (pullbackMetric (U, V) (pullbackMetric (prep.U, prep.V) g)) := by
      intro hnon
      exact htriv1 (pullback_nontrivial (U, V) hnon)
    have hnorm : rhoP er = 1 := by
      rw [rhoP_rotate]
      exact rhoP_normalize prep.euler
    have hdetP20 : d2.P.det ≠ 0 := ne_of_gt d2.P_pos.det_pos
    have hdetQ20 : d2.Q.det ≠ 0 := ne_of_gt d2.Q_pos.det_pos
    have hdetP : d2.P.det = d0.P.det := by
      rw [pullback_P_det d1 U V, pullback_P_det d0 prep.U prep.V]
    have hdetQ : d2.Q.det = d0.Q.det := by
      rw [pullback_Q_det d1 U V, pullback_Q_det d0 prep.U prep.V]
    have htFormula : t = 4 * lambda / d2.P.det := by
      dsimp [t]
      rw [rhoP_eulerForGraph d0 hEin, hdetP]
    have hrhoQPrep : rhoQ prep.euler = 4 * lambda / d0.Q.det :=
      rhoQ_eulerForGraph d0 hEin
    have hrhoQer : rhoQ er = rhoQ prep.euler / t := by
      rw [rhoQ_rotate]
      exact rhoQ_scale prep.euler t ht
    have hfirstRaw :=
      first_barrier_for_graph_of_trivial d2 hEin2 hMdetGraph htriv2
    have hfirstMatrix :
        rhoQ er • er.Q = (4 * lambda / d2.Q.det) • d2.Q := by
      rw [hQer, smul_smul]
      congr 1
      rw [hrhoQer, hrhoQPrep, hdetQ]
      field_simp [ne_of_gt ht, hdetQ20]
    have hfirst : S3xS3.Trivial.StrictBelowFour (rhoQ er • er.Q) := by
      rw [hfirstMatrix]
      exact hfirstRaw
    have hsecondRaw := second_barrier_for_graph_of_trivial
      d2 m hdiagGraph hm hEin2 htriv2
    have hsecond :
        S3xS3.Trivial.StrictBelowFour (secondMatrix m er.P) := by
      rw [hPer, htFormula]
      exact hsecondRaw
    have haxis := noCommonAxis_of_no_isotropy_scaled
      d2 er t ht m hPer hQer hdiagEr hdiagGraph htriv2
    exact no_fullRank_normalized_diagonal_euler er m hm hdiagEr
      hnorm hfirst hsecond haxis

end S3xS3.Trivial.MainTheorem
