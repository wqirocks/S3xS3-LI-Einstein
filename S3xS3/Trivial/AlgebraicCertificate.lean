import S3xS3.Core

/-!
# Algebraic certificate for excluding trivial inner isotropy

This file follows the graph-coordinate proof for `SU(2) × SU(2)`.  All
ordered-field and finite-support steps are stated independently so that the
geometric front end can use them without hiding sign or division arguments.
-/

open scoped Matrix

namespace S3xS3.Trivial

/-! ## The radial inequality -/

/-- The suppressed sign case in the radial estimate.  Positivity of
`(y-x)(2x-y)` together with `x>0` forces both factors, rather than allowing
both to be negative. -/
lemma positive_radial_factors {x y : ℝ} (hx : 0 < x)
    (hprod : 0 < (y - x) * (2 * x - y)) : x < y ∧ y < 2 * x := by
  rcases mul_pos_iff.mp hprod with hpos | hneg
  · constructor <;> linarith
  · exfalso
    linarith

/-- Exact ordered-field core of Proposition `radial`: Cauchy--Schwarz and the
radial identity imply `alpha < -ell`. -/
lemma radial_alpha_strict {ell x y c alpha : ℝ}
    (hell : 0 < ell) (hx : 0 < x)
    (hcidentity : 3 * c = 2 * x ^ 2 + y ^ 2 + ell)
    (hcauchy : c ≤ x * y) (halpha : alpha = x ^ 2 - c) :
    alpha < -ell := by
  have hproduct : ell ≤ (y - x) * (2 * x - y) := by
    nlinarith
  have hproduct_pos : 0 < (y - x) * (2 * x - y) :=
    lt_of_lt_of_le hell hproduct
  obtain ⟨hxy, hy2x⟩ := positive_radial_factors hx hproduct_pos
  have hsum : 2 * (2 * x - y) < x + y := by linarith
  have hyx : 0 < y - x := sub_pos.mpr hxy
  have hstrict : 2 * ell < y ^ 2 - x ^ 2 := by
    have hmul : 2 * ((y - x) * (2 * x - y)) <
        (y - x) * (x + y) := by
      nlinarith
    nlinarith
  nlinarith

/-! ## The scalar threshold four -/

lemma threshold_four_large_middle {r s t : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) (hst : s ≤ t)
    (hs : 2 ≤ s) (ht : 4 ≤ t) :
    0 < r * s - 2 * r - 2 * s + 2 * t := by
  by_cases hs2 : s = 2
  · subst s
    nlinarith
  · have hslt : 2 < s := lt_of_le_of_ne hs (Ne.symm hs2)
    have hspos : 0 < s - 2 := sub_pos.mpr hslt
    nlinarith

lemma threshold_four_small_middle {r s t : ℝ}
    (_hr : 0 < r) (hrs : r ≤ s) (hs : s < 2) (ht : 4 ≤ t) :
    0 < r * s - 2 * r - 2 * s + 2 * t := by
  have hr2 : r < 2 := lt_of_le_of_lt hrs hs
  have hfactor : 0 < (2 - r) * (2 - s) := mul_pos (sub_pos.mpr hr2) (sub_pos.mpr hs)
  nlinarith

/-- Eigenvalue form of the threshold lemma: if the largest eigenvalue is at
least four, the corresponding eigenvalue of `Kop` is strictly positive. -/
lemma threshold_four_scalar {r s t : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) (hst : s ≤ t) (ht : 4 ≤ t) :
    0 < r * s - 2 * r - 2 * s + 2 * t := by
  by_cases hs : 2 ≤ s
  · exact threshold_four_large_middle hr hrs hst hs ht
  · exact threshold_four_small_middle hr hrs (lt_of_not_ge hs) ht

/-! ## Rational inequalities used in the support exclusions -/

lemma theta_small_iff {S theta : ℝ} (hS : 0 < S) (htheta : theta ≠ 0) :
    S * (theta - 1) / theta < 0 ↔ 0 < theta ∧ theta < 1 := by
  constructor
  · intro h
    by_cases hp : 0 < theta
    · constructor
      · exact hp
      · have := (div_neg_iff.mp h)
        rcases this with hcase | hcase
        · nlinarith
        · nlinarith
    · have hn : theta < 0 := lt_of_le_of_ne (le_of_not_gt hp) htheta
      have ht1 : theta - 1 < 0 := by linarith
      have hnum : S * (theta - 1) < 0 := mul_neg_of_pos_of_neg hS ht1
      have : 0 < S * (theta - 1) / theta := div_pos_of_neg_of_neg hnum hn
      linarith
  · rintro ⟨hp, hlt⟩
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hS (sub_neg.mpr hlt)) hp

lemma theta_large_iff {a b S theta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hS : 0 < S) :
    S / b * (b - a * theta) < 0 ↔ b / a < theta := by
  have hSb : 0 < S / b := div_pos hS hb
  constructor
  · intro h
    have hneg : b - a * theta < 0 := by
      rcases mul_neg_iff.mp h with hcase | hcase
      · exact hcase.2
      · exfalso; linarith
    apply (div_lt_iff₀ ha).2
    linarith
  · intro h
    have hneg : b - a * theta < 0 := by
      have := (div_lt_iff₀ ha).mp h
      linarith
    exact mul_neg_of_pos_of_neg hSb hneg

/-! ## Three-index pigeonhole lemma -/

lemma two_large_subsets_intersect (A B : Finset (Fin 3))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) : (A ∩ B).Nonempty := by
  by_contra hnone
  have hdisj : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.not_nonempty_iff_eq_empty.mp hnone)
  have hcard : A.card + B.card ≤ 3 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.subset_univ _)
  omega

/-! ## A denominator-explicit fully-mixed barrier -/

def quad3 (H : Mat3) (v : I3 → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * H i j * v j

def normSq3 (v : I3 → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Coordinate form of `H ≺ 4I`, sufficient for the three explicit test
vectors used below. -/
def StrictBelowFour (H : Mat3) : Prop :=
  ∀ v : I3 → ℝ, v ≠ 0 → quad3 H v < 4 * normSq3 v

def off0 (H : Mat3) : ℝ := H 1 2
def off1 (H : Mat3) : ℝ := H 0 2
def off2 (H : Mat3) : ℝ := H 0 1

noncomputable def residual0 (H : Mat3) : ℝ := H 0 0 - off1 H * off2 H / off0 H
noncomputable def residual1 (H : Mat3) : ℝ := H 1 1 - off0 H * off2 H / off1 H
noncomputable def residual2 (H : Mat3) : ℝ := H 2 2 - off0 H * off1 H / off2 H

lemma pair01_test_identity {H : Mat3} (hsym : H.IsHermitian)
    (h0 : off0 H ≠ 0) (h1 : off1 H ≠ 0) :
    quad3 H ![off0 H, -off1 H, 0] =
      residual0 H * (off0 H) ^ 2 + residual1 H * (off1 H) ^ 2 := by
  have h01 : H 1 0 = H 0 1 := by
    have := congrFun (congrFun hsym 1) 0
    simpa using this.symm
  have h0' : H 1 2 ≠ 0 := h0
  have h1' : H 0 2 ≠ 0 := h1
  simp [quad3, off0, off1, off2, residual0, residual1,
    Fin.sum_univ_succ, h01]
  field_simp [h0', h1']
  ring

lemma pair02_test_identity {H : Mat3} (hsym : H.IsHermitian)
    (h0 : off0 H ≠ 0) (h2 : off2 H ≠ 0) :
    quad3 H ![off0 H, 0, -off2 H] =
      residual0 H * (off0 H) ^ 2 + residual2 H * (off2 H) ^ 2 := by
  have h02 : H 2 0 = H 0 2 := by
    have := congrFun (congrFun hsym 2) 0
    simpa using this.symm
  have h0' : H 1 2 ≠ 0 := h0
  have h2' : H 0 1 ≠ 0 := h2
  simp [quad3, off0, off1, off2, residual0, residual2,
    Fin.sum_univ_succ, h02]
  field_simp [h0', h2']
  ring

lemma pair12_test_identity {H : Mat3} (hsym : H.IsHermitian)
    (h1 : off1 H ≠ 0) (h2 : off2 H ≠ 0) :
    quad3 H ![0, off1 H, -off2 H] =
      residual1 H * (off1 H) ^ 2 + residual2 H * (off2 H) ^ 2 := by
  have h12 : H 2 1 = H 1 2 := by
    have := congrFun (congrFun hsym 2) 1
    simpa using this.symm
  have h1' : H 0 2 ≠ 0 := h1
  have h2' : H 0 1 ≠ 0 := h2
  simp [quad3, off0, off1, off2, residual1, residual2,
    Fin.sum_univ_succ, h12]
  field_simp [h1', h2']
  ring

lemma normSq3_pair01 (u v : ℝ) : normSq3 ![u, -v, 0] = u ^ 2 + v ^ 2 := by
  simp [normSq3, Fin.sum_univ_succ]

lemma normSq3_pair02 (u w : ℝ) : normSq3 ![u, 0, -w] = u ^ 2 + w ^ 2 := by
  simp [normSq3, Fin.sum_univ_succ]

lemma normSq3_pair12 (v w : ℝ) : normSq3 ![0, v, -w] = v ^ 2 + w ^ 2 := by
  simp [normSq3, Fin.sum_univ_succ]

lemma residual_pair01_not_both_large {H : Mat3} (hsym : H.IsHermitian)
    (hfour : StrictBelowFour H) (h0 : off0 H ≠ 0) (h1 : off1 H ≠ 0) :
    residual0 H < 4 ∨ residual1 H < 4 := by
  by_contra hnot
  push Not at hnot
  let v : I3 → ℝ := ![off0 H, -off1 H, 0]
  have hv : v ≠ 0 := by
    intro hv
    have := congrFun hv 0
    simp [v, h0] at this
  have hstrict := hfour v hv
  rw [pair01_test_identity hsym h0 h1, normSq3_pair01] at hstrict
  have hs0 : 0 < (off0 H) ^ 2 := sq_pos_of_ne_zero h0
  have hs1 : 0 < (off1 H) ^ 2 := sq_pos_of_ne_zero h1
  nlinarith

lemma residual_pair02_not_both_large {H : Mat3} (hsym : H.IsHermitian)
    (hfour : StrictBelowFour H) (h0 : off0 H ≠ 0) (h2 : off2 H ≠ 0) :
    residual0 H < 4 ∨ residual2 H < 4 := by
  by_contra hnot
  push Not at hnot
  let v : I3 → ℝ := ![off0 H, 0, -off2 H]
  have hv : v ≠ 0 := by
    intro hv
    have := congrFun hv 0
    simp [v, h0] at this
  have hstrict := hfour v hv
  rw [pair02_test_identity hsym h0 h2, normSq3_pair02] at hstrict
  have hs0 : 0 < (off0 H) ^ 2 := sq_pos_of_ne_zero h0
  have hs2 : 0 < (off2 H) ^ 2 := sq_pos_of_ne_zero h2
  nlinarith

lemma residual_pair12_not_both_large {H : Mat3} (hsym : H.IsHermitian)
    (hfour : StrictBelowFour H) (h1 : off1 H ≠ 0) (h2 : off2 H ≠ 0) :
    residual1 H < 4 ∨ residual2 H < 4 := by
  by_contra hnot
  push Not at hnot
  let v : I3 → ℝ := ![0, off1 H, -off2 H]
  have hv : v ≠ 0 := by
    intro hv
    have := congrFun hv 1
    simp [v, h1] at this
  have hstrict := hfour v hv
  rw [pair12_test_identity hsym h1 h2, normSq3_pair12] at hstrict
  have hs1 : 0 < (off1 H) ^ 2 := sq_pos_of_ne_zero h1
  have hs2 : 0 < (off2 H) ^ 2 := sq_pos_of_ne_zero h2
  nlinarith

/-- Fully mixed strict barrier in the exact form used by all support cases:
at least two of the three denominator-free residuals are below four. -/
theorem two_residuals_lt_four {H : Mat3} (hsym : H.IsHermitian)
    (hfour : StrictBelowFour H)
    (h0 : off0 H ≠ 0) (h1 : off1 H ≠ 0) (h2 : off2 H ≠ 0) :
    (residual0 H < 4 ∧ residual1 H < 4) ∨
    (residual0 H < 4 ∧ residual2 H < 4) ∨
    (residual1 H < 4 ∧ residual2 H < 4) := by
  have h01 := residual_pair01_not_both_large hsym hfour h0 h1
  have h02 := residual_pair02_not_both_large hsym hfour h0 h2
  have h12 := residual_pair12_not_both_large hsym hfour h1 h2
  by_cases h0s : residual0 H < 4
  · by_cases h1s : residual1 H < 4
    · exact Or.inl ⟨h0s, h1s⟩
    · have h2s : residual2 H < 4 := h12.resolve_left h1s
      exact Or.inr (Or.inl ⟨h0s, h2s⟩)
  · have h1s : residual1 H < 4 := h01.resolve_left h0s
    have h2s : residual2 H < 4 := h02.resolve_left h0s
    exact Or.inr (Or.inr ⟨h1s, h2s⟩)

def cofEdge0 (H : Mat3) : ℝ := H 0 1 * H 0 2 - H 0 0 * H 1 2
def cofEdge1 (H : Mat3) : ℝ := H 0 1 * H 1 2 - H 1 1 * H 0 2
def cofEdge2 (H : Mat3) : ℝ := H 0 2 * H 1 2 - H 2 2 * H 0 1

lemma cofEdge0_eq_neg_residual (H : Mat3) (h0 : off0 H ≠ 0) :
    cofEdge0 H = -residual0 H * off0 H := by
  have h0' : H 1 2 ≠ 0 := h0
  simp [cofEdge0, residual0, off0, off1, off2]
  field_simp [h0']

lemma cofEdge1_eq_neg_residual (H : Mat3) (h1 : off1 H ≠ 0) :
    cofEdge1 H = -residual1 H * off1 H := by
  have h1' : H 0 2 ≠ 0 := h1
  simp [cofEdge1, residual1, off0, off1, off2]
  field_simp [h1']

lemma cofEdge2_eq_neg_residual (H : Mat3) (h2 : off2 H ≠ 0) :
    cofEdge2 H = -residual2 H * off2 H := by
  have h2' : H 0 1 ≠ 0 := h2
  simp [cofEdge2, residual2, off0, off1, off2]
  field_simp [h2']

end S3xS3.Trivial
