import S3xS3.Naturality
import S3xS3.Geometry.LeftInvariantGeometry

/-!
# The trace `-2` involution branch

This file formalizes the sign chamber, square certificate, decisive diagonal
difference, and the explicit Klein-four enhancement in the trace `-2` branch.
-/

open scoped Matrix

namespace S3xS3.Z2

section OrderedFieldLemmas

lemma pair_zero_iff {r s u y z : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h₁ : r * y = u * z) (h₂ : s * z = u * y) : y = 0 ↔ z = 0 := by
  constructor
  · intro hy
    subst y
    simpa using (mul_eq_zero.mp (by simpa using h₂)).resolve_left (ne_of_gt hs)
  · intro hz
    subst z
    simpa using (mul_eq_zero.mp (by simpa using h₁)).resolve_left (ne_of_gt hr)

lemma pair_square_and_sign {r s u y z : ℝ} (hr : 0 < r) (_hs : 0 < s)
    (hy : y ≠ 0) (hz : z ≠ 0)
    (h₁ : r * y = u * z) (h₂ : s * z = u * y) :
    u ^ 2 = r * s ∧ 0 < u * (y * z) := by
  have hyz : y * z ≠ 0 := mul_ne_zero hy hz
  constructor
  · apply (mul_left_cancel₀ hyz)
    calc
      y * z * u ^ 2 = (u * z) * (u * y) := by ring
      _ = (r * y) * (s * z) := by rw [← h₁, ← h₂]
      _ = y * z * (r * s) := by ring
  · have hyr : 0 < r * y ^ 2 := mul_pos hr (sq_pos_of_ne_zero hy)
    nlinarith [congrArg (fun q : ℝ ↦ q * y) h₁]

lemma abs_eq_of_sq_eq_sq_pos {u R : ℝ} (hR : 0 < R) (h : u ^ 2 = R ^ 2) :
    |u| = R := by
  have hu : 0 ≤ |u| := abs_nonneg u
  have hsquare : |u| ^ 2 = R ^ 2 := by simpa [sq_abs] using h
  nlinarith

lemma abs_add_eq_of_mul_pos {u v : ℝ} (h : 0 < u * v) :
    |u + v| = |u| + |v| := by
  rcases (mul_pos_iff.mp h) with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · simp [abs_of_pos hu, abs_of_pos hv, abs_of_pos (add_pos hu hv)]
  · have huv : u + v < 0 := add_neg hu hv
    simp [abs_of_neg hu, abs_of_neg hv, abs_of_neg huv]
    ring

lemma abs_sub_le_add_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a - b| ≤ a + b := by
  calc
    |a - b| ≤ |a| + |b| := abs_sub a b
    _ = a + b := by rw [abs_of_pos ha, abs_of_pos hb]

/-- The strict square-root estimate used twice in the sign argument. -/
lemma strict_root_bound
    {p q e f b c x root : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p ∨ 0 < q)
    (he : 0 < e) (hf : 0 < f) (hb : 0 < b) (hc : 0 < c)
    (hroot : 0 < root)
    (hroot_sq : root ^ 2 = (p + e ^ 2 + c ^ 2 * x ^ 2) *
      (q + f ^ 2 + b ^ 2 * x ^ 2)) :
    |x| * (b * e + c * f) < root := by
  have hu : 0 < e ^ 2 + c ^ 2 * x ^ 2 := by
    positivity
  have hv : 0 < f ^ 2 + b ^ 2 * x ^ 2 := by
    positivity
  have hprod :
      (e ^ 2 + c ^ 2 * x ^ 2) * (f ^ 2 + b ^ 2 * x ^ 2) <
        (p + e ^ 2 + c ^ 2 * x ^ 2) * (q + f ^ 2 + b ^ 2 * x ^ 2) := by
    rcases hpq with hp' | hq'
    · have : 0 < p * (q + f ^ 2 + b ^ 2 * x ^ 2) +
          q * (e ^ 2 + c ^ 2 * x ^ 2) := by positivity
      nlinarith
    · have : 0 < p * (q + f ^ 2 + b ^ 2 * x ^ 2) +
          q * (e ^ 2 + c ^ 2 * x ^ 2) := by positivity
      nlinarith
  have hsquare :
      (x ^ 2) * (b * e + c * f) ^ 2 ≤
        (e ^ 2 + c ^ 2 * x ^ 2) * (f ^ 2 + b ^ 2 * x ^ 2) := by
    have hnonneg : 0 ≤ (e * f - b * c * x ^ 2) ^ 2 := sq_nonneg _
    nlinarith
  have habs_sq : (|x| * (b * e + c * f)) ^ 2 =
      x ^ 2 * (b * e + c * f) ^ 2 := by rw [mul_pow, sq_abs]
  have hrhs : 0 ≤ |x| * (b * e + c * f) := by positivity
  have hsq_lt : (|x| * (b * e + c * f)) ^ 2 < root ^ 2 := by
    rw [habs_sq, hroot_sq]
    exact lt_of_le_of_lt hsquare hprod
  nlinarith

lemma sum_bound_of_positive
    {B C E F : ℝ} (hB : 0 < B) (hC : 0 < C) (hE : 0 < E) (hF : 0 < F) :
    |B - C| * |E - F| ≤ (B + C) * (E + F) := by
  have hBC := abs_sub_le_add_of_pos hB hC
  have hEF := abs_sub_le_add_of_pos hE hF
  exact mul_le_mul hBC hEF (abs_nonneg _) (by positivity)

end OrderedFieldLemmas

/-! ## The reduced trace `-2` system -/

structure Parameters where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  f : ℝ
  x : ℝ
  y : ℝ
  z : ℝ
  w : ℝ
  t : ℝ

namespace Parameters

variable (p : Parameters)

def delta : ℝ := p.y * p.z - p.w * p.t
def Pi : ℝ := p.a * p.d + p.b * p.e + p.c * p.f
def Omega : ℝ := p.a * p.d + p.b * p.f + p.c * p.e
def alpha : ℝ := (p.b - p.c) ^ 2 + p.d ^ 2
def r1 : ℝ := (p.a - p.c) ^ 2 + p.e ^ 2 + p.c ^ 2 * p.x ^ 2
def s1 : ℝ := (p.a - p.b) ^ 2 + p.f ^ 2 + p.b ^ 2 * p.x ^ 2
def r2 : ℝ := (p.a - p.b) ^ 2 + p.e ^ 2 + p.b ^ 2 * p.x ^ 2
def s2 : ℝ := (p.a - p.c) ^ 2 + p.f ^ 2 + p.c ^ 2 * p.x ^ 2
def u : ℝ := p.x * p.Pi - p.a ^ 2 * p.delta
def v : ℝ := -p.x * p.Omega + p.a ^ 2 * p.delta
def H : ℝ := (p.b - p.c) ^ 2 + p.d ^ 2 +
  p.b ^ 2 * (p.w ^ 2 + p.z ^ 2) + p.c ^ 2 * (p.y ^ 2 + p.t ^ 2)

noncomputable def S0 : ℝ :=
  -(p.a ^ 2 + p.b ^ 2 + p.c ^ 2 + p.d ^ 2 + p.e ^ 2 + p.f ^ 2) / 2 +
    p.a * p.b + p.a * p.c + p.b * p.c + p.d * p.e + p.d * p.f + p.e * p.f

noncomputable def scalar : ℝ :=
  p.S0 - (p.alpha * p.x ^ 2 + p.r1 * p.y ^ 2 + p.s1 * p.z ^ 2 +
    p.r2 * p.w ^ 2 + p.s2 * p.t ^ 2 + p.a ^ 2 * p.delta ^ 2) / 2 +
    p.Pi * p.x * p.y * p.z - p.Omega * p.x * p.w * p.t

/-- The derivative with respect to `D`, written explicitly so no differentiation
oracle occurs in the trusted statement. -/
def scalarD : ℝ := -p.d + p.e + p.f - p.d * p.x ^ 2 + p.a * p.x * p.delta

/-- The raw diagonal difference `B S_B - C S_C`. -/
def diagonalDifference : ℝ :=
  p.a * p.b - p.a * p.c - (p.b ^ 2 - p.c ^ 2) * (1 + p.x ^ 2) +
  p.b * (p.a - p.b * (1 + p.x ^ 2)) * (p.w ^ 2 + p.z ^ 2) -
  p.c * (p.a - p.c * (1 + p.x ^ 2)) * (p.y ^ 2 + p.t ^ 2) +
  p.x * (p.b * p.e - p.c * p.f) * p.y * p.z +
  p.x * (p.c * p.e - p.b * p.f) * p.w * p.t

end Parameters

/-- The open positive coordinate chamber. -/
structure PositiveParameters (p : Parameters) : Prop where
  a_pos : 0 < p.a
  b_pos : 0 < p.b
  c_pos : 0 < p.c
  d_pos : 0 < p.d
  e_pos : 0 < p.e
  f_pos : 0 < p.f

/-- Positivity and the reduced critical equations used by the new proof.  The
geometric front end below derives this record from the Ricci equation.  The
unit-volume equation is deliberately not stored here: none of the exclusion
or enhancement steps uses it, and the five off-diagonal equations and the
diagonal difference are invariant under constant rescaling. -/
structure CriticalPoint (p : Parameters) : Prop extends PositiveParameters p where
  pairYZ₁ : p.r1 * p.y = p.u * p.z
  pairYZ₂ : p.s1 * p.z = p.u * p.y
  pairWT₁ : p.r2 * p.w = p.v * p.t
  pairWT₂ : p.s2 * p.t = p.v * p.w
  xEquation : p.x * p.H = p.Pi * (p.y * p.z) - p.Omega * (p.w * p.t)
  diagonalBC : p.diagonalDifference = 0
  scalarD_pos : 0 < p.scalarD

lemma r1_pos {p : Parameters} (h : CriticalPoint p) : 0 < p.r1 := by
  dsimp [Parameters.r1]
  have := h.e_pos
  positivity

lemma s1_pos {p : Parameters} (h : CriticalPoint p) : 0 < p.s1 := by
  dsimp [Parameters.s1]
  have := h.f_pos
  positivity

lemma r2_pos {p : Parameters} (h : CriticalPoint p) : 0 < p.r2 := by
  dsimp [Parameters.r2]
  have := h.e_pos
  positivity

lemma s2_pos {p : Parameters} (h : CriticalPoint p) : 0 < p.s2 := by
  dsimp [Parameters.s2]
  have := h.f_pos
  positivity

lemma pi_pos {p : Parameters} (h : CriticalPoint p) : 0 < p.Pi := by
  dsimp [Parameters.Pi]
  have := h.a_pos
  have := h.b_pos
  have := h.c_pos
  have := h.d_pos
  have := h.e_pos
  have := h.f_pos
  positivity

lemma omega_pos {p : Parameters} (h : CriticalPoint p) : 0 < p.Omega := by
  dsimp [Parameters.Omega]
  have := h.a_pos
  have := h.b_pos
  have := h.c_pos
  have := h.d_pos
  have := h.e_pos
  have := h.f_pos
  positivity

lemma pair_zero_YZ {p : Parameters} (h : CriticalPoint p) : p.y = 0 ↔ p.z = 0 :=
  pair_zero_iff (r1_pos h) (s1_pos h) h.pairYZ₁ h.pairYZ₂

lemma pair_zero_WT {p : Parameters} (h : CriticalPoint p) : p.w = 0 ↔ p.t = 0 :=
  pair_zero_iff (r2_pos h) (s2_pos h) h.pairWT₁ h.pairWT₂

def FullyMixed (p : Parameters) : Prop :=
  p.y * p.z ≠ 0 ∧ p.w * p.t ≠ 0 ∧ p.b ≠ p.c ∧ p.e ≠ p.f

lemma H_pos {p : Parameters} (h : CriticalPoint p) : 0 < p.H := by
  dsimp [Parameters.H]
  have := h.d_pos
  positivity

lemma u_add_v (p : Parameters) :
    p.u + p.v = p.x * (p.b - p.c) * (p.e - p.f) := by
  simp only [Parameters.u, Parameters.v, Parameters.Pi, Parameters.Omega]
  ring

lemma mixed_square_signs {p : Parameters} (h : CriticalPoint p) (hm : FullyMixed p) :
    p.u ^ 2 = p.r1 * p.s1 ∧ 0 < p.u * (p.y * p.z) ∧
    p.v ^ 2 = p.r2 * p.s2 ∧ 0 < p.v * (p.w * p.t) := by
  rcases hm with ⟨hyz, hwt, -, -⟩
  have hy : p.y ≠ 0 := fun hy ↦ hyz (by simp [hy])
  have hz : p.z ≠ 0 := fun hz ↦ hyz (by simp [hz])
  have hw : p.w ≠ 0 := fun hw ↦ hwt (by simp [hw])
  have ht : p.t ≠ 0 := fun ht ↦ hwt (by simp [ht])
  exact ⟨(pair_square_and_sign (r1_pos h) (s1_pos h) hy hz
      h.pairYZ₁ h.pairYZ₂).1,
    (pair_square_and_sign (r1_pos h) (s1_pos h) hy hz
      h.pairYZ₁ h.pairYZ₂).2,
    (pair_square_and_sign (r2_pos h) (s2_pos h) hw ht
      h.pairWT₁ h.pairWT₂).1,
    (pair_square_and_sign (r2_pos h) (s2_pos h) hw ht
      h.pairWT₁ h.pairWT₂).2⟩

noncomputable def rootR (p : Parameters) : ℝ := Real.sqrt (p.r1 * p.s1)
noncomputable def rootV (p : Parameters) : ℝ := Real.sqrt (p.r2 * p.s2)

lemma rootR_pos {p : Parameters} (h : CriticalPoint p) : 0 < rootR p := by
  exact Real.sqrt_pos.2 (mul_pos (r1_pos h) (s1_pos h))

lemma rootV_pos {p : Parameters} (h : CriticalPoint p) : 0 < rootV p := by
  exact Real.sqrt_pos.2 (mul_pos (r2_pos h) (s2_pos h))

lemma rootR_sq {p : Parameters} (h : CriticalPoint p) :
    rootR p ^ 2 = p.r1 * p.s1 := by
  exact Real.sq_sqrt (le_of_lt (mul_pos (r1_pos h) (s1_pos h)))

lemma rootV_sq {p : Parameters} (h : CriticalPoint p) :
    rootV p ^ 2 = p.r2 * p.s2 := by
  exact Real.sq_sqrt (le_of_lt (mul_pos (r2_pos h) (s2_pos h)))

lemma rootR_strict {p : Parameters} (h : CriticalPoint p) (hm : FullyMixed p) :
    |p.x| * (p.b * p.e + p.c * p.f) < rootR p := by
  have hpq : 0 < (p.a - p.c) ^ 2 ∨ 0 < (p.a - p.b) ^ 2 := by
    by_cases hac : p.a = p.c
    · right
      apply sq_pos_of_ne_zero
      rw [sub_ne_zero]
      intro hab
      exact hm.2.2.1 (hab.symm.trans hac)
    · left
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr hac)
  apply strict_root_bound (sq_nonneg _) (sq_nonneg _) hpq h.e_pos h.f_pos
    h.b_pos h.c_pos (rootR_pos h)
  simpa only [Parameters.r1, Parameters.s1] using rootR_sq h

lemma rootV_strict {p : Parameters} (h : CriticalPoint p) (hm : FullyMixed p) :
    |p.x| * (p.b * p.f + p.c * p.e) < rootV p := by
  have hpq : 0 < (p.a - p.b) ^ 2 ∨ 0 < (p.a - p.c) ^ 2 := by
    by_cases hab : p.a = p.b
    · right
      apply sq_pos_of_ne_zero
      rw [sub_ne_zero]
      intro hac
      exact hm.2.2.1 (hab.symm.trans hac)
    · left
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hbound := strict_root_bound (x := p.x) (root := rootV p)
    (sq_nonneg (p.a - p.b)) (sq_nonneg (p.a - p.c)) hpq
    h.e_pos h.f_pos h.c_pos h.b_pos (rootV_pos h) (by
      simpa only [Parameters.r2, Parameters.s2] using rootV_sq h)
  simpa only [add_comm (p.c * p.e) (p.b * p.f)] using hbound

lemma uv_neg {p : Parameters} (h : CriticalPoint p) (hm : FullyMixed p) :
    p.u * p.v < 0 := by
  rcases mixed_square_signs h hm with ⟨hu_sq, hu_sign, hv_sq, hv_sign⟩
  have huabs : |p.u| = rootR p :=
    abs_eq_of_sq_eq_sq_pos (rootR_pos h) (hu_sq.trans (rootR_sq h).symm)
  have hvabs : |p.v| = rootV p :=
    abs_eq_of_sq_eq_sq_pos (rootV_pos h) (hv_sq.trans (rootV_sq h).symm)
  have huv_ne : p.u * p.v ≠ 0 := mul_ne_zero
    (fun hu ↦ by simpa [hu] using hu_sign.ne')
    (fun hv ↦ by simpa [hv] using hv_sign.ne')
  by_contra hn
  have huv_nonneg : 0 ≤ p.u * p.v := le_of_not_gt hn
  have huv_pos : 0 < p.u * p.v := lt_of_le_of_ne huv_nonneg (Ne.symm huv_ne)
  have habsadd := abs_add_eq_of_mul_pos huv_pos
  have hstrict : |p.x| * ((p.b + p.c) * (p.e + p.f)) < rootR p + rootV p := by
    have hR := rootR_strict h hm
    have hV := rootV_strict h hm
    calc
      |p.x| * ((p.b + p.c) * (p.e + p.f)) =
          |p.x| * (p.b * p.e + p.c * p.f) +
            |p.x| * (p.b * p.f + p.c * p.e) := by ring
      _ < rootR p + rootV p := add_lt_add hR hV
  have hweak : |p.x * (p.b - p.c) * (p.e - p.f)| ≤
      |p.x| * ((p.b + p.c) * (p.e + p.f)) := by
    rw [abs_mul, abs_mul]
    calc
      |p.x| * |p.b - p.c| * |p.e - p.f| =
          |p.x| * (|p.b - p.c| * |p.e - p.f|) := by ring
      _ ≤ |p.x| * ((p.b + p.c) * (p.e + p.f)) :=
        mul_le_mul_of_nonneg_left
          (sum_bound_of_positive h.b_pos h.c_pos h.e_pos h.f_pos) (abs_nonneg _)
  have heq : |p.u + p.v| = |p.x * (p.b - p.c) * (p.e - p.f)| := by
    rw [u_add_v]
  rw [huabs, hvabs] at habsadd
  linarith

lemma mixed_products_opposite {p : Parameters} (h : CriticalPoint p) (hm : FullyMixed p) :
    (p.y * p.z) * (p.w * p.t) < 0 := by
  rcases mixed_square_signs h hm with ⟨-, hu_sign, -, hv_sign⟩
  have hpos := mul_pos hu_sign hv_sign
  have huv := uv_neg h hm
  by_contra hn
  have hyzwt : 0 ≤ (p.y * p.z) * (p.w * p.t) := le_of_not_gt hn
  have hnonpos : p.u * p.v * ((p.y * p.z) * (p.w * p.t)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt huv) hyzwt
  nlinarith

lemma x_ne_zero {p : Parameters} (h : CriticalPoint p) (hm : FullyMixed p) : p.x ≠ 0 := by
  intro hx
  have hopposite := mixed_products_opposite h hm
  have heq : p.Pi * (p.y * p.z) = p.Omega * (p.w * p.t) := by
    have he := h.xEquation
    rw [hx] at he
    norm_num at he
    linarith
  have hyz_ne := hm.1
  have hleft : 0 < p.Pi * (p.y * p.z) ^ 2 :=
    mul_pos (pi_pos h) (sq_pos_of_ne_zero hyz_ne)
  have hright : 0 < p.Omega * ((p.w * p.t) * (p.y * p.z)) := by
    calc
      0 < p.Pi * (p.y * p.z) ^ 2 := hleft
      _ = p.Omega * ((p.w * p.t) * (p.y * p.z)) := by
        calc
          p.Pi * (p.y * p.z) ^ 2 =
              (p.Pi * (p.y * p.z)) * (p.y * p.z) := by ring
          _ = (p.Omega * (p.w * p.t)) * (p.y * p.z) := by rw [heq]
          _ = p.Omega * ((p.w * p.t) * (p.y * p.z)) := by ring
  have : 0 < (p.w * p.t) * (p.y * p.z) := by
    rcases mul_pos_iff.mp hright with hcase | hcase
    · exact hcase.2
    · exact False.elim ((not_lt_of_ge (le_of_lt (omega_pos h))) hcase.1)
  nlinarith

/-- Sign-normalized data from the fully mixed branch. -/
structure SignData (p : Parameters) where
  eps : ℝ
  x : ℝ
  rho : ℝ
  omega : ℝ
  R : ℝ
  V : ℝ
  eps_sq : eps ^ 2 = 1
  x_pos : 0 < x
  rho_pos : 0 < rho
  omega_pos : 0 < omega
  R_pos : 0 < R
  V_pos : 0 < V
  bc_ne : p.b ≠ p.c
  ef_ne : p.e ≠ p.f
  original_x : p.x = eps * x
  yz : p.y * p.z = eps * rho
  wt : p.w * p.t = -eps * omega
  u_eq : p.u = eps * R
  v_eq : p.v = -eps * V
  delta_eq : p.delta = eps * (rho + omega)
  R_sq : R ^ 2 = p.r1 * p.s1
  V_sq : V ^ 2 = p.r2 * p.s2

lemma exists_signData {p : Parameters} (h : CriticalPoint p) (hm : FullyMixed p) :
    Nonempty (SignData p) := by
  have hxne := x_ne_zero h hm
  have hopposite := mixed_products_opposite h hm
  rcases mixed_square_signs h hm with ⟨hu_sq, hu_sign, hv_sq, hv_sign⟩
  have huabs : |p.u| = rootR p :=
    abs_eq_of_sq_eq_sq_pos (rootR_pos h) (hu_sq.trans (rootR_sq h).symm)
  have hvabs : |p.v| = rootV p :=
    abs_eq_of_sq_eq_sq_pos (rootV_pos h) (hv_sq.trans (rootV_sq h).symm)
  by_cases hx : 0 < p.x
  · have hyz : 0 < p.y * p.z := by
      by_contra hn
      have hyzneg : p.y * p.z < 0 := lt_of_le_of_ne (le_of_not_gt hn)
        hm.1
      have hwtpos : 0 < p.w * p.t := by
        rcases mul_neg_iff.mp hopposite with hcase | hcase
        · exact False.elim ((not_lt_of_ge (le_of_lt hyzneg)) hcase.1)
        · exact hcase.2
      have hlhs : 0 < p.x * p.H := mul_pos hx (H_pos h)
      have hrhs : p.Pi * (p.y * p.z) - p.Omega * (p.w * p.t) < 0 := by
        have := pi_pos h
        have := omega_pos h
        nlinarith [mul_neg_of_pos_of_neg (pi_pos h) hyzneg,
          mul_pos (omega_pos h) hwtpos]
      linarith [h.xEquation]
    have hwt : p.w * p.t < 0 := by
      rcases mul_neg_iff.mp hopposite with hcase | hcase
      · exact hcase.2
      · exact False.elim ((not_lt_of_ge (le_of_lt hyz)) hcase.1)
    have hu : 0 < p.u := by
      rcases mul_pos_iff.mp hu_sign with hcase | hcase
      · exact hcase.1
      · exact False.elim ((not_lt_of_ge (le_of_lt hyz)) hcase.2)
    have hv : p.v < 0 := by
      rcases mul_pos_iff.mp hv_sign with hcase | hcase
      · exact False.elim ((not_lt_of_ge (le_of_lt hwt)) hcase.2)
      · exact hcase.1
    refine ⟨{
      eps := 1
      x := p.x
      rho := p.y * p.z
      omega := -(p.w * p.t)
      R := rootR p
      V := rootV p
      eps_sq := by norm_num
      x_pos := hx
      rho_pos := hyz
      omega_pos := neg_pos.mpr hwt
      R_pos := rootR_pos h
      V_pos := rootV_pos h
      bc_ne := hm.2.2.1
      ef_ne := hm.2.2.2
      original_x := by ring
      yz := by ring
      wt := by ring
      u_eq := by rw [← huabs, abs_of_pos hu]; ring
      v_eq := by rw [← hvabs, abs_of_neg hv]; ring
      delta_eq := by simp [Parameters.delta]; ring
      R_sq := rootR_sq h
      V_sq := rootV_sq h
    }⟩

  · have hxneg : p.x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hxne
    have hyz : p.y * p.z < 0 := by
      by_contra hn
      have hyzpos : 0 < p.y * p.z := lt_of_le_of_ne (le_of_not_gt hn)
        (Ne.symm hm.1)
      have hwtneg : p.w * p.t < 0 := by
        rcases mul_neg_iff.mp hopposite with hcase | hcase
        · exact hcase.2
        · exact False.elim ((not_lt_of_ge (le_of_lt hyzpos)) hcase.1)
      have hlhs : p.x * p.H < 0 := mul_neg_of_neg_of_pos hxneg (H_pos h)
      have hrhs : 0 < p.Pi * (p.y * p.z) - p.Omega * (p.w * p.t) := by
        have := pi_pos h
        have := omega_pos h
        nlinarith [mul_pos (pi_pos h) hyzpos,
          mul_neg_of_pos_of_neg (omega_pos h) hwtneg]
      linarith [h.xEquation]
    have hwt : 0 < p.w * p.t := by
      rcases mul_neg_iff.mp hopposite with hcase | hcase
      · exact False.elim ((not_lt_of_ge (le_of_lt hyz)) hcase.1)
      · exact hcase.2
    have hu : p.u < 0 := by
      rcases mul_pos_iff.mp hu_sign with hcase | hcase
      · exact False.elim ((not_lt_of_ge (le_of_lt hyz)) hcase.2)
      · exact hcase.1
    have hv : 0 < p.v := by
      rcases mul_pos_iff.mp hv_sign with hcase | hcase
      · exact hcase.1
      · exact False.elim ((not_lt_of_ge (le_of_lt hwt)) hcase.2)
    refine ⟨{
      eps := -1
      x := -p.x
      rho := -(p.y * p.z)
      omega := p.w * p.t
      R := rootR p
      V := rootV p
      eps_sq := by norm_num
      x_pos := neg_pos.mpr hxneg
      rho_pos := neg_pos.mpr hyz
      omega_pos := hwt
      R_pos := rootR_pos h
      V_pos := rootV_pos h
      bc_ne := hm.2.2.1
      ef_ne := hm.2.2.2
      original_x := by ring
      yz := by ring
      wt := by ring
      u_eq := by rw [← huabs, abs_of_neg hu]; ring
      v_eq := by rw [← hvabs, abs_of_pos hv]; ring
      delta_eq := by simp [Parameters.delta]; ring
      R_sq := rootR_sq h
      V_sq := rootV_sq h
    }⟩

lemma r1s1_sub_r2s2 (p : Parameters) :
    p.r1 * p.s1 - p.r2 * p.s2 =
      (p.b - p.c) * (p.e - p.f) * (p.e + p.f) *
        ((p.b + p.c) * (1 + p.x ^ 2) - 2 * p.a) := by
  simp only [Parameters.r1, Parameters.s1, Parameters.r2, Parameters.s2]
  ring

namespace SignData

variable {p : Parameters} (d : SignData p)

def sumBC (_d : SignData p) : ℝ := p.b + p.c
def diffBC (_d : SignData p) : ℝ := p.b - p.c
def sumEF (_d : SignData p) : ℝ := p.e + p.f
def diffEF (_d : SignData p) : ℝ := p.e - p.f
def m : ℝ := d.sumBC - 2 * p.a
def absDelta : ℝ := d.rho + d.omega

lemma eps_ne_zero : d.eps ≠ 0 := by
  intro he
  have hs := d.eps_sq
  rw [he] at hs
  norm_num at hs

lemma original_x_sq : p.x ^ 2 = d.x ^ 2 := by
  rw [d.original_x]
  nlinarith [d.eps_sq]

lemma abs_original_x : |p.x| = d.x := by
  apply abs_eq_of_sq_eq_sq_pos d.x_pos
  exact d.original_x_sq

lemma R_sub_V : d.R - d.V = d.x * d.diffBC * d.diffEF := by
  apply mul_left_cancel₀ d.eps_ne_zero
  calc
    d.eps * (d.R - d.V) = p.u + p.v := by rw [d.u_eq, d.v_eq]; ring
    _ = p.x * (p.b - p.c) * (p.e - p.f) := u_add_v p
    _ = d.eps * (d.x * d.diffBC * d.diffEF) := by
      rw [d.original_x]
      simp only [diffBC, diffEF]
      ring

lemma R_add_V_mul :
    d.x * (d.R + d.V) =
      d.sumEF * (d.sumBC * (1 + d.x ^ 2) - 2 * p.a) := by
  have hsquares :
      (d.R - d.V) * (d.R + d.V) = p.r1 * p.s1 - p.r2 * p.s2 := by
    rw [← d.R_sq, ← d.V_sq]
    ring
  have hdiff := r1s1_sub_r2s2 p
  have hproduct :
      d.diffBC * d.diffEF *
        (d.x * (d.R + d.V) -
          d.sumEF * (d.sumBC * (1 + d.x ^ 2) - 2 * p.a)) = 0 := by
    rw [d.R_sub_V] at hsquares
    simp only [sumBC, diffBC, sumEF, diffEF] at *
    rw [d.original_x_sq] at hdiff
    nlinarith
  have hbc : d.diffBC ≠ 0 := by
    simpa [diffBC, sub_ne_zero] using d.bc_ne
  have hef : d.diffEF ≠ 0 := by
    simpa [diffEF, sub_ne_zero] using d.ef_ne
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left (mul_ne_zero hbc hef))

lemma sumBC_pos (h : CriticalPoint p) : 0 < d.sumBC := by
  simp only [sumBC]
  nlinarith [h.b_pos, h.c_pos]

lemma sumEF_pos (h : CriticalPoint p) : 0 < d.sumEF := by
  simp only [sumEF]
  nlinarith [h.e_pos, h.f_pos]

lemma R_strict (h : CriticalPoint p) :
    d.x * (p.b * p.e + p.c * p.f) < d.R := by
  have hpq : 0 < (p.a - p.c) ^ 2 ∨ 0 < (p.a - p.b) ^ 2 := by
    by_cases hac : p.a = p.c
    · right
      apply sq_pos_of_ne_zero
      rw [sub_ne_zero]
      intro hab
      exact d.bc_ne (hab.symm.trans hac)
    · left
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr hac)
  have hsq : d.R ^ 2 =
      ((p.a - p.c) ^ 2 + p.e ^ 2 + p.c ^ 2 * d.x ^ 2) *
        ((p.a - p.b) ^ 2 + p.f ^ 2 + p.b ^ 2 * d.x ^ 2) := by
    simpa only [Parameters.r1, Parameters.s1, d.original_x_sq] using d.R_sq
  have hbound := strict_root_bound (x := d.x) (root := d.R)
    (sq_nonneg (p.a - p.c)) (sq_nonneg (p.a - p.b)) hpq h.e_pos h.f_pos
    h.b_pos h.c_pos d.R_pos hsq
  simpa only [abs_of_pos d.x_pos] using hbound

lemma V_strict (h : CriticalPoint p) :
    d.x * (p.b * p.f + p.c * p.e) < d.V := by
  have hpq : 0 < (p.a - p.b) ^ 2 ∨ 0 < (p.a - p.c) ^ 2 := by
    by_cases hab : p.a = p.b
    · right
      apply sq_pos_of_ne_zero
      rw [sub_ne_zero]
      intro hac
      exact d.bc_ne (hab.symm.trans hac)
    · left
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hsq : d.V ^ 2 =
      ((p.a - p.b) ^ 2 + p.e ^ 2 + p.b ^ 2 * d.x ^ 2) *
        ((p.a - p.c) ^ 2 + p.f ^ 2 + p.c ^ 2 * d.x ^ 2) := by
    simpa only [Parameters.r2, Parameters.s2, d.original_x_sq] using d.V_sq
  have hbound := strict_root_bound (x := d.x) (root := d.V)
    (sq_nonneg (p.a - p.b)) (sq_nonneg (p.a - p.c)) hpq
    h.e_pos h.f_pos h.c_pos h.b_pos d.V_pos hsq
  simpa only [abs_of_pos d.x_pos, add_comm (p.c * p.e) (p.b * p.f)] using hbound

lemma R_add_V_strict (h : CriticalPoint p) :
    d.x * d.sumBC * d.sumEF < d.R + d.V := by
  have hR := d.R_strict h
  have hV := d.V_strict h
  calc
    d.x * d.sumBC * d.sumEF =
        d.x * (p.b * p.e + p.c * p.f) +
          d.x * (p.b * p.f + p.c * p.e) := by
            simp only [sumBC, sumEF]
            ring
    _ < d.R + d.V := add_lt_add hR hV

lemma m_pos (h : CriticalPoint p) : 0 < d.m := by
  have hgap : 0 < d.R + d.V - d.x * d.sumBC * d.sumEF := by
    linarith [d.R_add_V_strict h]
  have hxgap : 0 < d.x *
      (d.R + d.V - d.x * d.sumBC * d.sumEF) := mul_pos d.x_pos hgap
  have heq : d.x * (d.R + d.V - d.x * d.sumBC * d.sumEF) =
      d.sumEF * d.m := by
    calc
      d.x * (d.R + d.V - d.x * d.sumBC * d.sumEF) =
          d.x * (d.R + d.V) - d.x ^ 2 * d.sumBC * d.sumEF := by ring
      _ = d.sumEF * (d.sumBC * (1 + d.x ^ 2) - 2 * p.a) -
          d.x ^ 2 * d.sumBC * d.sumEF := by rw [d.R_add_V_mul]
      _ = d.sumEF * d.m := by simp only [m]; ring
  have htm : 0 < d.sumEF * d.m := heq ▸ hxgap
  rcases mul_pos_iff.mp htm with hcase | hcase
  · exact hcase.2
  · exact False.elim ((not_lt_of_ge (le_of_lt (d.sumEF_pos h))) hcase.1)

lemma two_x_R (_h : CriticalPoint p) :
    2 * d.x * d.R =
      2 * d.x ^ 2 * (p.b * p.e + p.c * p.f) + d.sumEF * d.m := by
  calc
    2 * d.x * d.R = d.x * (d.R + d.V) + d.x * (d.R - d.V) := by ring
    _ = d.sumEF * (d.sumBC * (1 + d.x ^ 2) - 2 * p.a) +
        d.x * (d.x * d.diffBC * d.diffEF) := by
          rw [d.R_add_V_mul, d.R_sub_V]
    _ = 2 * d.x ^ 2 * (p.b * p.e + p.c * p.f) + d.sumEF * d.m := by
          simp only [sumBC, diffBC, sumEF, diffEF, m]
          ring

lemma two_x_V (_h : CriticalPoint p) :
    2 * d.x * d.V =
      2 * d.x ^ 2 * (p.b * p.f + p.c * p.e) + d.sumEF * d.m := by
  calc
    2 * d.x * d.V = d.x * (d.R + d.V) - d.x * (d.R - d.V) := by ring
    _ = d.sumEF * (d.sumBC * (1 + d.x ^ 2) - 2 * p.a) -
        d.x * (d.x * d.diffBC * d.diffEF) := by
          rw [d.R_add_V_mul, d.R_sub_V]
    _ = 2 * d.x ^ 2 * (p.b * p.f + p.c * p.e) + d.sumEF * d.m := by
          simp only [sumBC, diffBC, sumEF, diffEF, m]
          ring

lemma R_from_u : d.R = d.x * p.Pi - p.a ^ 2 * d.absDelta := by
  apply mul_left_cancel₀ d.eps_ne_zero
  calc
    d.eps * d.R = p.u := d.u_eq.symm
    _ = p.x * p.Pi - p.a ^ 2 * p.delta := rfl
    _ = d.eps * (d.x * p.Pi - p.a ^ 2 * d.absDelta) := by
      rw [d.original_x, d.delta_eq]
      simp only [absDelta]
      ring

lemma scaled_delta (h : CriticalPoint p) :
    2 * p.a ^ 2 * d.x * d.absDelta =
      2 * p.a * p.d * d.x ^ 2 - d.sumEF * d.m := by
  have hR := d.two_x_R h
  have hu := d.R_from_u
  simp only [Parameters.Pi] at hu
  rw [hu] at hR
  nlinarith

lemma scalarD_normalized :
    p.scalarD = -p.d + d.sumEF - p.d * d.x ^ 2 +
      p.a * d.x * d.absDelta := by
  simp only [Parameters.scalarD, sumEF, absDelta]
  have hprod : p.x * p.delta = d.x * (d.rho + d.omega) := by
    calc
      p.x * p.delta = (d.eps * d.x) * (d.eps * (d.rho + d.omega)) := by
        rw [d.original_x, d.delta_eq]
      _ = d.eps ^ 2 * (d.x * (d.rho + d.omega)) := by ring
      _ = d.x * (d.rho + d.omega) := by rw [d.eps_sq]; ring
  rw [d.original_x_sq]
  calc
    -p.d + p.e + p.f - p.d * d.x ^ 2 + p.a * p.x * p.delta =
        -p.d + p.e + p.f - p.d * d.x ^ 2 + p.a * (p.x * p.delta) := by ring
    _ = -p.d + (p.e + p.f) - p.d * d.x ^ 2 +
        p.a * (d.x * (d.rho + d.omega)) := by rw [hprod]; ring
    _ = -p.d + (p.e + p.f) - p.d * d.x ^ 2 +
        p.a * d.x * (d.rho + d.omega) := by ring

lemma scaled_scalarD (h : CriticalPoint p) :
    2 * p.a * p.scalarD =
      -2 * p.a * p.d + d.sumEF * (2 * p.a - d.m) := by
  have hδ := d.scaled_delta h
  rw [d.scalarD_normalized]
  simp only [sumEF, m, absDelta] at hδ ⊢
  nlinarith

lemma m_lt_two_a (h : CriticalPoint p) : d.m < 2 * p.a := by
  have htwoa : 0 < 2 * p.a := by nlinarith [h.a_pos]
  have hleft : 0 < 2 * p.a * p.scalarD := mul_pos htwoa h.scalarD_pos
  have hright : 0 < d.sumEF * (2 * p.a - d.m) := by
    rw [d.scaled_scalarD h] at hleft
    have had : 0 < 2 * p.a * p.d := mul_pos htwoa h.d_pos
    nlinarith
  rcases mul_pos_iff.mp hright with hcase | hcase
  · linarith [hcase.2]
  · exact False.elim ((not_lt_of_ge (le_of_lt (d.sumEF_pos h))) hcase.1)

lemma D_lower (h : CriticalPoint p) :
    d.sumEF * d.m < 2 * p.a * p.d * d.x ^ 2 := by
  have hdelta : 0 < d.absDelta := by
    simp only [absDelta]
    nlinarith [d.rho_pos, d.omega_pos]
  have ha2 : 0 < p.a ^ 2 := sq_pos_of_pos h.a_pos
  have hleft : 0 < 2 * p.a ^ 2 * d.x * d.absDelta := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) ha2) d.x_pos) hdelta
  rw [d.scaled_delta h] at hleft
  nlinarith

lemma D_upper (h : CriticalPoint p) :
    2 * p.a * p.d < d.sumEF * (2 * p.a - d.m) := by
  have htwoa : 0 < 2 * p.a := by nlinarith [h.a_pos]
  have hleft : 0 < 2 * p.a * p.scalarD := mul_pos htwoa h.scalarD_pos
  rw [d.scaled_scalarD h] at hleft
  nlinarith

lemma x_chamber (h : CriticalPoint p) :
    d.m < (2 * p.a - d.m) * d.x ^ 2 := by
  have hx2 : 0 < d.x ^ 2 := sq_pos_of_pos d.x_pos
  have hu := mul_lt_mul_of_pos_right (d.D_upper h) hx2
  have hc : d.sumEF * d.m <
      d.sumEF * ((2 * p.a - d.m) * d.x ^ 2) := by
    calc
      d.sumEF * d.m < 2 * p.a * p.d * d.x ^ 2 := d.D_lower h
      _ < (d.sumEF * (2 * p.a - d.m)) * d.x ^ 2 := by
        simpa only [mul_assoc] using hu
      _ = d.sumEF * ((2 * p.a - d.m) * d.x ^ 2) := by ring
  by_contra hn
  have hge : (2 * p.a - d.m) * d.x ^ 2 ≤ d.m := le_of_not_gt hn
  have hmul := mul_le_mul_of_nonneg_left hge (le_of_lt (d.sumEF_pos h))
  linarith

def xi : ℝ := d.x ^ 2
def beta : ℝ := d.diffBC ^ 2
def eta : ℝ := d.diffEF ^ 2
def tau : ℝ := d.sumEF ^ 2

def scriptL : ℝ :=
  4 * p.a ^ 2 * d.xi + 4 * p.a * d.m * d.xi - d.beta * d.xi +
    d.beta + d.m ^ 2 * d.xi + d.m ^ 2 - d.tau

def scriptM : ℝ :=
  d.m ^ 2 * (1 + d.xi) + 4 * p.a * d.m * d.xi - d.beta * d.xi

lemma four_r1 :
    4 * p.r1 = (d.diffBC - d.m) ^ 2 + (d.sumEF + d.diffEF) ^ 2 +
      (2 * p.a + d.m - d.diffBC) ^ 2 * d.xi := by
  simp only [Parameters.r1, diffBC, diffEF, sumBC, sumEF, m, xi]
  rw [d.original_x_sq]
  ring

lemma four_s1 :
    4 * p.s1 = (d.diffBC + d.m) ^ 2 + (d.sumEF - d.diffEF) ^ 2 +
      (2 * p.a + d.m + d.diffBC) ^ 2 * d.xi := by
  simp only [Parameters.s1, diffBC, diffEF, sumBC, sumEF, m, xi]
  rw [d.original_x_sq]
  ring

lemma two_x_R_alternate (h : CriticalPoint p) :
    2 * d.x * d.R =
      d.sumEF * (d.m + (2 * p.a + d.m) * d.xi) +
        d.diffBC * d.diffEF * d.xi := by
  have hR := d.two_x_R h
  simp only [sumBC, sumEF, diffBC, diffEF, m, xi] at hR ⊢
  nlinarith

/-- The exact square identity.  This proof is a kernel-checked polynomial
certificate after the three displayed substitutions. -/
lemma square_certificate (h : CriticalPoint p) :
    16 * d.xi * (p.r1 * p.s1 - d.R ^ 2) =
      d.xi * (d.eta + d.scriptL) ^ 2 -
        4 * (d.tau + d.beta * d.xi) * d.scriptM := by
  have hr1 : p.r1 =
      ((d.diffBC - d.m) ^ 2 + (d.sumEF + d.diffEF) ^ 2 +
        (2 * p.a + d.m - d.diffBC) ^ 2 * d.xi) / 4 := by
    nlinarith [d.four_r1]
  have hs1 : p.s1 =
      ((d.diffBC + d.m) ^ 2 + (d.sumEF - d.diffEF) ^ 2 +
        (2 * p.a + d.m + d.diffBC) ^ 2 * d.xi) / 4 := by
    nlinarith [d.four_s1]
  have hxne : d.x ≠ 0 := ne_of_gt d.x_pos
  have hR : d.R =
      (d.sumEF * (d.m + (2 * p.a + d.m) * d.xi) +
        d.diffBC * d.diffEF * d.xi) / (2 * d.x) := by
    apply (eq_div_iff (by positivity)).2
    nlinarith [d.two_x_R_alternate h]
  rw [hr1, hs1, hR]
  simp only [xi, beta, eta, tau, scriptL, scriptM]
  field_simp [hxne]
  ring

lemma scriptM_nonneg (h : CriticalPoint p) : 0 ≤ d.scriptM := by
  have hcert := d.square_certificate h
  have hzero : p.r1 * p.s1 - d.R ^ 2 = 0 := by rw [← d.R_sq]; ring
  rw [hzero] at hcert
  have hxi : 0 < d.xi := by simp only [xi]; exact sq_pos_of_pos d.x_pos
  have htau : 0 < d.tau := by simp only [tau]; exact sq_pos_of_pos (d.sumEF_pos h)
  have hbeta : 0 ≤ d.beta := by simp only [beta]; positivity
  have hcoeff : 0 < d.tau + d.beta * d.xi := by positivity
  by_contra hn
  have hM : d.scriptM < 0 := lt_of_not_ge hn
  have hrhs : 4 * (d.tau + d.beta * d.xi) * d.scriptM < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by norm_num) hcoeff) hM
  have hlhs : 0 ≤ d.xi * (d.eta + d.scriptL) ^ 2 := by positivity
  nlinarith

lemma beta_mul_xi_bound (h : CriticalPoint p) :
    d.beta * d.xi ≤ 4 * p.a * d.m * d.xi + d.m ^ 2 * (1 + d.xi) := by
  have hM := d.scriptM_nonneg h
  simp only [scriptM] at hM
  nlinarith

lemma anisotropy_bound (h : CriticalPoint p) :
    d.beta < 6 * p.a * d.m ∧ 6 * p.a * d.m < 4 * p.a * (p.a + d.m) := by
  have hm := d.m_pos h
  have hxi : 0 < d.xi := by simp only [xi]; exact sq_pos_of_pos d.x_pos
  have hchamber := d.x_chamber h
  have hm_mul : d.m ^ 2 < d.m * ((2 * p.a - d.m) * d.x ^ 2) := by
    have := mul_lt_mul_of_pos_left hchamber hm
    nlinarith
  have hraw := d.beta_mul_xi_bound h
  have hstrict : d.beta * d.xi < 6 * p.a * d.m * d.xi := by
    simp only [xi] at hraw ⊢
    nlinarith
  have hbeta : d.beta < 6 * p.a * d.m := by
    by_contra hn
    have hge : 6 * p.a * d.m ≤ d.beta := le_of_not_gt hn
    have hmul := mul_le_mul_of_nonneg_right hge (le_of_lt hxi)
    linarith
  constructor
  · exact hbeta
  · have := d.m_lt_two_a h
    nlinarith [h.a_pos, mul_pos h.a_pos (by linarith : 0 < 2 * p.a - d.m)]

noncomputable def k : ℝ := d.R / p.r1
noncomputable def ell : ℝ := d.V / p.r2

lemma k_pos (h : CriticalPoint p) : 0 < d.k := div_pos d.R_pos (r1_pos h)
lemma ell_pos (h : CriticalPoint p) : 0 < d.ell := div_pos d.V_pos (r2_pos h)

lemma u_yz : p.u * (p.y * p.z) = d.R * d.rho := by
  rw [d.u_eq, d.yz]
  calc
    d.eps * d.R * (d.eps * d.rho) = d.eps ^ 2 * (d.R * d.rho) := by ring
    _ = d.R * d.rho := by rw [d.eps_sq]; ring

lemma v_wt : p.v * (p.w * p.t) = d.V * d.omega := by
  rw [d.v_eq, d.wt]
  calc
    -d.eps * d.V * (-d.eps * d.omega) = d.eps ^ 2 * (d.V * d.omega) := by ring
    _ = d.V * d.omega := by rw [d.eps_sq]; ring

lemma y_sq (h : CriticalPoint p) : p.y ^ 2 = d.k * d.rho := by
  have heq := congrArg (fun q : ℝ ↦ q * p.y) h.pairYZ₁
  have hrel : p.r1 * p.y ^ 2 = d.R * d.rho := by
    calc
      p.r1 * p.y ^ 2 = (p.r1 * p.y) * p.y := by ring
      _ = (p.u * p.z) * p.y := by rw [h.pairYZ₁]
      _ = p.u * (p.y * p.z) := by ring
      _ = d.R * d.rho := d.u_yz
  simp only [k]
  field_simp [ne_of_gt (r1_pos h)]
  nlinarith

lemma z_sq (h : CriticalPoint p) : p.z ^ 2 = d.rho / d.k := by
  have hrel : p.s1 * p.z ^ 2 = d.R * d.rho := by
    calc
      p.s1 * p.z ^ 2 = (p.s1 * p.z) * p.z := by ring
      _ = (p.u * p.y) * p.z := by rw [h.pairYZ₂]
      _ = p.u * (p.y * p.z) := by ring
      _ = d.R * d.rho := d.u_yz
  have hk : d.k ≠ 0 := ne_of_gt (d.k_pos h)
  have hR : d.R ≠ 0 := ne_of_gt d.R_pos
  have hcancel : p.z ^ 2 * d.R = p.r1 * d.rho := by
    apply mul_left_cancel₀ hR
    calc
      d.R * (p.z ^ 2 * d.R) = (p.r1 * p.s1) * p.z ^ 2 := by
        rw [← d.R_sq]
        ring
      _ = p.r1 * (p.s1 * p.z ^ 2) := by ring
      _ = p.r1 * (d.R * d.rho) := by rw [hrel]
      _ = d.R * (p.r1 * d.rho) := by ring
  apply (eq_div_iff hk).2
  simp only [k]
  field_simp [ne_of_gt (r1_pos h)]
  nlinarith

lemma w_sq (h : CriticalPoint p) : p.w ^ 2 = d.ell * d.omega := by
  have hrel : p.r2 * p.w ^ 2 = d.V * d.omega := by
    calc
      p.r2 * p.w ^ 2 = (p.r2 * p.w) * p.w := by ring
      _ = (p.v * p.t) * p.w := by rw [h.pairWT₁]
      _ = p.v * (p.w * p.t) := by ring
      _ = d.V * d.omega := d.v_wt
  simp only [ell]
  field_simp [ne_of_gt (r2_pos h)]
  nlinarith

lemma t_sq (h : CriticalPoint p) : p.t ^ 2 = d.omega / d.ell := by
  have hrel : p.s2 * p.t ^ 2 = d.V * d.omega := by
    calc
      p.s2 * p.t ^ 2 = (p.s2 * p.t) * p.t := by ring
      _ = (p.v * p.w) * p.t := by rw [h.pairWT₂]
      _ = p.v * (p.w * p.t) := by ring
      _ = d.V * d.omega := d.v_wt
  have hell : d.ell ≠ 0 := ne_of_gt (d.ell_pos h)
  have hV : d.V ≠ 0 := ne_of_gt d.V_pos
  have hcancel : p.t ^ 2 * d.V = p.r2 * d.omega := by
    apply mul_left_cancel₀ hV
    calc
      d.V * (p.t ^ 2 * d.V) = (p.r2 * p.s2) * p.t ^ 2 := by
        rw [← d.V_sq]
        ring
      _ = p.r2 * (p.s2 * p.t ^ 2) := by ring
      _ = p.r2 * (d.V * d.omega) := by rw [hrel]
      _ = d.V * (p.r2 * d.omega) := by ring
  apply (eq_div_iff hell).2
  simp only [ell]
  field_simp [ne_of_gt (r2_pos h)]
  nlinarith

def UB : ℝ := p.a - p.b * (1 + d.x ^ 2)
def UC : ℝ := p.a - p.c * (1 + d.x ^ 2)

noncomputable def Tplus : ℝ :=
  p.b * d.UB / d.k - p.c * d.UC * d.k +
    d.x * (p.b * p.e - p.c * p.f)

noncomputable def Tminus : ℝ :=
  p.b * d.UB * d.ell - p.c * d.UC / d.ell +
    d.x * (p.b * p.f - p.c * p.e)

def Hminus : ℝ :=
  p.a * (1 + d.x ^ 2) * (d.m ^ 2 - d.diffBC ^ 2) -
    4 * p.a ^ 3 * d.x ^ 2 - p.a * d.sumEF ^ 2 -
    (p.a + d.m) * d.diffEF ^ 2 - d.diffBC * d.diffEF * d.sumEF

def Hplus : ℝ :=
  p.a * (1 + d.x ^ 2) * (d.m ^ 2 - d.diffBC ^ 2) -
    4 * p.a ^ 3 * d.x ^ 2 - p.a * d.sumEF ^ 2 -
    (p.a + d.m) * d.diffEF ^ 2 + d.diffBC * d.diffEF * d.sumEF

lemma diagonal_difference_decomposition (h : CriticalPoint p) :
    p.diagonalDifference =
      d.diffBC * (p.a - d.sumBC * (1 + d.x ^ 2)) +
        d.rho * d.Tplus + d.omega * d.Tminus := by
  have hy := d.y_sq h
  have hz := d.z_sq h
  have hw := d.w_sq h
  have ht := d.t_sq h
  have hgrouped : p.diagonalDifference =
      p.a * p.b - p.a * p.c - (p.b ^ 2 - p.c ^ 2) * (1 + p.x ^ 2) +
      p.b * (p.a - p.b * (1 + p.x ^ 2)) * (p.w ^ 2 + p.z ^ 2) -
      p.c * (p.a - p.c * (1 + p.x ^ 2)) * (p.y ^ 2 + p.t ^ 2) +
      p.x * (p.b * p.e - p.c * p.f) * (p.y * p.z) +
      p.x * (p.c * p.e - p.b * p.f) * (p.w * p.t) := by
    simp only [Parameters.diagonalDifference]
    ring
  rw [hgrouped]
  simp only [diffBC, sumBC, Tplus, Tminus, UB, UC]
  rw [d.original_x_sq, d.original_x, d.yz, d.wt, hy, hz, hw, ht]
  have hk : d.k ≠ 0 := ne_of_gt (d.k_pos h)
  have hell : d.ell ≠ 0 := ne_of_gt (d.ell_pos h)
  field_simp [hk, hell]
  rw [d.eps_sq]
  ring

lemma R_div_k (h : CriticalPoint p) : d.R / d.k = p.r1 := by
  simp only [k]
  field_simp [ne_of_gt d.R_pos, ne_of_gt (r1_pos h)]

lemma R_mul_k (h : CriticalPoint p) : d.R * d.k = p.s1 := by
  simp only [k]
  field_simp [ne_of_gt (r1_pos h)]
  nlinarith [d.R_sq]

lemma V_div_ell (h : CriticalPoint p) : d.V / d.ell = p.r2 := by
  simp only [ell]
  field_simp [ne_of_gt d.V_pos, ne_of_gt (r2_pos h)]

lemma V_mul_ell (h : CriticalPoint p) : d.V * d.ell = p.s2 := by
  simp only [ell]
  field_simp [ne_of_gt (r2_pos h)]
  nlinarith [d.V_sq]

lemma R_Tplus_raw (h : CriticalPoint p) :
    d.R * d.Tplus =
      p.r1 * p.b * d.UB - p.s1 * p.c * d.UC +
        d.x * d.R * (p.b * p.e - p.c * p.f) := by
  simp only [Tplus]
  calc
    d.R * (p.b * d.UB / d.k - p.c * d.UC * d.k +
        d.x * (p.b * p.e - p.c * p.f)) =
      p.b * d.UB * (d.R / d.k) - p.c * d.UC * (d.R * d.k) +
        d.x * d.R * (p.b * p.e - p.c * p.f) := by ring
    _ = p.r1 * p.b * d.UB - p.s1 * p.c * d.UC +
        d.x * d.R * (p.b * p.e - p.c * p.f) := by
          rw [d.R_div_k h, d.R_mul_k h]
          ring

lemma V_Tminus_raw (h : CriticalPoint p) :
    d.V * d.Tminus =
      p.s2 * p.b * d.UB - p.r2 * p.c * d.UC +
        d.x * d.V * (p.b * p.f - p.c * p.e) := by
  simp only [Tminus]
  calc
    d.V * (p.b * d.UB * d.ell - p.c * d.UC / d.ell +
        d.x * (p.b * p.f - p.c * p.e)) =
      p.b * d.UB * (d.V * d.ell) - p.c * d.UC * (d.V / d.ell) +
        d.x * d.V * (p.b * p.f - p.c * p.e) := by ring
    _ = p.s2 * p.b * d.UB - p.r2 * p.c * d.UC +
        d.x * d.V * (p.b * p.f - p.c * p.e) := by
          rw [d.V_mul_ell h, d.V_div_ell h]
          ring

lemma four_r2 :
    4 * p.r2 = (d.diffBC + d.m) ^ 2 + (d.sumEF + d.diffEF) ^ 2 +
      (2 * p.a + d.m + d.diffBC) ^ 2 * d.xi := by
  simp only [Parameters.r2, diffBC, diffEF, sumBC, sumEF, m, xi]
  rw [d.original_x_sq]
  ring

lemma four_s2 :
    4 * p.s2 = (d.diffBC - d.m) ^ 2 + (d.sumEF - d.diffEF) ^ 2 +
      (2 * p.a + d.m - d.diffBC) ^ 2 * d.xi := by
  simp only [Parameters.s2, diffBC, diffEF, sumBC, sumEF, m, xi]
  rw [d.original_x_sq]
  ring

lemma two_x_V_alternate (h : CriticalPoint p) :
    2 * d.x * d.V =
      d.sumEF * (d.m + (2 * p.a + d.m) * d.xi) -
        d.diffBC * d.diffEF * d.xi := by
  have hV := d.two_x_V h
  simp only [sumBC, sumEF, diffBC, diffEF, m, xi] at hV ⊢
  nlinarith

/-- First denominator-free factorization in the decisive diagonal difference. -/
lemma Tplus_factor (h : CriticalPoint p) :
    4 * d.R * d.Tplus = d.diffBC * d.Hminus := by
  rw [show 4 * d.R * d.Tplus = 4 * (d.R * d.Tplus) by ring, d.R_Tplus_raw h]
  have hr1 : p.r1 = ((d.diffBC - d.m) ^ 2 + (d.sumEF + d.diffEF) ^ 2 +
      (2 * p.a + d.m - d.diffBC) ^ 2 * d.xi) / 4 := by
    nlinarith [d.four_r1]
  have hs1 : p.s1 = ((d.diffBC + d.m) ^ 2 + (d.sumEF - d.diffEF) ^ 2 +
      (2 * p.a + d.m + d.diffBC) ^ 2 * d.xi) / 4 := by
    nlinarith [d.four_s1]
  have hxR : d.x * d.R =
      (d.sumEF * (d.m + (2 * p.a + d.m) * d.xi) +
        d.diffBC * d.diffEF * d.xi) / 2 := by
    nlinarith [d.two_x_R_alternate h]
  rw [hr1, hs1, hxR]
  simp only [UB, UC, Hminus, sumBC, sumEF, diffBC, diffEF, m, xi]
  ring

/-- Second denominator-free factorization in the decisive diagonal difference. -/
lemma Tminus_factor (h : CriticalPoint p) :
    4 * d.V * d.Tminus = d.diffBC * d.Hplus := by
  rw [show 4 * d.V * d.Tminus = 4 * (d.V * d.Tminus) by ring, d.V_Tminus_raw h]
  have hr2 : p.r2 = ((d.diffBC + d.m) ^ 2 + (d.sumEF + d.diffEF) ^ 2 +
      (2 * p.a + d.m + d.diffBC) ^ 2 * d.xi) / 4 := by
    nlinarith [d.four_r2]
  have hs2 : p.s2 = ((d.diffBC - d.m) ^ 2 + (d.sumEF - d.diffEF) ^ 2 +
      (2 * p.a + d.m - d.diffBC) ^ 2 * d.xi) / 4 := by
    nlinarith [d.four_s2]
  have hxV : d.x * d.V =
      (d.sumEF * (d.m + (2 * p.a + d.m) * d.xi) -
        d.diffBC * d.diffEF * d.xi) / 2 := by
    nlinarith [d.two_x_V_alternate h]
  rw [hr2, hs2, hxV]
  simp only [UB, UC, Hplus, sumBC, sumEF, diffBC, diffEF, m, xi]
  ring

lemma chamber_quadratic_negative (h : CriticalPoint p) :
    (1 + d.x ^ 2) * d.m ^ 2 - 4 * p.a ^ 2 * d.x ^ 2 < 0 := by
  have hm := d.m_pos h
  have h2am := d.m_lt_two_a h
  have hch := d.x_chamber h
  have hfactor : 0 < 2 * p.a + d.m := by nlinarith [h.a_pos]
  have hmul := mul_lt_mul_of_pos_left hch hfactor
  have hmself : d.m ^ 2 < (2 * p.a + d.m) * d.m := by
    have : d.m < 2 * p.a + d.m := by nlinarith [h.a_pos]
    have := mul_lt_mul_of_pos_left this hm
    nlinarith
  have hlarge : d.m ^ 2 < (4 * p.a ^ 2 - d.m ^ 2) * d.x ^ 2 := by
    calc
      d.m ^ 2 < (2 * p.a + d.m) * d.m := hmself
      _ < (2 * p.a + d.m) * ((2 * p.a - d.m) * d.x ^ 2) := hmul
      _ = (4 * p.a ^ 2 - d.m ^ 2) * d.x ^ 2 := by ring
  nlinarith

lemma first_H_term_negative (h : CriticalPoint p) :
    p.a * (1 + d.x ^ 2) * (d.m ^ 2 - d.diffBC ^ 2) -
      4 * p.a ^ 3 * d.x ^ 2 < 0 := by
  have hbase := d.chamber_quadratic_negative h
  have hscaled : p.a * ((1 + d.x ^ 2) * d.m ^ 2 -
      4 * p.a ^ 2 * d.x ^ 2) < 0 := mul_neg_of_pos_of_neg h.a_pos hbase
  have hsubtract : 0 ≤ p.a * (1 + d.x ^ 2) * d.diffBC ^ 2 := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt h.a_pos) (by nlinarith [sq_nonneg d.x]))
      (sq_nonneg d.diffBC)
  nlinarith

lemma quadratic_plus_pos (h : CriticalPoint p) :
    0 < p.a * d.sumEF ^ 2 + (p.a + d.m) * d.diffEF ^ 2 +
      d.diffBC * d.diffEF * d.sumEF := by
  have hbounds := d.anisotropy_bound h
  have hbound := lt_trans hbounds.1 hbounds.2
  have hcoeff : 0 < 4 * p.a * (p.a + d.m) - d.diffBC ^ 2 := by
    simp only [beta] at hbound
    linarith
  have he2 : 0 < d.diffEF ^ 2 :=
    sq_pos_of_ne_zero (by simpa [diffEF, sub_ne_zero] using d.ef_ne)
  have hpositive : 0 <
      (2 * p.a * d.sumEF + d.diffBC * d.diffEF) ^ 2 +
        (4 * p.a * (p.a + d.m) - d.diffBC ^ 2) * d.diffEF ^ 2 := by
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hcoeff he2)
  have hid :
      4 * p.a * (p.a * d.sumEF ^ 2 + (p.a + d.m) * d.diffEF ^ 2 +
        d.diffBC * d.diffEF * d.sumEF) =
      (2 * p.a * d.sumEF + d.diffBC * d.diffEF) ^ 2 +
        (4 * p.a * (p.a + d.m) - d.diffBC ^ 2) * d.diffEF ^ 2 := by ring
  have hfoura : 0 < 4 * p.a := by nlinarith [h.a_pos]
  rw [← hid] at hpositive
  rcases mul_pos_iff.mp hpositive with hcase | hcase
  · exact hcase.2
  · exact False.elim ((not_lt_of_ge (le_of_lt hfoura)) hcase.1)

lemma quadratic_minus_pos (h : CriticalPoint p) :
    0 < p.a * d.sumEF ^ 2 + (p.a + d.m) * d.diffEF ^ 2 -
      d.diffBC * d.diffEF * d.sumEF := by
  have hbounds := d.anisotropy_bound h
  have hbound := lt_trans hbounds.1 hbounds.2
  have hcoeff : 0 < 4 * p.a * (p.a + d.m) - d.diffBC ^ 2 := by
    simp only [beta] at hbound
    linarith
  have he2 : 0 < d.diffEF ^ 2 :=
    sq_pos_of_ne_zero (by simpa [diffEF, sub_ne_zero] using d.ef_ne)
  have hpositive : 0 <
      (2 * p.a * d.sumEF - d.diffBC * d.diffEF) ^ 2 +
        (4 * p.a * (p.a + d.m) - d.diffBC ^ 2) * d.diffEF ^ 2 := by
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hcoeff he2)
  have hid :
      4 * p.a * (p.a * d.sumEF ^ 2 + (p.a + d.m) * d.diffEF ^ 2 -
        d.diffBC * d.diffEF * d.sumEF) =
      (2 * p.a * d.sumEF - d.diffBC * d.diffEF) ^ 2 +
        (4 * p.a * (p.a + d.m) - d.diffBC ^ 2) * d.diffEF ^ 2 := by ring
  have hfoura : 0 < 4 * p.a := by nlinarith [h.a_pos]
  rw [← hid] at hpositive
  rcases mul_pos_iff.mp hpositive with hcase | hcase
  · exact hcase.2
  · exact False.elim ((not_lt_of_ge (le_of_lt hfoura)) hcase.1)

lemma Hminus_neg (h : CriticalPoint p) : d.Hminus < 0 := by
  have hfirst := d.first_H_term_negative h
  have hquad := d.quadratic_plus_pos h
  simp only [Hminus]
  nlinarith

lemma Hplus_neg (h : CriticalPoint p) : d.Hplus < 0 := by
  have hfirst := d.first_H_term_negative h
  have hquad := d.quadratic_minus_pos h
  simp only [Hplus]
  nlinarith

lemma diff_mul_Tplus_neg (h : CriticalPoint p) : d.diffBC * d.Tplus < 0 := by
  have hb2 : 0 < d.diffBC ^ 2 :=
    sq_pos_of_ne_zero (by simpa [diffBC, sub_ne_zero] using d.bc_ne)
  have hrhs : d.diffBC ^ 2 * d.Hminus < 0 :=
    mul_neg_of_pos_of_neg hb2 (d.Hminus_neg h)
  have heq : 4 * d.R * (d.diffBC * d.Tplus) =
      d.diffBC ^ 2 * d.Hminus := by
    calc
      4 * d.R * (d.diffBC * d.Tplus) = d.diffBC * (4 * d.R * d.Tplus) := by ring
      _ = d.diffBC * (d.diffBC * d.Hminus) := by rw [d.Tplus_factor h]
      _ = d.diffBC ^ 2 * d.Hminus := by ring
  have hscaled : 4 * d.R * (d.diffBC * d.Tplus) < 0 := heq.symm ▸ hrhs
  have hcoeff : 0 < 4 * d.R := by nlinarith [d.R_pos]
  rcases mul_neg_iff.mp hscaled with hcase | hcase
  · exact hcase.2
  · exact False.elim ((not_lt_of_ge (le_of_lt hcoeff)) hcase.1)

lemma diff_mul_Tminus_neg (h : CriticalPoint p) : d.diffBC * d.Tminus < 0 := by
  have hb2 : 0 < d.diffBC ^ 2 :=
    sq_pos_of_ne_zero (by simpa [diffBC, sub_ne_zero] using d.bc_ne)
  have hrhs : d.diffBC ^ 2 * d.Hplus < 0 :=
    mul_neg_of_pos_of_neg hb2 (d.Hplus_neg h)
  have heq : 4 * d.V * (d.diffBC * d.Tminus) =
      d.diffBC ^ 2 * d.Hplus := by
    calc
      4 * d.V * (d.diffBC * d.Tminus) = d.diffBC * (4 * d.V * d.Tminus) := by ring
      _ = d.diffBC * (d.diffBC * d.Hplus) := by rw [d.Tminus_factor h]
      _ = d.diffBC ^ 2 * d.Hplus := by ring
  have hscaled : 4 * d.V * (d.diffBC * d.Tminus) < 0 := heq.symm ▸ hrhs
  have hcoeff : 0 < 4 * d.V := by nlinarith [d.V_pos]
  rcases mul_neg_iff.mp hscaled with hcase | hcase
  · exact hcase.2
  · exact False.elim ((not_lt_of_ge (le_of_lt hcoeff)) hcase.1)

lemma final_diagonal_negative (h : CriticalPoint p) :
    d.diffBC * p.diagonalDifference < 0 := by
  have hbaseInside : p.a - d.sumBC * (1 + d.x ^ 2) < 0 := by
    have hs := d.m_pos h
    have hs2a : 2 * p.a < d.sumBC := by simp only [m] at hs; linarith
    have hnonneg : 0 ≤ d.sumBC * d.x ^ 2 :=
      mul_nonneg (le_of_lt (d.sumBC_pos h)) (sq_nonneg d.x)
    have hid : d.sumBC * (1 + d.x ^ 2) =
        d.sumBC + d.sumBC * d.x ^ 2 := by ring
    rw [hid]
    have ha_lt : p.a < 2 * p.a := by nlinarith [h.a_pos]
    linarith
  have hb2 : 0 < d.diffBC ^ 2 :=
    sq_pos_of_ne_zero (by simpa [diffBC, sub_ne_zero] using d.bc_ne)
  have hbase : d.diffBC ^ 2 *
      (p.a - d.sumBC * (1 + d.x ^ 2)) < 0 :=
    mul_neg_of_pos_of_neg hb2 hbaseInside
  have hplus : d.rho * (d.diffBC * d.Tplus) < 0 :=
    mul_neg_of_pos_of_neg d.rho_pos (d.diff_mul_Tplus_neg h)
  have hminus : d.omega * (d.diffBC * d.Tminus) < 0 :=
    mul_neg_of_pos_of_neg d.omega_pos (d.diff_mul_Tminus_neg h)
  rw [d.diagonal_difference_decomposition h]
  have hid : d.diffBC *
      (d.diffBC * (p.a - d.sumBC * (1 + d.x ^ 2)) +
        d.rho * d.Tplus + d.omega * d.Tminus) =
      d.diffBC ^ 2 * (p.a - d.sumBC * (1 + d.x ^ 2)) +
        d.rho * (d.diffBC * d.Tplus) +
        d.omega * (d.diffBC * d.Tminus) := by ring
  rw [hid]
  linarith

lemma contradiction (d : SignData p) (h : CriticalPoint p) : False := by
  have hneg := d.final_diagonal_negative h
  rw [h.diagonalBC] at hneg
  norm_num at hneg

end SignData

/-- The fully mixed anisotropic branch of the reduced trace `-2` system is empty. -/
theorem no_fully_mixed {p : Parameters} (h : CriticalPoint p) : ¬ FullyMixed p := by
  intro hm
  exact (Classical.choice (exists_signData h hm)).contradiction h

/-- Polynomial form of the new trace `-2` exclusion theorem. -/
theorem degeneracy_product_eq_zero {p : Parameters} (h : CriticalPoint p) :
    (p.y * p.z) * (p.w * p.t) * (p.b - p.c) * (p.e - p.f) = 0 := by
  by_contra hprod
  have h₁ : p.y * p.z ≠ 0 := by
    intro hz
    apply hprod
    simp [hz]
  have h₂ : p.w * p.t ≠ 0 := by
    intro hz
    apply hprod
    simp [hz]
  have h₃ : p.b ≠ p.c := by
    intro heq
    apply hprod
    simp [heq]
  have h₄ : p.e ≠ p.f := by
    intro heq
    apply hprod
    simp [heq]
  exact no_fully_mixed h ⟨h₁, h₂, h₃, h₄⟩

lemma row_orthogonality_of_b_eq_c {p : Parameters} (h : CriticalPoint p)
    (hbc : p.b = p.c) : p.y * p.t + p.w * p.z = 0 := by
  have huv : p.u + p.v = 0 := by rw [u_add_v, hbc]; ring
  have hr : p.r1 = p.r2 := by
    simp only [Parameters.r1, Parameters.r2, hbc]
  have heq : p.r1 * (p.y * p.t + p.w * p.z) = 0 := by
    calc
      p.r1 * (p.y * p.t + p.w * p.z) =
          (p.r1 * p.y) * p.t + (p.r2 * p.w) * p.z := by rw [hr]; ring
      _ = (p.u * p.z) * p.t + (p.v * p.t) * p.z := by
        rw [h.pairYZ₁, h.pairWT₁]
      _ = (p.u + p.v) * (p.z * p.t) := by ring
      _ = 0 := by rw [huv]; ring
  exact (mul_eq_zero.mp heq).resolve_left (ne_of_gt (r1_pos h))

lemma column_orthogonality_of_e_eq_f {p : Parameters} (h : CriticalPoint p)
    (hef : p.e = p.f) : p.y * p.w + p.t * p.z = 0 := by
  have huv : p.u + p.v = 0 := by rw [u_add_v, hef]; ring
  have hr : p.r1 = p.s2 := by
    simp only [Parameters.r1, Parameters.s2, hef]
  have heq : p.r1 * (p.y * p.w + p.t * p.z) = 0 := by
    calc
      p.r1 * (p.y * p.w + p.t * p.z) =
          (p.r1 * p.y) * p.w + (p.s2 * p.t) * p.z := by rw [hr]; ring
      _ = (p.u * p.z) * p.w + (p.v * p.w) * p.z := by
        rw [h.pairYZ₁, h.pairWT₂]
      _ = (p.u + p.v) * (p.z * p.w) := by ring
      _ = 0 := by rw [huv]; ring
  exact (mul_eq_zero.mp heq).resolve_left (ne_of_gt (r1_pos h))

/-- The four explicit degenerate alternatives used in the symmetry-enhancement step. -/
def DegenerateNormalizable (p : Parameters) : Prop :=
  (p.y = 0 ∧ p.z = 0) ∨
  (p.w = 0 ∧ p.t = 0) ∨
  (p.b = p.c ∧ p.y * p.t + p.w * p.z = 0) ∨
  (p.e = p.f ∧ p.y * p.w + p.t * p.z = 0)

theorem degenerate_normalizable {p : Parameters} (h : CriticalPoint p) :
    DegenerateNormalizable p := by
  have hprod := degeneracy_product_eq_zero h
  rcases mul_eq_zero.mp hprod with hleft | hef
  · rcases mul_eq_zero.mp hleft with hleft | hbc
    · rcases mul_eq_zero.mp hleft with hyz | hwt
      · left
        rcases mul_eq_zero.mp hyz with hy | hz
        · exact ⟨hy, (pair_zero_YZ h).mp hy⟩
        · exact ⟨(pair_zero_YZ h).mpr hz, hz⟩
      · right; left
        rcases mul_eq_zero.mp hwt with hw | ht
        · exact ⟨hw, (pair_zero_WT h).mp hw⟩
        · exact ⟨(pair_zero_WT h).mpr ht, ht⟩
    · right; right; left
      have hbc' : p.b = p.c := sub_eq_zero.mp hbc
      exact ⟨hbc', row_orthogonality_of_b_eq_c h hbc'⟩
  · right; right; right
    have hef' : p.e = p.f := sub_eq_zero.mp hef
    exact ⟨hef', column_orthogonality_of_e_eq_f h hef'⟩

/-! ## Explicit two-dimensional rotations -/

abbrev I2 := Fin 2
abbrev Mat2 := Matrix I2 I2 ℝ
abbrev SO2 := Matrix.specialOrthogonalGroup I2 ℝ

def IsDiagonal2 (N : Mat2) : Prop := N 0 1 = 0 ∧ N 1 0 = 0

def quarterTurn : SO2 :=
  ⟨!![0, -1; 1, 0], by
    rw [Matrix.mem_specialOrthogonalGroup_fin_two_iff]
    norm_num⟩

lemma quarterTurn_right_diagonalizes_antidiagonal (a b : ℝ) :
    IsDiagonal2 (!![0, a; b, 0] * ((quarterTurn : SO2) : Mat2)ᵀ) := by
  constructor <;>
    simp [quarterTurn, Matrix.mul_apply, Fin.sum_univ_succ]

/-- An explicit `SO(2)` rotation diagonalizing a matrix with two orthogonal,
nonzero rows. -/
lemma diagonalize_orthogonal_rows {a b c e : ℝ}
    (hnorm : 0 < a ^ 2 + b ^ 2) (horth : a * c + b * e = 0) :
    ∃ Q : SO2, IsDiagonal2 (!![a, b; c, e] * (Q : Mat2)ᵀ) := by
  let r : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  have hr : 0 < r := Real.sqrt_pos.2 hnorm
  have hrne : r ≠ 0 := ne_of_gt hr
  have hrsq : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (le_of_lt hnorm)
  let Qm : Mat2 := !![a / r, b / r; -b / r, a / r]
  have hQ : Qm ∈ Matrix.specialOrthogonalGroup I2 ℝ := by
    rw [Matrix.mem_specialOrthogonalGroup_fin_two_iff]
    dsimp [Qm]
    constructor
    · rfl
    constructor
    · ring
    · field_simp [hrne]
      nlinarith
  let Q : SO2 := ⟨Qm, hQ⟩
  refine ⟨Q, ?_⟩
  constructor
  · dsimp [Q, Qm]
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
    field_simp [hrne]
    ring
  · dsimp [Q, Qm]
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
    field_simp [hrne]
    nlinarith

/-- Column version; the action is on the left and is deliberately kept
separate to make transpose conventions explicit. -/
lemma diagonalize_orthogonal_columns {a b c e : ℝ}
    (hnorm : 0 < a ^ 2 + c ^ 2) (horth : a * b + c * e = 0) :
    ∃ Q : SO2, IsDiagonal2 ((Q : Mat2) * !![a, b; c, e]) := by
  obtain ⟨Q, hQ⟩ := diagonalize_orthogonal_rows
    (a := a) (b := c) (c := b) (e := e) hnorm horth
  refine ⟨Q, ?_⟩
  have heq : (((Q : Mat2) * !![a, b; c, e])ᵀ) =
      !![a, c; b, e] * (Q : Mat2)ᵀ := by
    rw [Matrix.transpose_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  constructor
  · change (((Q : Mat2) * !![a, b; c, e])ᵀ) 1 0 = 0
    rw [heq]
    exact hQ.2
  · change (((Q : Mat2) * !![a, b; c, e])ᵀ) 0 1 = 0
    rw [heq]
    exact hQ.1

/-! ## Embedding the plane rotations in the inner action -/

/-- The orientation-preserving extension of a two-dimensional rotation which
fixes the first coordinate axis. -/
def extendSO2Matrix (Q : SO2) : Mat3 :=
  !![1, 0, 0;
     0, (Q : Mat2) 0 0, (Q : Mat2) 0 1;
     0, (Q : Mat2) 1 0, (Q : Mat2) 1 1]

def extendSO2 (Q : SO2) : SO3 := by
  refine ⟨extendSO2Matrix Q, ?_⟩
  rcases Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp Q.property with
    ⟨hdiag, hoff, hsquare⟩
  have hoff' : (Q : Mat2) 1 0 = -(Q : Mat2) 0 1 := by linarith
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [extendSO2Matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      try simp only [← hdiag, hoff'] <;> nlinarith [hsquare]
    all_goals nlinarith [hsquare]
  · rw [Matrix.det_fin_three]
    simp [extendSO2Matrix]
    simp only [← hdiag, hoff']
    nlinarith [hsquare]

@[simp]
lemma extendSO2_coe (Q : SO2) : (extendSO2 Q : Mat3) = extendSO2Matrix Q := rfl

/-- The three nonidentity diagonal half turns. -/
def halfTurn1 : SO3 :=
  ⟨Matrix.diagonal ![1, -1, -1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    · rw [Matrix.mem_orthogonalGroup_iff]
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> norm_num
    · rw [Matrix.det_diagonal]
      norm_num [Fin.prod_univ_succ]⟩

def halfTurn2 : SO3 :=
  ⟨Matrix.diagonal ![-1, 1, -1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    · rw [Matrix.mem_orthogonalGroup_iff]
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> norm_num
    · rw [Matrix.det_diagonal]
      norm_num [Fin.prod_univ_succ]⟩

def halfTurn3 : SO3 :=
  ⟨Matrix.diagonal ![-1, -1, 1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    · rw [Matrix.mem_orthogonalGroup_iff]
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> norm_num
    · rw [Matrix.det_diagonal]
      norm_num [Fin.prod_univ_succ]⟩

@[simp] lemma halfTurn1_sq : halfTurn1 * halfTurn1 = 1 := by
  apply Subtype.ext
  change Matrix.diagonal ![1, -1, -1] * Matrix.diagonal ![1, -1, -1] = 1
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num

@[simp] lemma halfTurn2_sq : halfTurn2 * halfTurn2 = 1 := by
  apply Subtype.ext
  change Matrix.diagonal ![-1, 1, -1] * Matrix.diagonal ![-1, 1, -1] = 1
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num

@[simp] lemma halfTurn3_sq : halfTurn3 * halfTurn3 = 1 := by
  apply Subtype.ext
  change Matrix.diagonal ![-1, -1, 1] * Matrix.diagonal ![-1, -1, 1] = 1
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num

lemma halfTurn1_mul_halfTurn2 : halfTurn1 * halfTurn2 = halfTurn3 := by
  apply Subtype.ext
  change Matrix.diagonal ![1, -1, -1] * Matrix.diagonal ![-1, 1, -1] =
    Matrix.diagonal ![-1, -1, 1]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> norm_num

lemma halfTurn2_mul_halfTurn1 : halfTurn2 * halfTurn1 = halfTurn3 := by
  apply Subtype.ext
  change Matrix.diagonal ![-1, 1, -1] * Matrix.diagonal ![1, -1, -1] =
    Matrix.diagonal ![-1, -1, 1]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> norm_num

/-! ## A literal Klein-four subgroup -/

/-- Cancel the `Multiplicative (Additive G)` wrappers without changing the
group operation. -/
def mulAddCancel {G : Type*} [Group G] : Multiplicative (Additive G) ≃* G where
  toFun z := z.toAdd.toMul
  invFun g := Multiplicative.ofAdd (Additive.ofMul g)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The homomorphism from the cyclic group of order two generated by a
specified involution. -/
noncomputable def z2HomOfInvolution {G : Type*} [Group G] (g : G)
    (hg : g * g = 1) : Multiplicative (ZMod 2) →* G := by
  have htwo : (2 : ℕ) • Additive.ofMul g = 0 := by
    change g ^ 2 = 1
    simpa [pow_two] using hg
  let f : ℤ →+ Additive G := zmultiplesHom (Additive G) (Additive.ofMul g)
  have hf : f (2 : ℤ) = 0 := by
    change g ^ (2 : ℤ) = 1
    simpa [zpow_ofNat, pow_two] using hg
  exact mulAddCancel.toMonoidHom.comp
    (AddMonoidHom.toMultiplicative (ZMod.lift 2 ⟨f, hf⟩))

@[simp]
lemma z2Hom_zero {G : Type*} [Group G] (g : G) (hg : g * g = 1) :
    z2HomOfInvolution g hg (Multiplicative.ofAdd 0) = 1 := by
  simp [z2HomOfInvolution, mulAddCancel]

@[simp]
lemma z2Hom_one {G : Type*} [Group G] (g : G) (hg : g * g = 1) :
    z2HomOfInvolution g hg (Multiplicative.ofAdd 1) = g := by
  unfold z2HomOfInvolution
  dsimp [mulAddCancel]
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num]
  rw [ZMod.lift_coe]
  simp

lemma z2Hom_eq_one_or {G : Type*} [Group G] (g : G) (hg : g * g = 1)
    (x : Multiplicative (ZMod 2)) :
    z2HomOfInvolution g hg x = 1 ∨ z2HomOfInvolution g hg x = g := by
  fin_cases x
  · left
    convert z2Hom_zero g hg
    apply congrArg Multiplicative.ofAdd
    apply Fin.ext
    rfl
  · right
    convert z2Hom_one g hg
    apply congrArg Multiplicative.ofAdd
    apply Fin.ext
    rfl

lemma multiplicative_zmod_two_eq (x : Multiplicative (ZMod 2)) :
    x = Multiplicative.ofAdd 0 ∨ x = Multiplicative.ofAdd 1 := by
  fin_cases x
  · left
    apply congrArg Multiplicative.ofAdd
    apply Fin.ext
    rfl
  · right
    apply congrArg Multiplicative.ofAdd
    apply Fin.ext
    rfl

/-- Two distinct commuting involutions generate a homomorphic copy of
`ZMod 2 × ZMod 2`. -/
noncomputable def kleinHomOfPair {G : Type*} [Group G] (g h : G)
    (hg : g * g = 1) (hh : h * h = 1) (hcomm : g * h = h * g) :
    Multiplicative (ZMod 2 × ZMod 2) →* G := by
  let fg := z2HomOfInvolution g hg
  let fh := z2HomOfInvolution h hh
  refine
    { toFun := fun x => fg (Multiplicative.ofAdd x.toAdd.1) *
        fh (Multiplicative.ofAdd x.toAdd.2)
      map_one' := by simp [fg, fh]
      map_mul' := ?_ }
  intro x y
  change fg (Multiplicative.ofAdd (x.toAdd.1 + y.toAdd.1)) *
      fh (Multiplicative.ofAdd (x.toAdd.2 + y.toAdd.2)) =
    (fg (Multiplicative.ofAdd x.toAdd.1) * fh (Multiplicative.ofAdd x.toAdd.2)) *
      (fg (Multiplicative.ofAdd y.toAdd.1) * fh (Multiplicative.ofAdd y.toAdd.2))
  rw [show Multiplicative.ofAdd (x.toAdd.1 + y.toAdd.1) =
        Multiplicative.ofAdd x.toAdd.1 * Multiplicative.ofAdd y.toAdd.1 by rfl,
      show Multiplicative.ofAdd (x.toAdd.2 + y.toAdd.2) =
        Multiplicative.ofAdd x.toAdd.2 * Multiplicative.ofAdd y.toAdd.2 by rfl,
      map_mul, map_mul]
  have hc : fh (Multiplicative.ofAdd x.toAdd.2) *
      fg (Multiplicative.ofAdd y.toAdd.1) =
      fg (Multiplicative.ofAdd y.toAdd.1) *
        fh (Multiplicative.ofAdd x.toAdd.2) := by
    rcases z2Hom_eq_one_or h hh (Multiplicative.ofAdd x.toAdd.2) with hx | hx <;>
      rcases z2Hom_eq_one_or g hg (Multiplicative.ofAdd y.toAdd.1) with hy | hy <;>
      rw [hx, hy] <;> simp [hcomm]
  calc
    fg (Multiplicative.ofAdd x.toAdd.1) * fg (Multiplicative.ofAdd y.toAdd.1) *
          (fh (Multiplicative.ofAdd x.toAdd.2) *
            fh (Multiplicative.ofAdd y.toAdd.2)) =
        fg (Multiplicative.ofAdd x.toAdd.1) *
          (fg (Multiplicative.ofAdd y.toAdd.1) *
            fh (Multiplicative.ofAdd x.toAdd.2)) *
          fh (Multiplicative.ofAdd y.toAdd.2) := by group
    _ = fg (Multiplicative.ofAdd x.toAdd.1) *
          (fh (Multiplicative.ofAdd x.toAdd.2) *
            fg (Multiplicative.ofAdd y.toAdd.1)) *
          fh (Multiplicative.ofAdd y.toAdd.2) := by rw [hc]
    _ = (fg (Multiplicative.ofAdd x.toAdd.1) *
          fh (Multiplicative.ofAdd x.toAdd.2)) *
        (fg (Multiplicative.ofAdd y.toAdd.1) *
          fh (Multiplicative.ofAdd y.toAdd.2)) := by group

lemma multiplicative_zmod_two_prod_eq (x : Multiplicative (ZMod 2 × ZMod 2)) :
    x = Multiplicative.ofAdd (0, 0) ∨
    x = Multiplicative.ofAdd (1, 0) ∨
    x = Multiplicative.ofAdd (0, 1) ∨
    x = Multiplicative.ofAdd (1, 1) := by
  rcases multiplicative_zmod_two_eq (Multiplicative.ofAdd x.toAdd.1) with h₁ | h₁ <;>
    rcases multiplicative_zmod_two_eq (Multiplicative.ofAdd x.toAdd.2) with h₂ | h₂
  · left
    apply Multiplicative.toAdd.injective
    exact Prod.ext (Multiplicative.ofAdd.injective h₁)
      (Multiplicative.ofAdd.injective h₂)
  · right; right; left
    apply Multiplicative.toAdd.injective
    exact Prod.ext (Multiplicative.ofAdd.injective h₁)
      (Multiplicative.ofAdd.injective h₂)
  · right; left
    apply Multiplicative.toAdd.injective
    exact Prod.ext (Multiplicative.ofAdd.injective h₁)
      (Multiplicative.ofAdd.injective h₂)
  · right; right; right
    apply Multiplicative.toAdd.injective
    exact Prod.ext (Multiplicative.ofAdd.injective h₁)
      (Multiplicative.ofAdd.injective h₂)

lemma kleinHomOfPair_injective {G : Type*} [Group G] (g h : G)
    (hg : g * g = 1) (hh : h * h = 1) (hcomm : g * h = h * g)
    (hg1 : g ≠ 1) (hh1 : h ≠ 1) (hgh : g ≠ h) :
    Function.Injective (kleinHomOfPair g h hg hh hcomm) := by
  have hprod : g * h ≠ 1 := by
    intro hp
    apply hgh
    calc
      g = g * 1 := by simp
      _ = g * (g * h) := by rw [hp]
      _ = (g * g) * h := by group
      _ = h := by rw [hg]; simp
  intro x y hxy
  rcases multiplicative_zmod_two_prod_eq x with rfl | rfl | rfl | rfl <;>
    rcases multiplicative_zmod_two_prod_eq y with rfl | rfl | rfl | rfl
  all_goals simp [kleinHomOfPair, z2Hom_one] at hxy
  all_goals try rfl
  all_goals exfalso
  all_goals
    first
    | exact hg1 hxy
    | exact hg1 hxy.symm
    | exact hh1 hxy
    | exact hh1 hxy.symm
    | exact hgh hxy
    | exact hgh hxy.symm
    | exact hprod hxy
    | exact hprod hxy.symm

/-- The range of an injective Klein-pair homomorphism is a genuine
`IsKleinFour` subgroup. -/
theorem containsKleinFour_of_pair {g : LeftInvariantMetric}
    (a b : innerIsotropy g) (ha : a * a = 1) (hb : b * b = 1)
    (hcomm : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    ContainsKleinFour g := by
  let f := kleinHomOfPair a b ha hb hcomm
  have hf : Function.Injective f :=
    kleinHomOfPair_injective a b ha hb hcomm ha1 hb1 hab
  let H : Subgroup (innerIsotropy g) := f.range
  have hfr : Function.Injective f.rangeRestrict := by
    intro x y hxy
    apply hf
    exact congrArg Subtype.val hxy
  let e : Multiplicative (ZMod 2 × ZMod 2) ≃* H :=
    MulEquiv.ofBijective f.rangeRestrict
      ⟨hfr, MonoidHom.rangeRestrict_surjective f⟩
  letI : IsKleinFour H := {
    card_four := by
      calc
        Nat.card H = Nat.card (Multiplicative (ZMod 2 × ZMod 2)) :=
          (Nat.card_congr e.toEquiv).symm
        _ = 4 := by simp
    exponent_two := by
      calc
        Monoid.exponent H =
            Monoid.exponent (Multiplicative (ZMod 2 × ZMod 2)) :=
          (Monoid.exponent_eq_of_mulEquiv e).symm
        _ = 2 := by simp
  }
  exact ⟨H, inferInstance⟩

def diagonalTurn1 : InnerAction := (halfTurn1, halfTurn1)
def diagonalTurn2 : InnerAction := (halfTurn2, halfTurn2)
def diagonalTurn3 : InnerAction := (halfTurn3, halfTurn3)

@[simp] lemma diagonalTurn1_sq : diagonalTurn1 * diagonalTurn1 = 1 := by
  apply Prod.ext <;> simp [diagonalTurn1]

@[simp] lemma diagonalTurn2_sq : diagonalTurn2 * diagonalTurn2 = 1 := by
  apply Prod.ext <;> simp [diagonalTurn2]

lemma diagonalTurn_comm : diagonalTurn1 * diagonalTurn2 =
    diagonalTurn2 * diagonalTurn1 := by
  apply Prod.ext <;>
    simp [diagonalTurn1, diagonalTurn2, halfTurn1_mul_halfTurn2,
      halfTurn2_mul_halfTurn1]

lemma halfTurn1_ne_one : halfTurn1 ≠ 1 := by
  intro h
  have he := congrArg (fun R : SO3 ↦ (R : Mat3) 1 1) h
  norm_num [halfTurn1] at he

lemma halfTurn2_ne_one : halfTurn2 ≠ 1 := by
  intro h
  have he := congrArg (fun R : SO3 ↦ (R : Mat3) 0 0) h
  norm_num [halfTurn2] at he

lemma halfTurn1_ne_halfTurn2 : halfTurn1 ≠ halfTurn2 := by
  intro h
  have he := congrArg (fun R : SO3 ↦ (R : Mat3) 0 0) h
  norm_num [halfTurn1, halfTurn2] at he

lemma diagonalTurn1_ne_one : diagonalTurn1 ≠ 1 := by
  intro h
  exact halfTurn1_ne_one (congrArg Prod.fst h)

lemma diagonalTurn2_ne_one : diagonalTurn2 ≠ 1 := by
  intro h
  exact halfTurn2_ne_one (congrArg Prod.fst h)

lemma diagonalTurn1_ne_diagonalTurn2 : diagonalTurn1 ≠ diagonalTurn2 := by
  intro h
  exact halfTurn1_ne_halfTurn2 (congrArg Prod.fst h)

theorem containsKleinFour_of_diagonal_turns {g : LeftInvariantMetric}
    (h₁ : Fixes diagonalTurn1 g) (h₂ : Fixes diagonalTurn2 g) :
    ContainsKleinFour g := by
  let a : innerIsotropy g := ⟨diagonalTurn1, h₁⟩
  let b : innerIsotropy g := ⟨diagonalTurn2, h₂⟩
  apply containsKleinFour_of_pair a b
  · apply Subtype.ext
    exact congrArg id diagonalTurn1_sq
  · apply Subtype.ext
    exact congrArg id diagonalTurn2_sq
  · apply Subtype.ext
    exact congrArg id diagonalTurn_comm
  · intro h
    exact diagonalTurn1_ne_one (congrArg Subtype.val h)
  · intro h
    exact diagonalTurn2_ne_one (congrArg Subtype.val h)
  · intro h
    exact diagonalTurn1_ne_diagonalTurn2 (congrArg Subtype.val h)

/-! A co-metric is in the `Z₂²` normal form exactly when all four of its
`3 × 3` blocks are diagonal. -/

def PairedMatrix (K : Mat6) : Prop :=
  ∃ A B C D : I3 → ℝ,
    K = Matrix.fromBlocks (Matrix.diagonal A) (Matrix.diagonal B)
      (Matrix.diagonal C) (Matrix.diagonal D)

lemma diagonal_conjugates_diagonal (s a : I3 → ℝ)
    (hs : ∀ i, s i * s i = 1) :
    (Matrix.diagonal s)ᵀ * Matrix.diagonal a * Matrix.diagonal s =
      Matrix.diagonal a := by
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  specialize hs i
  calc
    s i * a i * s i = a i * (s i * s i) := by ring
    _ = a i := by rw [hs]; ring

lemma paired_fixed_by_diagonal_action
    (r : SO3) (s : I3 → ℝ) (hr : (r : Mat3) = Matrix.diagonal s)
    (hs : ∀ i, s i * s i = 1) {K : Mat6} (hK : PairedMatrix K) :
    (innerMatrix (r, r))ᵀ * K * innerMatrix (r, r) = K := by
  rcases hK with ⟨A, B, C, D, rfl⟩
  have hA := diagonal_conjugates_diagonal s A hs
  have hB := diagonal_conjugates_diagonal s B hs
  have hC := diagonal_conjugates_diagonal s C hs
  have hD := diagonal_conjugates_diagonal s D hs
  simp only [innerMatrix, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.transpose_zero, zero_mul, mul_zero,
    add_zero, zero_add, hr]
  rw [hA, hB, hC, hD]

lemma paired_fixed_by_turn1 {K : Mat6} (hK : PairedMatrix K) :
    (innerMatrix diagonalTurn1)ᵀ * K * innerMatrix diagonalTurn1 = K := by
  apply paired_fixed_by_diagonal_action halfTurn1 ![1, -1, -1]
  · rfl
  · intro i
    fin_cases i <;> norm_num
  · exact hK

lemma paired_fixed_by_turn2 {K : Mat6} (hK : PairedMatrix K) :
    (innerMatrix diagonalTurn2)ᵀ * K * innerMatrix diagonalTurn2 = K := by
  apply paired_fixed_by_diagonal_action halfTurn2 ![-1, 1, -1]
  · rfl
  · intro i
    fin_cases i <;> norm_num
  · exact hK

/-- If `r` fixes the co-metric after the background change `t`, then the
conjugate `t r t⁻¹` fixes the original co-metric. -/
lemma conjugate_fixes_cometric (t r : InnerAction) (K : Mat6)
    (hr : (innerMatrix r)ᵀ * ((innerMatrix t)ᵀ * K * innerMatrix t) *
      innerMatrix r = (innerMatrix t)ᵀ * K * innerMatrix t) :
    (innerMatrix (t * r * t⁻¹))ᵀ * K * innerMatrix (t * r * t⁻¹) = K := by
  let T := innerMatrix t
  let R := innerMatrix r
  let U := innerMatrix t⁻¹
  have hTU : T * U = 1 := by
    rw [← innerMatrix_mul]
    simp
  have hUt : Uᵀ * Tᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose hTU
  rw [innerMatrix_mul, innerMatrix_mul, Matrix.transpose_mul,
    Matrix.transpose_mul]
  change Uᵀ * (Rᵀ * Tᵀ) * K * (T * R * U) = K
  change Rᵀ * (Tᵀ * K * T) * R = Tᵀ * K * T at hr
  calc
    Uᵀ * (Rᵀ * Tᵀ) * K * (T * R * U) =
        Uᵀ * (Rᵀ * (Tᵀ * K * T) * R) * U := by noncomm_ring
    _ = Uᵀ * (Tᵀ * K * T) * U := by rw [hr]
    _ = K := by
      calc
        Uᵀ * (Tᵀ * K * T) * U = (Uᵀ * Tᵀ) * K * (T * U) := by
          noncomm_ring
        _ = K := by rw [hUt, hTU]; simp

/-- A paired co-metric in some inner coordinate system yields a conjugate
Klein four subgroup of the original metric's inner isotropy. -/
theorem containsKleinFour_of_conjugate_paired
    (C : Mat6) (hC : C.det ≠ 0) (t : InnerAction)
    (hpaired : PairedMatrix ((innerMatrix t)ᵀ * (Cᵀ * C) * innerMatrix t)) :
    ContainsKleinFour (metricOfFrame C hC) := by
  let K : Mat6 := Cᵀ * C
  let a : InnerAction := t * diagonalTurn1 * t⁻¹
  let b : InnerAction := t * diagonalTurn2 * t⁻¹
  have hrot₁ := paired_fixed_by_turn1 hpaired
  have hrot₂ := paired_fixed_by_turn2 hpaired
  have haK : (innerMatrix a)ᵀ * K * innerMatrix a = K := by
    exact conjugate_fixes_cometric t diagonalTurn1 K hrot₁
  have hbK : (innerMatrix b)ᵀ * K * innerMatrix b = K := by
    exact conjugate_fixes_cometric t diagonalTurn2 K hrot₂
  have hfixa : Fixes a (metricOfFrame C hC) :=
    fixes_metricOfFrame_of_fixes_cometric a C hC haK
  have hfixb : Fixes b (metricOfFrame C hC) :=
    fixes_metricOfFrame_of_fixes_cometric b C hC hbK
  let aa : innerIsotropy (metricOfFrame C hC) := ⟨a, hfixa⟩
  let bb : innerIsotropy (metricOfFrame C hC) := ⟨b, hfixb⟩
  apply containsKleinFour_of_pair aa bb
  · apply Subtype.ext
    change a * a = 1
    dsimp [a]
    calc
      (t * diagonalTurn1 * t⁻¹) * (t * diagonalTurn1 * t⁻¹) =
          t * (diagonalTurn1 * diagonalTurn1) * t⁻¹ := by group
      _ = 1 := by rw [diagonalTurn1_sq]; simp
  · apply Subtype.ext
    change b * b = 1
    dsimp [b]
    calc
      (t * diagonalTurn2 * t⁻¹) * (t * diagonalTurn2 * t⁻¹) =
          t * (diagonalTurn2 * diagonalTurn2) * t⁻¹ := by group
      _ = 1 := by rw [diagonalTurn2_sq]; simp
  · apply Subtype.ext
    change a * b = b * a
    dsimp [a, b]
    calc
      (t * diagonalTurn1 * t⁻¹) * (t * diagonalTurn2 * t⁻¹) =
          t * (diagonalTurn1 * diagonalTurn2) * t⁻¹ := by group
      _ = t * (diagonalTurn2 * diagonalTurn1) * t⁻¹ := by
        rw [diagonalTurn_comm]
      _ = (t * diagonalTurn2 * t⁻¹) * (t * diagonalTurn1 * t⁻¹) := by group
  · intro h
    apply diagonalTurn1_ne_one
    have hv := congrArg (fun q : innerIsotropy (metricOfFrame C hC) ↦
      t⁻¹ * q.1 * t) h
    simpa [aa, a, mul_assoc] using hv
  · intro h
    apply diagonalTurn2_ne_one
    have hv := congrArg (fun q : innerIsotropy (metricOfFrame C hC) ↦
      t⁻¹ * q.1 * t) h
    simpa [bb, b, mul_assoc] using hv
  · intro h
    apply diagonalTurn1_ne_diagonalTurn2
    have hv := congrArg (fun q : innerIsotropy (metricOfFrame C hC) ↦
      t⁻¹ * q.1 * t) h
    simpa [aa, bb, a, b, mul_assoc] using hv

/-! ## The trace `-2` normal frame and its plane blocks -/

def liftPlane (a : ℝ) (N : Mat2) : Mat3 :=
  !![a, 0, 0;
     0, N 0 0, N 0 1;
     0, N 1 0, N 1 1]

lemma liftPlane_transpose (a : ℝ) (N : Mat2) :
    (liftPlane a N)ᵀ = liftPlane a Nᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftPlane]

lemma liftPlane_mul (a b : ℝ) (N P : Mat2) :
    liftPlane a N * liftPlane b P = liftPlane (a * b) (N * P) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftPlane, Matrix.mul_apply, Fin.sum_univ_succ]

lemma liftPlane_add (a b : ℝ) (N P : Mat2) :
    liftPlane a N + liftPlane b P = liftPlane (a + b) (N + P) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftPlane]

lemma liftPlane_zero : liftPlane 0 (0 : Mat2) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftPlane]

lemma liftPlane_one : liftPlane 1 (1 : Mat2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftPlane]

lemma extendSO2Matrix_eq_liftPlane (Q : SO2) :
    extendSO2Matrix Q = liftPlane 1 (Q : Mat2) := rfl

lemma extendSO2_inv_coe (Q : SO2) :
    (((extendSO2 Q)⁻¹ : SO3) : Mat3) = liftPlane 1 (Q : Mat2)ᵀ := by
  change (extendSO2Matrix Q)ᵀ = liftPlane 1 (Q : Mat2)ᵀ
  rw [extendSO2Matrix_eq_liftPlane, liftPlane_transpose]

lemma liftPlane_det (a : ℝ) (N : Mat2) :
    (liftPlane a N).det = a * N.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [liftPlane]
  ring

def diag2 (a b : ℝ) : Mat2 := !![a, 0; 0, b]

lemma diag2_det (a b : ℝ) : (diag2 a b).det = a * b := by
  rw [Matrix.det_fin_two]
  simp [diag2]

lemma diag2_isDiagonal (a b : ℝ) : IsDiagonal2 (diag2 a b) := by
  simp [IsDiagonal2, diag2]

lemma isDiagonal2_transpose {N : Mat2} (h : IsDiagonal2 N) :
    IsDiagonal2 Nᵀ := ⟨h.2, h.1⟩

lemma isDiagonal2_add {N P : Mat2} (hN : IsDiagonal2 N)
    (hP : IsDiagonal2 P) : IsDiagonal2 (N + P) := by
  constructor <;> simp [hN.1, hN.2, hP.1, hP.2]

lemma isDiagonal2_mul {N P : Mat2} (hN : IsDiagonal2 N)
    (hP : IsDiagonal2 P) : IsDiagonal2 (N * P) := by
  constructor <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hN.1, hN.2, hP.1, hP.2]

lemma eq_diag2_of_isDiagonal2 {N : Mat2} (hN : IsDiagonal2 N) :
    N = diag2 (N 0 0) (N 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2, hN.1, hN.2]

lemma so2_mul_transpose (Q : SO2) : (Q : Mat2) * (Q : Mat2)ᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff I2 ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).1

lemma so2_transpose_mul (Q : SO2) : (Q : Mat2)ᵀ * (Q : Mat2) = 1 :=
  (Matrix.mem_orthogonalGroup_iff' I2 ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).1

lemma scalar_diag2_commutes (s : ℝ) (Q : Mat2) :
    diag2 s s * Q = Q * diag2 s s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag2, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

lemma scalar_diag2_right_gram (s : ℝ) (Q : SO2) :
    IsDiagonal2 ((diag2 s s * (Q : Mat2)ᵀ)ᵀ *
      (diag2 s s * (Q : Mat2)ᵀ)) := by
  have horth := so2_mul_transpose Q
  have hcomm := scalar_diag2_commutes s (Q : Mat2)
  have hsq : diag2 s s * diag2 s s = diag2 (s ^ 2) (s ^ 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diag2, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  have heq : ((diag2 s s * (Q : Mat2)ᵀ)ᵀ *
      (diag2 s s * (Q : Mat2)ᵀ)) = diag2 (s ^ 2) (s ^ 2) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    have hDt : (diag2 s s)ᵀ = diag2 s s := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diag2]
    rw [hDt]
    calc
      (Q : Mat2) * diag2 s s * (diag2 s s * (Q : Mat2)ᵀ) =
          (diag2 s s * (Q : Mat2)) *
            (diag2 s s * (Q : Mat2)ᵀ) := by
              exact congrArg (fun X : Mat2 ↦ X *
                (diag2 s s * (Q : Mat2)ᵀ)) hcomm.symm
      _ = diag2 s s * (((Q : Mat2) * diag2 s s) *
            (Q : Mat2)ᵀ) := by noncomm_ring
      _ = diag2 s s * ((diag2 s s * (Q : Mat2)) *
            (Q : Mat2)ᵀ) := by
              exact congrArg (fun X : Mat2 ↦ diag2 s s *
                (X * (Q : Mat2)ᵀ)) hcomm.symm
      _ = (diag2 s s * diag2 s s) * ((Q : Mat2) * (Q : Mat2)ᵀ) := by
            noncomm_ring
      _ = diag2 (s ^ 2) (s ^ 2) := by rw [hsq, horth]; simp
  rw [heq]
  exact diag2_isDiagonal _ _

lemma quarter_diagonal_right_gram (s u : ℝ) :
    IsDiagonal2 ((diag2 s u * (quarterTurn : Mat2)ᵀ)ᵀ *
      (diag2 s u * (quarterTurn : Mat2)ᵀ)) := by
  have heq : diag2 s u * (quarterTurn : Mat2)ᵀ = !![0, s; -u, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [diag2, quarterTurn, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [heq]
  constructor <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

lemma isDiagonal2_gram_of_left_diagonalized (P : SO2) {N : Mat2}
    (hPN : IsDiagonal2 ((P : Mat2) * N)) : IsDiagonal2 (Nᵀ * N) := by
  have heq : (((P : Mat2) * N)ᵀ * ((P : Mat2) * N)) = Nᵀ * N := by
    rw [Matrix.transpose_mul]
    calc
      Nᵀ * (P : Mat2)ᵀ * ((P : Mat2) * N) =
          Nᵀ * ((P : Mat2)ᵀ * (P : Mat2)) * N := by noncomm_ring
      _ = Nᵀ * N := by rw [so2_transpose_mul]; simp
  rw [← heq]
  exact isDiagonal2_mul (isDiagonal2_transpose hPN) hPN

lemma isDiagonal2_cross_of_left_diagonalized (P : SO2) {N : Mat2}
    (s : ℝ) (hPN : IsDiagonal2 ((P : Mat2) * N)) :
    IsDiagonal2 (Nᵀ * (diag2 s s * (P : Mat2)ᵀ)) := by
  have hcomm := scalar_diag2_commutes s (P : Mat2)ᵀ
  have heq : Nᵀ * (diag2 s s * (P : Mat2)ᵀ) =
      ((P : Mat2) * N)ᵀ * diag2 s s := by
    rw [Matrix.transpose_mul]
    rw [hcomm]
    noncomm_ring
  rw [heq]
  exact isDiagonal2_mul (isDiagonal2_transpose hPN) (diag2_isDiagonal _ _)

def IsDiagonal3 (N : Mat3) : Prop := ∀ i j, i ≠ j → N i j = 0

lemma liftPlane_isDiagonal3 {a : ℝ} {N : Mat2} (hN : IsDiagonal2 N) :
    IsDiagonal3 (liftPlane a N) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [liftPlane, IsDiagonal2]

lemma eq_diagonal_of_isDiagonal3 {N : Mat3} (hN : IsDiagonal3 N) :
    N = Matrix.diagonal (fun i ↦ N i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [hN i j hij, Matrix.diagonal_apply_ne _ hij]

lemma pairedMatrix_fromBlocks {A B C D : Mat3}
    (hA : IsDiagonal3 A) (hB : IsDiagonal3 B)
    (hC : IsDiagonal3 C) (hD : IsDiagonal3 D) :
    PairedMatrix (Matrix.fromBlocks A B C D) := by
  refine ⟨(fun i ↦ A i i), (fun i ↦ B i i), (fun i ↦ C i i),
    (fun i ↦ D i i), ?_⟩
  congr 1
  · exact eq_diagonal_of_isDiagonal3 hA
  · exact eq_diagonal_of_isDiagonal3 hB
  · exact eq_diagonal_of_isDiagonal3 hC
  · exact eq_diagonal_of_isDiagonal3 hD

lemma triangular_frame_cometric (E M F : Mat3) :
    (Matrix.fromBlocks E 0 M F : Mat6)ᵀ *
        Matrix.fromBlocks E 0 M F =
      Matrix.fromBlocks (Eᵀ * E + Mᵀ * M) (Mᵀ * F)
        (Fᵀ * M) (Fᵀ * F) := by
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

lemma rotated_triangular_frame_cometric (E M F U V : Mat3) :
    (Matrix.fromBlocks U 0 0 V : Mat6)ᵀ *
        ((Matrix.fromBlocks E 0 M F : Mat6)ᵀ *
          Matrix.fromBlocks E 0 M F) *
        Matrix.fromBlocks U 0 0 V =
      Matrix.fromBlocks
        ((E * U)ᵀ * (E * U) + (M * U)ᵀ * (M * U))
        ((M * U)ᵀ * (F * V))
        ((F * V)ᵀ * (M * U))
        ((F * V)ᵀ * (F * V)) := by
  have hmul : (Matrix.fromBlocks E 0 M F : Mat6) *
      Matrix.fromBlocks U 0 0 V = Matrix.fromBlocks (E * U) 0 (M * U) (F * V) := by
    rw [Matrix.fromBlocks_multiply]
    simp
  calc
    (Matrix.fromBlocks U 0 0 V : Mat6)ᵀ *
          ((Matrix.fromBlocks E 0 M F : Mat6)ᵀ *
            Matrix.fromBlocks E 0 M F) *
          Matrix.fromBlocks U 0 0 V =
        ((Matrix.fromBlocks E 0 M F : Mat6) *
          Matrix.fromBlocks U 0 0 V)ᵀ *
        ((Matrix.fromBlocks E 0 M F : Mat6) *
          Matrix.fromBlocks U 0 0 V) := by
            rw [Matrix.transpose_mul]
            noncomm_ring
    _ = (Matrix.fromBlocks (E * U) 0 (M * U) (F * V) : Mat6)ᵀ *
        Matrix.fromBlocks (E * U) 0 (M * U) (F * V) := by rw [hmul]
    _ = _ := triangular_frame_cometric _ _ _

lemma paired_rotated_liftPlane
    (e₀ m₀ f₀ u₀ v₀ : ℝ) (DE N DF U V : Mat2)
    (hA : IsDiagonal2
      ((DE * U)ᵀ * (DE * U) + (N * U)ᵀ * (N * U)))
    (hB : IsDiagonal2 ((N * U)ᵀ * (DF * V)))
    (hC : IsDiagonal2 ((DF * V)ᵀ * (N * U)))
    (hD : IsDiagonal2 ((DF * V)ᵀ * (DF * V))) :
    PairedMatrix
      ((Matrix.fromBlocks (liftPlane u₀ U) 0 0 (liftPlane v₀ V) : Mat6)ᵀ *
        ((Matrix.fromBlocks (liftPlane e₀ DE) 0 (liftPlane m₀ N)
          (liftPlane f₀ DF) : Mat6)ᵀ *
          Matrix.fromBlocks (liftPlane e₀ DE) 0 (liftPlane m₀ N)
            (liftPlane f₀ DF)) *
        Matrix.fromBlocks (liftPlane u₀ U) 0 0 (liftPlane v₀ V)) := by
  rw [rotated_triangular_frame_cometric]
  apply pairedMatrix_fromBlocks
  · rw [liftPlane_mul, liftPlane_transpose, liftPlane_mul,
      liftPlane_mul, liftPlane_transpose, liftPlane_mul, liftPlane_add]
    exact liftPlane_isDiagonal3 hA
  · rw [liftPlane_mul, liftPlane_mul, liftPlane_transpose, liftPlane_mul]
    exact liftPlane_isDiagonal3 hB
  · rw [liftPlane_mul, liftPlane_transpose, liftPlane_mul, liftPlane_mul]
    exact liftPlane_isDiagonal3 hC
  · rw [liftPlane_mul, liftPlane_transpose, liftPlane_mul]
    exact liftPlane_isDiagonal3 hD

lemma paired_liftPlane_of_diagonal
    (e₀ m₀ f₀ : ℝ) (DE N DF : Mat2)
    (hDE : IsDiagonal2 DE) (hN : IsDiagonal2 N) (hDF : IsDiagonal2 DF) :
    PairedMatrix
      ((Matrix.fromBlocks (liftPlane e₀ DE) 0 (liftPlane m₀ N)
        (liftPlane f₀ DF) : Mat6)ᵀ *
        Matrix.fromBlocks (liftPlane e₀ DE) 0 (liftPlane m₀ N)
          (liftPlane f₀ DF)) := by
  rw [triangular_frame_cometric]
  apply pairedMatrix_fromBlocks
  · rw [liftPlane_transpose, liftPlane_mul, liftPlane_transpose,
      liftPlane_mul, liftPlane_add]
    exact liftPlane_isDiagonal3
      (isDiagonal2_add
        (isDiagonal2_mul (isDiagonal2_transpose hDE) hDE)
        (isDiagonal2_mul (isDiagonal2_transpose hN) hN))
  · rw [liftPlane_transpose, liftPlane_mul]
    exact liftPlane_isDiagonal3
      (isDiagonal2_mul (isDiagonal2_transpose hN) hDF)
  · rw [liftPlane_transpose, liftPlane_mul]
    exact liftPlane_isDiagonal3
      (isDiagonal2_mul (isDiagonal2_transpose hDF) hN)
  · rw [liftPlane_transpose, liftPlane_mul]
    exact liftPlane_isDiagonal3
      (isDiagonal2_mul (isDiagonal2_transpose hDF) hDF)

lemma paired_liftPlane_after_row_rotation
    (e₀ m₀ f₀ : ℝ) (DE N DF : Mat2) (Q : SO2)
    (hEgram : IsDiagonal2 ((DE * (Q : Mat2)ᵀ)ᵀ *
      (DE * (Q : Mat2)ᵀ)))
    (hNQ : IsDiagonal2 (N * (Q : Mat2)ᵀ))
    (hDF : IsDiagonal2 DF) :
    PairedMatrix
      ((Matrix.fromBlocks (liftPlane 1 (Q : Mat2)ᵀ) 0 0
          (liftPlane 1 1) : Mat6)ᵀ *
        ((Matrix.fromBlocks (liftPlane e₀ DE) 0 (liftPlane m₀ N)
          (liftPlane f₀ DF) : Mat6)ᵀ *
          Matrix.fromBlocks (liftPlane e₀ DE) 0 (liftPlane m₀ N)
            (liftPlane f₀ DF)) *
        Matrix.fromBlocks (liftPlane 1 (Q : Mat2)ᵀ) 0 0
          (liftPlane 1 1)) := by
  apply paired_rotated_liftPlane e₀ m₀ f₀ 1 1 DE N DF (Q : Mat2)ᵀ 1
  · simpa using isDiagonal2_add hEgram
      (isDiagonal2_mul (isDiagonal2_transpose hNQ) hNQ)
  · simpa using isDiagonal2_mul (isDiagonal2_transpose hNQ) hDF
  · simpa using isDiagonal2_mul (isDiagonal2_transpose hDF) hNQ
  · simpa using isDiagonal2_mul (isDiagonal2_transpose hDF) hDF

lemma paired_liftPlane_after_column_rotation
    (e₀ m₀ f₀ : ℝ) (DE N : Mat2) (s : ℝ) (P : SO2)
    (hDE : IsDiagonal2 DE) (hPN : IsDiagonal2 ((P : Mat2) * N)) :
    PairedMatrix
      ((Matrix.fromBlocks (liftPlane 1 1) 0 0
          (liftPlane 1 (P : Mat2)ᵀ) : Mat6)ᵀ *
        ((Matrix.fromBlocks (liftPlane e₀ DE) 0 (liftPlane m₀ N)
          (liftPlane f₀ (diag2 s s)) : Mat6)ᵀ *
          Matrix.fromBlocks (liftPlane e₀ DE) 0 (liftPlane m₀ N)
            (liftPlane f₀ (diag2 s s))) *
        Matrix.fromBlocks (liftPlane 1 1) 0 0
          (liftPlane 1 (P : Mat2)ᵀ)) := by
  apply paired_rotated_liftPlane e₀ m₀ f₀ 1 1 DE N (diag2 s s) 1 (P : Mat2)ᵀ
  · simpa using isDiagonal2_add
      (isDiagonal2_mul (isDiagonal2_transpose hDE) hDE)
      (isDiagonal2_gram_of_left_diagonalized P hPN)
  · simpa using isDiagonal2_cross_of_left_diagonalized P s hPN
  · have hcross := isDiagonal2_cross_of_left_diagonalized P s hPN
    have ht := isDiagonal2_transpose hcross
    simpa [Matrix.transpose_mul, Matrix.transpose_transpose] using ht
  · simpa using scalar_diag2_right_gram s P

namespace Parameters

noncomputable def planeE (p : Parameters) : Mat2 :=
  diag2 (Real.sqrt (p.a * p.c)) (Real.sqrt (p.a * p.b))

noncomputable def planeF (p : Parameters) : Mat2 :=
  diag2 (Real.sqrt (p.d * p.f)) (Real.sqrt (p.d * p.e))

noncomputable def planeN (p : Parameters) : Mat2 :=
  !![p.y * Real.sqrt (p.a * p.c), p.w * Real.sqrt (p.a * p.b);
     p.t * Real.sqrt (p.a * p.c), p.z * Real.sqrt (p.a * p.b)]

noncomputable def eDiag (p : Parameters) : Mat3 :=
  liftPlane (Real.sqrt (p.b * p.c))
    p.planeE

noncomputable def fDiag (p : Parameters) : Mat3 :=
  liftPlane (Real.sqrt (p.e * p.f))
    p.planeF

noncomputable def mixing (p : Parameters) : Mat3 :=
  liftPlane (p.x * Real.sqrt (p.b * p.c))
    p.planeN

noncomputable def frame (p : Parameters) : Mat6 :=
  Matrix.fromBlocks p.eDiag 0 p.mixing p.fDiag

end Parameters

lemma frame_det_ne_zero_of_positive {p : Parameters} (h : PositiveParameters p) :
    p.frame.det ≠ 0 := by
  rw [Parameters.frame, Matrix.det_fromBlocks_zero₁₂]
  have hab : 0 < p.a * p.b := mul_pos h.a_pos h.b_pos
  have hac : 0 < p.a * p.c := mul_pos h.a_pos h.c_pos
  have hbc : 0 < p.b * p.c := mul_pos h.b_pos h.c_pos
  have hde : 0 < p.d * p.e := mul_pos h.d_pos h.e_pos
  have hdf : 0 < p.d * p.f := mul_pos h.d_pos h.f_pos
  have hef : 0 < p.e * p.f := mul_pos h.e_pos h.f_pos
  have hsab : Real.sqrt (p.a * p.b) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hab)
  have hsac : Real.sqrt (p.a * p.c) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hac)
  have hsbc : Real.sqrt (p.b * p.c) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hbc)
  have hsde : Real.sqrt (p.d * p.e) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hde)
  have hsdf : Real.sqrt (p.d * p.f) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdf)
  have hsef : Real.sqrt (p.e * p.f) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hef)
  rw [Parameters.eDiag, Parameters.fDiag, liftPlane_det, liftPlane_det,
    Parameters.planeE, Parameters.planeF, diag2_det, diag2_det]
  exact mul_ne_zero (mul_ne_zero hsbc (mul_ne_zero hsac hsab))
    (mul_ne_zero hsef (mul_ne_zero hsdf hsde))

lemma frame_det_ne_zero {p : Parameters} (h : CriticalPoint p) :
    p.frame.det ≠ 0 := frame_det_ne_zero_of_positive h.toPositiveParameters

noncomputable def metricOfPositiveParameters (p : Parameters)
    (h : PositiveParameters p) : LeftInvariantMetric :=
  metricOfFrame p.frame (frame_det_ne_zero_of_positive h)

noncomputable def metricOfParameters (p : Parameters) (h : CriticalPoint p) :
    LeftInvariantMetric := metricOfPositiveParameters p h.toPositiveParameters

def DegenerateResolution (p : Parameters) : Prop :=
  (p.y = 0 ∧ p.z = 0) ∨
  (p.w = 0 ∧ p.t = 0) ∨
  (p.y * p.z ≠ 0 ∧ p.w * p.t ≠ 0 ∧ p.b = p.c ∧
    p.y * p.t + p.w * p.z = 0) ∨
  (p.y * p.z ≠ 0 ∧ p.w * p.t ≠ 0 ∧ p.e = p.f ∧
    p.y * p.w + p.t * p.z = 0)

theorem criticalPoint_resolution {p : Parameters} (h : CriticalPoint p) :
    DegenerateResolution p := by
  by_cases hyz : p.y * p.z = 0
  · left
    rcases mul_eq_zero.mp hyz with hy | hz
    · exact ⟨hy, (pair_zero_YZ h).mp hy⟩
    · exact ⟨(pair_zero_YZ h).mpr hz, hz⟩
  by_cases hwt : p.w * p.t = 0
  · right; left
    rcases mul_eq_zero.mp hwt with hw | ht
    · exact ⟨hw, (pair_zero_WT h).mp hw⟩
    · exact ⟨(pair_zero_WT h).mpr ht, ht⟩
  by_cases hbc : p.b = p.c
  · right; right; left
    exact ⟨hyz, hwt, hbc, row_orthogonality_of_b_eq_c h hbc⟩
  · right; right; right
    have hef : p.e = p.f := by
      by_contra hef
      exact no_fully_mixed h ⟨hyz, hwt, hbc, hef⟩
    exact ⟨hyz, hwt, hef, column_orthogonality_of_e_eq_f h hef⟩

/-- The complete coefficient-level symmetry-enhancement theorem, including
all four degenerate branches and the conjugation back to the original
background coordinates. -/
theorem criticalPoint_containsKleinFour {p : Parameters} (h : CriticalPoint p) :
    ContainsKleinFour (metricOfParameters p h) := by
  rcases criticalPoint_resolution h with hyz | hwt | hrow | hcol
  · rcases hyz with ⟨hy, hz⟩
    have hN : p.planeN =
        !![0, p.w * Real.sqrt (p.a * p.b);
           p.t * Real.sqrt (p.a * p.c), 0] := by
      simp [Parameters.planeN, hy, hz]
    have hNQ : IsDiagonal2 (p.planeN * (quarterTurn : Mat2)ᵀ) := by
      rw [hN]
      exact quarterTurn_right_diagonalizes_antidiagonal _ _
    have hEgram : IsDiagonal2
        ((p.planeE * (quarterTurn : Mat2)ᵀ)ᵀ *
          (p.planeE * (quarterTurn : Mat2)ᵀ)) := by
      rw [Parameters.planeE]
      exact quarter_diagonal_right_gram _ _
    have hDF : IsDiagonal2 p.planeF := by
      rw [Parameters.planeF]
      exact diag2_isDiagonal _ _
    let q : InnerAction := ((extendSO2 quarterTurn)⁻¹, 1)
    apply containsKleinFour_of_conjugate_paired p.frame (frame_det_ne_zero h) q
    have hp := paired_liftPlane_after_row_rotation
      (Real.sqrt (p.b * p.c)) (p.x * Real.sqrt (p.b * p.c))
      (Real.sqrt (p.e * p.f)) p.planeE p.planeN p.planeF quarterTurn
      hEgram hNQ hDF
    simpa [metricOfParameters, q, innerMatrix, Parameters.frame,
      Parameters.eDiag, Parameters.mixing, Parameters.fDiag,
      extendSO2_inv_coe, liftPlane_one] using hp
  · rcases hwt with ⟨hw, ht⟩
    have hDE : IsDiagonal2 p.planeE := by
      rw [Parameters.planeE]
      exact diag2_isDiagonal _ _
    have hN : IsDiagonal2 p.planeN := by
      simp [Parameters.planeN, IsDiagonal2, hw, ht]
    have hDF : IsDiagonal2 p.planeF := by
      rw [Parameters.planeF]
      exact diag2_isDiagonal _ _
    apply containsKleinFour_of_conjugate_paired p.frame (frame_det_ne_zero h) 1
    have hp := paired_liftPlane_of_diagonal
      (Real.sqrt (p.b * p.c)) (p.x * Real.sqrt (p.b * p.c))
      (Real.sqrt (p.e * p.f)) p.planeE p.planeN p.planeF hDE hN hDF
    simpa [metricOfParameters, innerMatrix, Parameters.frame,
      Parameters.eDiag, Parameters.mixing, Parameters.fDiag] using hp
  · rcases hrow with ⟨hyz, hwt, hbc, horth⟩
    have hy : p.y ≠ 0 := fun hy ↦ hyz (by simp [hy])
    have hs : 0 < Real.sqrt (p.a * p.c) :=
      Real.sqrt_pos.2 (mul_pos h.a_pos h.c_pos)
    have hsEq : Real.sqrt (p.a * p.b) = Real.sqrt (p.a * p.c) := by
      rw [hbc]
    have hnorm : 0 <
        (p.y * Real.sqrt (p.a * p.c)) ^ 2 +
          (p.w * Real.sqrt (p.a * p.b)) ^ 2 := by
      have : 0 < (p.y * Real.sqrt (p.a * p.c)) ^ 2 :=
        sq_pos_of_ne_zero (mul_ne_zero hy (ne_of_gt hs))
      positivity
    have horthN :
        (p.y * Real.sqrt (p.a * p.c)) *
            (p.t * Real.sqrt (p.a * p.c)) +
          (p.w * Real.sqrt (p.a * p.b)) *
            (p.z * Real.sqrt (p.a * p.b)) = 0 := by
      rw [hsEq]
      nlinarith [sq_nonneg (Real.sqrt (p.a * p.c))]
    obtain ⟨Q, hNQraw⟩ := diagonalize_orthogonal_rows hnorm horthN
    have hNQ : IsDiagonal2 (p.planeN * (Q : Mat2)ᵀ) := by
      simpa [Parameters.planeN] using hNQraw
    have hPE : p.planeE = diag2 (Real.sqrt (p.a * p.c))
        (Real.sqrt (p.a * p.c)) := by
      simp [Parameters.planeE, hbc]
    have hEgram : IsDiagonal2 ((p.planeE * (Q : Mat2)ᵀ)ᵀ *
        (p.planeE * (Q : Mat2)ᵀ)) := by
      rw [hPE]
      exact scalar_diag2_right_gram _ Q
    have hDF : IsDiagonal2 p.planeF := by
      rw [Parameters.planeF]
      exact diag2_isDiagonal _ _
    let q : InnerAction := ((extendSO2 Q)⁻¹, 1)
    apply containsKleinFour_of_conjugate_paired p.frame (frame_det_ne_zero h) q
    have hp := paired_liftPlane_after_row_rotation
      (Real.sqrt (p.b * p.c)) (p.x * Real.sqrt (p.b * p.c))
      (Real.sqrt (p.e * p.f)) p.planeE p.planeN p.planeF Q
      hEgram hNQ hDF
    simpa [metricOfParameters, q, innerMatrix, Parameters.frame,
      Parameters.eDiag, Parameters.mixing, Parameters.fDiag,
      extendSO2_inv_coe, liftPlane_one] using hp
  · rcases hcol with ⟨hyz, hwt, hef, horth⟩
    have hy : p.y ≠ 0 := fun hy ↦ hyz (by simp [hy])
    have hsa : 0 < Real.sqrt (p.a * p.c) :=
      Real.sqrt_pos.2 (mul_pos h.a_pos h.c_pos)
    have hnorm : 0 <
        (p.y * Real.sqrt (p.a * p.c)) ^ 2 +
          (p.t * Real.sqrt (p.a * p.c)) ^ 2 := by
      have : 0 < (p.y * Real.sqrt (p.a * p.c)) ^ 2 :=
        sq_pos_of_ne_zero (mul_ne_zero hy (ne_of_gt hsa))
      positivity
    have horthN :
        (p.y * Real.sqrt (p.a * p.c)) *
            (p.w * Real.sqrt (p.a * p.b)) +
          (p.t * Real.sqrt (p.a * p.c)) *
            (p.z * Real.sqrt (p.a * p.b)) = 0 := by
      calc
        (p.y * Real.sqrt (p.a * p.c)) *
              (p.w * Real.sqrt (p.a * p.b)) +
            (p.t * Real.sqrt (p.a * p.c)) *
              (p.z * Real.sqrt (p.a * p.b)) =
            Real.sqrt (p.a * p.c) * Real.sqrt (p.a * p.b) *
              (p.y * p.w + p.t * p.z) := by ring
        _ = 0 := by rw [horth]; ring
    obtain ⟨P, hPNraw⟩ := diagonalize_orthogonal_columns hnorm horthN
    have hPN : IsDiagonal2 ((P : Mat2) * p.planeN) := by
      simpa [Parameters.planeN] using hPNraw
    have hDE : IsDiagonal2 p.planeE := by
      rw [Parameters.planeE]
      exact diag2_isDiagonal _ _
    have hPF : p.planeF = diag2 (Real.sqrt (p.d * p.e))
        (Real.sqrt (p.d * p.e)) := by
      simp [Parameters.planeF, hef]
    let q : InnerAction := (1, (extendSO2 P)⁻¹)
    apply containsKleinFour_of_conjugate_paired p.frame (frame_det_ne_zero h) q
    have hp := paired_liftPlane_after_column_rotation
      (Real.sqrt (p.b * p.c)) (p.x * Real.sqrt (p.b * p.c))
      (Real.sqrt (p.e * p.f)) p.planeE p.planeN
      (Real.sqrt (p.d * p.e)) P hDE hPN
    rw [← hPF] at hp
    simpa [metricOfParameters, q, innerMatrix, Parameters.frame,
      Parameters.eDiag, Parameters.mixing, Parameters.fDiag,
      extendSO2_inv_coe, liftPlane_one] using hp

end S3xS3.Z2

open scoped Matrix

namespace S3xS3.Z2

def orientationCorrection (V : Mat3) : Mat3 :=
  Matrix.diagonal ![V.det, (1 : ℝ), (1 : ℝ)]

def orientedMatrix (V : Mat3) : Mat3 := V * orientationCorrection V

lemma det_sq_of_transpose_mul_eq_one {V : Mat3} (hV : Vᵀ * V = 1) :
    V.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hV
  rw [Matrix.det_mul, Matrix.det_transpose] at h
  simpa [pow_two] using h

lemma orientationCorrection_transpose (V : Mat3) :
    (orientationCorrection V)ᵀ = orientationCorrection V := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [orientationCorrection]

lemma orientationCorrection_sq {V : Mat3} (hV : Vᵀ * V = 1) :
    orientationCorrection V * orientationCorrection V = 1 := by
  have hd := det_sq_of_transpose_mul_eq_one hV
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orientationCorrection, Matrix.mul_apply, Fin.sum_univ_succ] ;
    nlinarith

lemma orientedMatrix_transpose_mul {V : Mat3} (hV : Vᵀ * V = 1) :
    (orientedMatrix V)ᵀ * orientedMatrix V = 1 := by
  rw [orientedMatrix, Matrix.transpose_mul, orientationCorrection_transpose]
  calc
    orientationCorrection V * Vᵀ * (V * orientationCorrection V) =
        orientationCorrection V * (Vᵀ * V) * orientationCorrection V := by
          noncomm_ring
    _ = 1 := by rw [hV]; simpa using orientationCorrection_sq hV

lemma orientedMatrix_det {V : Mat3} (hV : Vᵀ * V = 1) :
    (orientedMatrix V).det = 1 := by
  have hd := det_sq_of_transpose_mul_eq_one hV
  rw [orientedMatrix, Matrix.det_mul]
  have hc : (orientationCorrection V).det = V.det := by
    rw [orientationCorrection, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ]
  rw [hc]
  simpa [pow_two] using hd

def orientedSO3 (V : Mat3) (hV : Vᵀ * V = 1) : SO3 :=
  ⟨orientedMatrix V, (Matrix.mem_specialOrthogonalGroup_iff).2
    ⟨(Matrix.mem_orthogonalGroup_iff' I3 ℝ).2
      (orientedMatrix_transpose_mul hV), orientedMatrix_det hV⟩⟩

def swap01 : Mat3 := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
def swap02 : Mat3 := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

lemma swap01_transpose_mul : swap01ᵀ * swap01 = (1 : Mat3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swap01, Matrix.mul_apply, Fin.sum_univ_succ]

lemma swap02_transpose_mul : swap02ᵀ * swap02 = (1 : Mat3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swap02, Matrix.mul_apply, Fin.sum_univ_succ]

lemma so3_involution_symmetric (A : SO3) (hA2 : A * A = 1) :
    (A : Mat3).IsHermitian := by
  have hA2m : (A : Mat3) * A = 1 := by
    simpa using congrArg Subtype.val hA2
  have horth : (A : Mat3)ᵀ * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).1
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  calc
    (A : Mat3)ᵀ = (A : Mat3)ᵀ * 1 := by simp
    _ = (A : Mat3)ᵀ * ((A : Mat3) * A) := by rw [hA2m]
    _ = ((A : Mat3)ᵀ * A) * A := by noncomm_ring
    _ = A := by rw [horth]; simp

lemma eigen_sq_one (A : SO3) (hA2 : A * A = 1)
    (hA : (A : Mat3).IsHermitian) (i : I3) :
    hA.eigenvalues i ^ 2 = 1 := by
  let U : Mat3 := hA.eigenvectorUnitary
  let D : Mat3 := Matrix.diagonal (hA.eigenvalues)
  have hA2m : (A : Mat3) * A = 1 := by
    simpa using congrArg Subtype.val hA2
  have hUtU : Uᵀ * U = 1 := by
    change (hA.eigenvectorUnitary : Mat3)ᵀ * hA.eigenvectorUnitary = 1
    simpa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUUt : U * Uᵀ = 1 := by
    change (hA.eigenvectorUnitary : Mat3) *
      (hA.eigenvectorUnitary : Mat3)ᵀ = 1
    simpa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspect : (A : Mat3) = U * D * Uᵀ := by
    simpa [U, D, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hA.spectral_theorem
  have hDsq : D * D = 1 := by
    have hh := congrArg (fun X : Mat3 ↦ Uᵀ * X * U) hA2m
    rw [hspect] at hh
    calc
      D * D = Uᵀ * ((U * D * Uᵀ) * (U * D * Uᵀ)) * U := by
        calc
          _ = (Uᵀ * U) * D * (Uᵀ * U) * D * (Uᵀ * U) := by
            rw [hUtU]
            simp
          _ = _ := by noncomm_ring
      _ = Uᵀ * 1 * U := hh
      _ = 1 := by simpa only [Matrix.mul_one] using hUtU
  have hii := congrFun (congrFun hDsq i) i
  fin_cases i <;>
    simpa [D, Matrix.mul_apply, Fin.sum_univ_succ, pow_two] using hii

lemma so3_involution_trace_or_one (A : SO3) (hA2 : A * A = 1) :
    (A : Mat3).trace = -1 ∨ A = 1 := by
  let hA := so3_involution_symmetric A hA2
  have h0 := (sq_eq_one_iff).mp (eigen_sq_one A hA2 hA 0)
  have h1 := (sq_eq_one_iff).mp (eigen_sq_one A hA2 hA 1)
  have h2 := (sq_eq_one_iff).mp (eigen_sq_one A hA2 hA 2)
  have hdet : hA.eigenvalues 0 * hA.eigenvalues 1 * hA.eigenvalues 2 = 1 := by
    have hd := hA.det_eq_prod_eigenvalues
    have hAdet : (A : Mat3).det = 1 :=
      (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).2
    rw [hAdet] at hd
    have hd' : 1 = hA.eigenvalues 0 *
        (hA.eigenvalues 1 * hA.eigenvalues 2) := by
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
        RCLike.ofReal_real_eq_id, id_eq] at hd
      convert hd using 1 ; norm_num
    nlinarith
  have htrace : (A : Mat3).trace = hA.eigenvalues 0 +
      hA.eigenvalues 1 + hA.eigenvalues 2 := by
    have ht : (A : Mat3).trace = hA.eigenvalues 0 +
        (hA.eigenvalues 1 + hA.eigenvalues 2) := by
      have ht' := hA.trace_eq_sum_eigenvalues
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
        RCLike.ofReal_real_eq_id, id_eq] at ht'
      convert ht' using 1 ; norm_num
    linarith
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2
  all_goals try { left; rw [htrace, h0, h1, h2]; norm_num }
  all_goals try { exfalso; rw [h0, h1, h2] at hdet; norm_num at hdet }
  · right
    apply Subtype.ext
    have hs := hA.spectral_theorem
    have hUUt : (hA.eigenvectorUnitary : Mat3) *
        (hA.eigenvectorUnitary : Mat3)ᵀ = 1 := by
      simpa [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using
        Unitary.coe_mul_star_self hA.eigenvectorUnitary
    have hD : Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) =
        (1 : Mat3) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]
    rw [hD] at hs
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, hUUt] using hs

lemma correction_preserves_halfTurn1 {V : Mat3} (hV : Vᵀ * V = 1) :
    (orientationCorrection V)ᵀ * (halfTurn1 : Mat3) *
        orientationCorrection V = (halfTurn1 : Mat3) := by
  have hd := det_sq_of_transpose_mul_eq_one hV
  rw [orientationCorrection_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orientationCorrection, halfTurn1, Matrix.mul_apply,
      Fin.sum_univ_succ] ; nlinarith

lemma orientedSO3_conjugates_halfTurn1 {A V : Mat3} (hV : Vᵀ * V = 1)
    (hconj : Vᵀ * A * V = (halfTurn1 : Mat3)) :
    ((orientedSO3 V hV : SO3) : Mat3)ᵀ * A *
        (orientedSO3 V hV : SO3) = (halfTurn1 : Mat3) := by
  change (orientedMatrix V)ᵀ * A * orientedMatrix V = _
  rw [orientedMatrix, Matrix.transpose_mul]
  calc
    (orientationCorrection V)ᵀ * Vᵀ * A *
          (V * orientationCorrection V) =
        (orientationCorrection V)ᵀ * (Vᵀ * A * V) *
          orientationCorrection V := by noncomm_ring
    _ = _ := by rw [hconj]; exact correction_preserves_halfTurn1 hV

lemma so3_involution_conjugate_halfTurn1 (A : SO3) (hA2 : A * A = 1)
    (htr : (A : Mat3).trace = -1) :
    ∃ q : SO3, (q : Mat3)ᵀ * A * q = (halfTurn1 : Mat3) := by
  let hA := so3_involution_symmetric A hA2
  let U : Mat3 := hA.eigenvectorUnitary
  let D : Mat3 := Matrix.diagonal hA.eigenvalues
  have hUtU : Uᵀ * U = 1 := by
    change (hA.eigenvectorUnitary : Mat3)ᵀ * hA.eigenvectorUnitary = 1
    simpa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUUt : U * Uᵀ = 1 := by
    change (hA.eigenvectorUnitary : Mat3) *
      (hA.eigenvectorUnitary : Mat3)ᵀ = 1
    simpa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspect : (A : Mat3) = U * D * Uᵀ := by
    simpa [U, D, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hA.spectral_theorem
  have hdiag : Uᵀ * (A : Mat3) * U = D := by
    rw [hspect]
    calc
      Uᵀ * (U * D * Uᵀ) * U = (Uᵀ * U) * D * (Uᵀ * U) := by
        noncomm_ring
      _ = D := by rw [hUtU]; simp
  have h0 := (sq_eq_one_iff).mp (eigen_sq_one A hA2 hA 0)
  have h1 := (sq_eq_one_iff).mp (eigen_sq_one A hA2 hA 1)
  have h2 := (sq_eq_one_iff).mp (eigen_sq_one A hA2 hA 2)
  have hdet : hA.eigenvalues 0 * hA.eigenvalues 1 * hA.eigenvalues 2 = 1 := by
    have hd := hA.det_eq_prod_eigenvalues
    have hAdet : (A : Mat3).det = 1 :=
      (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).2
    rw [hAdet] at hd
    have hd' : 1 = hA.eigenvalues 0 *
        (hA.eigenvalues 1 * hA.eigenvalues 2) := by
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
        RCLike.ofReal_real_eq_id, id_eq] at hd
      convert hd using 1 ; norm_num
    nlinarith
  have htrace : hA.eigenvalues 0 + hA.eigenvalues 1 +
      hA.eigenvalues 2 = -1 := by
    have ht' := hA.trace_eq_sum_eigenvalues
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      RCLike.ofReal_real_eq_id, id_eq] at ht'
    have ht : (A : Mat3).trace = hA.eigenvalues 0 +
        (hA.eigenvalues 1 + hA.eigenvalues 2) := by
      convert ht' using 1 ; norm_num
    linarith
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2
  · let q := orientedSO3 U hUtU
    exfalso
    norm_num [h0, h1, h2] at htrace
  · exfalso
    norm_num [h0, h1, h2] at hdet
  · exfalso
    norm_num [h0, h1, h2] at hdet
  · let q := orientedSO3 U hUtU
    refine ⟨q, orientedSO3_conjugates_halfTurn1 hUtU ?_⟩
    have hDmat : D = !![(1 : ℝ), 0, 0; 0, -1, 0; 0, 0, -1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [D, h0, h1, h2]
    calc
      Uᵀ * (A : Mat3) * U = D := hdiag
      _ = (halfTurn1 : Mat3) := by
        rw [hDmat]
        ext i j
        fin_cases i <;> fin_cases j <;> norm_num [halfTurn1]
  · exfalso
    norm_num [h0, h1, h2] at hdet
  · have hV : (U * swap01)ᵀ * (U * swap01) = 1 := by
      rw [Matrix.transpose_mul]
      calc
        swap01ᵀ * Uᵀ * (U * swap01) =
            swap01ᵀ * (Uᵀ * U) * swap01 := by noncomm_ring
        _ = 1 := by rw [hUtU]; simpa using swap01_transpose_mul
    let q := orientedSO3 (U * swap01) hV
    refine ⟨q, orientedSO3_conjugates_halfTurn1 hV ?_⟩
    have hDmat : D = !![-(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, -1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [D, h0, h1, h2]
    calc
      (U * swap01)ᵀ * (A : Mat3) * (U * swap01) =
          swap01ᵀ * (Uᵀ * (A : Mat3) * U) * swap01 := by
            rw [Matrix.transpose_mul]
            noncomm_ring
      _ = swap01ᵀ * D * swap01 := by rw [hdiag]
      _ = (halfTurn1 : Mat3) := by
        rw [hDmat]
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [swap01, halfTurn1,
            Matrix.mul_apply, Fin.sum_univ_succ]
  · have hV : (U * swap02)ᵀ * (U * swap02) = 1 := by
      rw [Matrix.transpose_mul]
      calc
        swap02ᵀ * Uᵀ * (U * swap02) =
            swap02ᵀ * (Uᵀ * U) * swap02 := by noncomm_ring
        _ = 1 := by rw [hUtU]; simpa using swap02_transpose_mul
    let q := orientedSO3 (U * swap02) hV
    refine ⟨q, orientedSO3_conjugates_halfTurn1 hV ?_⟩
    have hDmat : D = !![-(1 : ℝ), 0, 0; 0, -1, 0; 0, 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [D, h0, h1, h2]
    calc
      (U * swap02)ᵀ * (A : Mat3) * (U * swap02) =
          swap02ᵀ * (Uᵀ * (A : Mat3) * U) * swap02 := by
            rw [Matrix.transpose_mul]
            noncomm_ring
      _ = swap02ᵀ * D * swap02 := by rw [hdiag]
      _ = (halfTurn1 : Mat3) := by
        rw [hDmat]
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [swap02, halfTurn1,
            Matrix.mul_apply, Fin.sum_univ_succ]
  · exfalso
    norm_num [h0, h1, h2] at hdet

lemma so3_inv_coe (q : SO3) : (((q⁻¹ : SO3) : Mat3)) = (q : Mat3)ᵀ := by
  change star (q : Mat3) = (q : Mat3)ᵀ
  rw [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

def innerTrace (s : InnerAction) : ℝ := (innerMatrix s).trace

lemma innerTrace_eq (s : InnerAction) :
    innerTrace s = (s.1 : Mat3).trace + (s.2 : Mat3).trace := by
  rw [innerTrace, Matrix.trace]
  simp [innerMatrix, Fintype.sum_sum_type]
  rfl

lemma standardize_trace_neg_two_involution (s : InnerAction)
    (hsq : s * s = 1) (htr : innerTrace s = -2) :
    ∃ q : InnerAction, q⁻¹ * s * q = diagonalTurn1 := by
  have hs1 : s.1 * s.1 = 1 := by
    simpa using congrArg Prod.fst hsq
  have hs2 : s.2 * s.2 = 1 := by
    simpa using congrArg Prod.snd hsq
  rcases so3_involution_trace_or_one s.1 hs1 with ht1 | he1
  · rcases so3_involution_trace_or_one s.2 hs2 with ht2 | he2
    · obtain ⟨q1, hq1⟩ := so3_involution_conjugate_halfTurn1 s.1 hs1 ht1
      obtain ⟨q2, hq2⟩ := so3_involution_conjugate_halfTurn1 s.2 hs2 ht2
      refine ⟨(q1, q2), ?_⟩
      apply Prod.ext
      · change q1⁻¹ * s.1 * q1 = halfTurn1
        apply Subtype.ext
        simpa [so3_inv_coe] using hq1
      · change q2⁻¹ * s.2 * q2 = halfTurn1
        apply Subtype.ext
        simpa [so3_inv_coe] using hq2
    · have htrace2 : (s.2 : Mat3).trace = 3 := by
        rw [he2]
        norm_num [Matrix.trace_fin_three]
      rw [innerTrace_eq, ht1, htrace2] at htr
      norm_num at htr
  · have htrace1 : (s.1 : Mat3).trace = 3 := by
      rw [he1]
      norm_num [Matrix.trace_fin_three]
    rcases so3_involution_trace_or_one s.2 hs2 with ht2 | he2
    · rw [innerTrace_eq, htrace1, ht2] at htr
      norm_num at htr
    · have htrace2 : (s.2 : Mat3).trace = 3 := by
        rw [he2]
        norm_num [Matrix.trace_fin_three]
      rw [innerTrace_eq, htrace1, htrace2] at htr
      norm_num at htr

end S3xS3.Z2

namespace S3xS3.Z2

def planePart (N : Mat3) : Mat2 :=
  !![N 1 1, N 1 2; N 2 1, N 2 2]

lemma halfTurn1_fixed_iff_liftPlane (N : Mat3) :
    (halfTurn1 : Mat3)ᵀ * N * halfTurn1 = N ↔
      N = liftPlane (N 0 0) (planePart N) := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    have h02 := congrFun (congrFun h 0) 2
    have h10 := congrFun (congrFun h 1) 0
    have h20 := congrFun (congrFun h 2) 0
    norm_num [halfTurn1, Matrix.diagonal, Matrix.mul_apply,
      Fin.sum_univ_succ] at h01 h02 h10 h20
    simp at h02 h20
    have hz01 : N 0 1 = 0 := by linarith
    have hz02 : N 0 2 = 0 := by linarith
    have hz10 : N 1 0 = 0 := by linarith
    have hz20 : N 2 0 = 0 := by linarith
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [liftPlane, planePart, hz01, hz02, hz10, hz20]
  · intro h
    have hleft := congrArg
      (fun X : Mat3 ↦ (halfTurn1 : Mat3)ᵀ * X * halfTurn1) h
    have hmiddle : (halfTurn1 : Mat3)ᵀ *
          liftPlane (N 0 0) (planePart N) * halfTurn1 =
        liftPlane (N 0 0) (planePart N) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [halfTurn1, Matrix.diagonal, liftPlane,
          Matrix.mul_apply]
    calc
      (halfTurn1 : Mat3)ᵀ * N * halfTurn1 =
          (halfTurn1 : Mat3)ᵀ *
            liftPlane (N 0 0) (planePart N) * halfTurn1 := hleft
      _ = liftPlane (N 0 0) (planePart N) := hmiddle
      _ = N := h.symm

def orientationCorrection2 (V : Mat2) : Mat2 :=
  Matrix.diagonal ![V.det, (1 : ℝ)]

def orientedMatrix2 (V : Mat2) : Mat2 := V * orientationCorrection2 V

lemma det_sq_of_transpose_mul_eq_one2 {V : Mat2} (hV : Vᵀ * V = 1) :
    V.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hV
  rw [Matrix.det_mul, Matrix.det_transpose] at h
  simpa [pow_two] using h

lemma orientationCorrection2_transpose (V : Mat2) :
    (orientationCorrection2 V)ᵀ = orientationCorrection2 V := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [orientationCorrection2]

lemma orientationCorrection2_sq {V : Mat2} (hV : Vᵀ * V = 1) :
    orientationCorrection2 V * orientationCorrection2 V = 1 := by
  have hd := det_sq_of_transpose_mul_eq_one2 hV
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orientationCorrection2, Matrix.mul_apply, Fin.sum_univ_succ] ;
    nlinarith

lemma orientedMatrix2_transpose_mul {V : Mat2} (hV : Vᵀ * V = 1) :
    (orientedMatrix2 V)ᵀ * orientedMatrix2 V = 1 := by
  rw [orientedMatrix2, Matrix.transpose_mul, orientationCorrection2_transpose]
  calc
    orientationCorrection2 V * Vᵀ * (V * orientationCorrection2 V) =
        orientationCorrection2 V * (Vᵀ * V) * orientationCorrection2 V := by
          noncomm_ring
    _ = 1 := by rw [hV]; simpa using orientationCorrection2_sq hV

lemma orientedMatrix2_det {V : Mat2} (hV : Vᵀ * V = 1) :
    (orientedMatrix2 V).det = 1 := by
  have hd := det_sq_of_transpose_mul_eq_one2 hV
  rw [orientedMatrix2, Matrix.det_mul]
  have hc : (orientationCorrection2 V).det = V.det := by
    rw [orientationCorrection2, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ]
  rw [hc]
  simpa [pow_two] using hd

def orientedSO2 (V : Mat2) (hV : Vᵀ * V = 1) : SO2 :=
  ⟨orientedMatrix2 V, (Matrix.mem_specialOrthogonalGroup_iff).2
    ⟨(Matrix.mem_orthogonalGroup_iff' I2 ℝ).2
      (orientedMatrix2_transpose_mul hV), orientedMatrix2_det hV⟩⟩

lemma correction2_preserves_diagonal (V : Mat2) (u v : ℝ)
    (hV : Vᵀ * V = 1) :
    (orientationCorrection2 V)ᵀ * diag2 u v * orientationCorrection2 V =
      diag2 u v := by
  have hd := det_sq_of_transpose_mul_eq_one2 hV
  rw [orientationCorrection2_transpose]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [orientationCorrection2, diag2, Matrix.mul_apply,
      Fin.sum_univ_succ]
    calc
      V.det * u * V.det = V.det ^ 2 * u := by ring
      _ = u := by rw [hd]; ring
  all_goals simp [orientationCorrection2, diag2, Matrix.mul_apply,
    Fin.sum_univ_succ]

theorem diagonalize_posDef_two {N : Mat2} (hN : N.PosDef) :
    ∃ q : SO2, ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
      (q : Mat2)ᵀ * N * q = diag2 u v := by
  let U : Mat2 := hN.isHermitian.eigenvectorUnitary
  let u : ℝ := hN.isHermitian.eigenvalues 0
  let v : ℝ := hN.isHermitian.eigenvalues 1
  have hu : 0 < u := hN.eigenvalues_pos 0
  have hv : 0 < v := hN.eigenvalues_pos 1
  have hUtU : Uᵀ * U = 1 := by
    change (hN.isHermitian.eigenvectorUnitary : Mat2)ᵀ *
      hN.isHermitian.eigenvectorUnitary = 1
    simpa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hN.isHermitian.eigenvectorUnitary
  have hUUt : U * Uᵀ = 1 := by
    change (hN.isHermitian.eigenvectorUnitary : Mat2) *
      (hN.isHermitian.eigenvectorUnitary : Mat2)ᵀ = 1
    simpa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hN.isHermitian.eigenvectorUnitary
  have hspect : N = U * diag2 u v * Uᵀ := by
    have hs := hN.isHermitian.spectral_theorem
    have hD : Matrix.diagonal
        (RCLike.ofReal ∘ hN.isHermitian.eigenvalues) = diag2 u v := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [u, v, diag2]
    rw [hD] at hs
    simpa [U, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hs
  have hdiag : Uᵀ * N * U = diag2 u v := by
    rw [hspect]
    calc
      Uᵀ * (U * diag2 u v * Uᵀ) * U =
          (Uᵀ * U) * diag2 u v * (Uᵀ * U) := by noncomm_ring
      _ = diag2 u v := by rw [hUtU]; simp
  let q := orientedSO2 U hUtU
  refine ⟨q, u, v, hu, hv, ?_⟩
  change (orientedMatrix2 U)ᵀ * N * orientedMatrix2 U = _
  rw [orientedMatrix2, Matrix.transpose_mul]
  calc
    (orientationCorrection2 U)ᵀ * Uᵀ * N *
          (U * orientationCorrection2 U) =
        (orientationCorrection2 U)ᵀ * (Uᵀ * N * U) *
          orientationCorrection2 U := by noncomm_ring
    _ = _ := by rw [hdiag]; exact correction2_preserves_diagonal U u v hUtU

end S3xS3.Z2

namespace S3xS3.Z2

lemma fixed_by_standard_turn_blocks {K : Mat6}
    (hK : (innerMatrix diagonalTurn1)ᵀ * K *
      innerMatrix diagonalTurn1 = K) :
    (halfTurn1 : Mat3)ᵀ * K.toBlocks₁₁ * halfTurn1 = K.toBlocks₁₁ ∧
    (halfTurn1 : Mat3)ᵀ * K.toBlocks₁₂ * halfTurn1 = K.toBlocks₁₂ ∧
    (halfTurn1 : Mat3)ᵀ * K.toBlocks₂₁ * halfTurn1 = K.toBlocks₂₁ ∧
    (halfTurn1 : Mat3)ᵀ * K.toBlocks₂₂ * halfTurn1 = K.toBlocks₂₂ := by
  have hK' :
      (Matrix.fromBlocks (halfTurn1 : Mat3) 0 0 halfTurn1 : Mat6)ᵀ *
          Matrix.fromBlocks K.toBlocks₁₁ K.toBlocks₁₂
            K.toBlocks₂₁ K.toBlocks₂₂ *
          Matrix.fromBlocks halfTurn1 0 0 halfTurn1 =
        Matrix.fromBlocks K.toBlocks₁₁ K.toBlocks₁₂
          K.toBlocks₂₁ K.toBlocks₂₂ := by
    rw [Matrix.fromBlocks_toBlocks]
    simpa [innerMatrix, diagonalTurn1] using hK
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hK'
  simpa using (Matrix.fromBlocks_inj.mp hK')

lemma fixed_by_standard_turn_lift_blocks {K : Mat6}
    (hK : (innerMatrix diagonalTurn1)ᵀ * K *
      innerMatrix diagonalTurn1 = K) :
    ∃ a b c d : ℝ, ∃ A B C D : Mat2,
      K = Matrix.fromBlocks (liftPlane a A) (liftPlane b B)
        (liftPlane c C) (liftPlane d D) := by
  rcases fixed_by_standard_turn_blocks hK with ⟨h11, h12, h21, h22⟩
  have e11 := (halfTurn1_fixed_iff_liftPlane _).mp h11
  have e12 := (halfTurn1_fixed_iff_liftPlane _).mp h12
  have e21 := (halfTurn1_fixed_iff_liftPlane _).mp h21
  have e22 := (halfTurn1_fixed_iff_liftPlane _).mp h22
  refine ⟨K.toBlocks₁₁ 0 0, K.toBlocks₁₂ 0 0,
    K.toBlocks₂₁ 0 0, K.toBlocks₂₂ 0 0,
    planePart K.toBlocks₁₁, planePart K.toBlocks₁₂,
    planePart K.toBlocks₂₁, planePart K.toBlocks₂₂, ?_⟩
  calc
    K = Matrix.fromBlocks K.toBlocks₁₁ K.toBlocks₁₂
        K.toBlocks₂₁ K.toBlocks₂₂ := (Matrix.fromBlocks_toBlocks K).symm
    _ = _ := Matrix.fromBlocks_inj.mpr ⟨e11, e12, e21, e22⟩

def planeEmbed : I2 → I3 := ![1, 2]

lemma planeEmbed_injective : Function.Injective planeEmbed := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [planeEmbed]

lemma submatrix_plane_eq_planePart (N : Mat3) :
    N.submatrix planeEmbed planeEmbed = planePart N := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma planePart_posDef {N : Mat3} (hN : N.PosDef) :
    (planePart N).PosDef := by
  rw [← submatrix_plane_eq_planePart]
  exact hN.submatrix planeEmbed_injective

lemma block22_posDef {K : Mat6} (hK : K.PosDef) : K.toBlocks₂₂.PosDef := by
  exact hK.submatrix Sum.inr_injective

lemma block11_posDef {K : Mat6} (hK : K.PosDef) : K.toBlocks₁₁.PosDef := by
  exact hK.submatrix Sum.inl_injective

lemma block21_eq_transpose_block12 {K : Mat6} (hK : K.IsHermitian) :
    K.toBlocks₂₁ = K.toBlocks₁₂ᵀ := by
  ext i j
  have hij := congrFun (congrFun hK.eq (Sum.inl j)) (Sum.inr i)
  simpa [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hij

theorem schur_posDef {K : Mat6} (hK : K.PosDef) :
    (K.toBlocks₁₁ - K.toBlocks₁₂ * K.toBlocks₂₂⁻¹ *
      K.toBlocks₁₂ᵀ).PosDef := by
  let A : Mat3 := K.toBlocks₁₁
  let B : Mat3 := K.toBlocks₁₂
  let D : Mat3 := K.toBlocks₂₂
  have hD : D.PosDef := block22_posDef hK
  letI : Invertible D := hD.isUnit.invertible
  have hform : K = Matrix.fromBlocks A B Bᴴ D := by
    rw [← Matrix.fromBlocks_toBlocks K]
    congr 1
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      block21_eq_transpose_block12 hK.isHermitian
  have hA : A.PosDef := block11_posDef hK
  have hterm : (B * D⁻¹ * Bᴴ).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose B hD.isHermitian.inv
  have hSsym : (A - B * D⁻¹ * Bᴴ).IsHermitian :=
    hA.isHermitian.sub hterm
  have hS : (A - B * D⁻¹ * Bᴴ).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hSsym
    intro x hx
    let y : I3 → ℝ := -((D⁻¹ * Bᴴ) *ᵥ x)
    have hxy : Sum.elim x y ≠ 0 := by
      intro hz
      apply hx
      funext i
      have hi := congrFun hz (Sum.inl i)
      exact hi
    have hp := hK.dotProduct_mulVec_pos hxy
    rw [hform] at hp
    rw [Matrix.dotProduct_mulVec,
      Matrix.schur_complement_eq₂₂ A B x y hD.isHermitian] at hp
    rw [Matrix.dotProduct_mulVec]
    simpa [y, Matrix.conjTranspose_eq_transpose_of_trivial] using hp
  simpa [A, B, D, Matrix.conjTranspose_eq_transpose_of_trivial] using hS

lemma halfTurn1_transpose : (halfTurn1 : Mat3)ᵀ = halfTurn1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [halfTurn1]

lemma halfTurn1_matrix_sq : (halfTurn1 : Mat3) * halfTurn1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [halfTurn1, Matrix.diagonal, Matrix.mul_apply,
      Fin.sum_univ_succ]

lemma standardFixed_mul {X Y : Mat3}
    (hX : (halfTurn1 : Mat3)ᵀ * X * halfTurn1 = X)
    (hY : (halfTurn1 : Mat3)ᵀ * Y * halfTurn1 = Y) :
    (halfTurn1 : Mat3)ᵀ * (X * Y) * halfTurn1 = X * Y := by
  rw [halfTurn1_transpose] at hX hY ⊢
  calc
    (halfTurn1 : Mat3) * (X * Y) * halfTurn1 =
        halfTurn1 * X * 1 * Y * halfTurn1 := by noncomm_ring
    _ = halfTurn1 * X * (halfTurn1 * halfTurn1) * Y * halfTurn1 := by
      rw [halfTurn1_matrix_sq]
    _ = (halfTurn1 * X * halfTurn1) *
          (halfTurn1 * Y * halfTurn1) := by noncomm_ring
    _ = X * Y := by rw [hX, hY]

lemma standardFixed_transpose {X : Mat3}
    (hX : (halfTurn1 : Mat3)ᵀ * X * halfTurn1 = X) :
    (halfTurn1 : Mat3)ᵀ * Xᵀ * halfTurn1 = Xᵀ := by
  have ht := congrArg Matrix.transpose hX
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, halfTurn1_transpose] at ht
  simpa only [Matrix.mul_assoc, halfTurn1_transpose] using ht

lemma standardFixed_inv {X : Mat3}
    (hX : (halfTurn1 : Mat3)ᵀ * X * halfTurn1 = X) :
    (halfTurn1 : Mat3)ᵀ * X⁻¹ * halfTurn1 = X⁻¹ := by
  have hi := congrArg (fun M : Mat3 ↦ M⁻¹) hX
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev] at hi
  rw [halfTurn1_transpose] at hi ⊢
  have hhinv : (halfTurn1 : Mat3)⁻¹ = halfTurn1 :=
    Matrix.inv_eq_right_inv halfTurn1_matrix_sq
  rw [hhinv] at hi
  simpa only [Matrix.mul_assoc] using hi

lemma standardFixed_sub {X Y : Mat3}
    (hX : (halfTurn1 : Mat3)ᵀ * X * halfTurn1 = X)
    (hY : (halfTurn1 : Mat3)ᵀ * Y * halfTurn1 = Y) :
    (halfTurn1 : Mat3)ᵀ * (X - Y) * halfTurn1 = X - Y := by
  rw [Matrix.mul_sub, Matrix.sub_mul, hX, hY]

lemma schur_fixed_by_standard_turn {K : Mat6}
    (hK : (innerMatrix diagonalTurn1)ᵀ * K *
      innerMatrix diagonalTurn1 = K) :
    (halfTurn1 : Mat3)ᵀ *
        (K.toBlocks₁₁ - K.toBlocks₁₂ * K.toBlocks₂₂⁻¹ *
          K.toBlocks₁₂ᵀ) * halfTurn1 =
      K.toBlocks₁₁ - K.toBlocks₁₂ * K.toBlocks₂₂⁻¹ *
        K.toBlocks₁₂ᵀ := by
  rcases fixed_by_standard_turn_blocks hK with ⟨hA, hB, -, hD⟩
  exact standardFixed_sub hA
    (standardFixed_mul (standardFixed_mul hB (standardFixed_inv hD))
      (standardFixed_transpose hB))

lemma block_diagonal_congruence (A B C D U V : Mat3) :
    (Matrix.fromBlocks U 0 0 V : Mat6)ᵀ *
        Matrix.fromBlocks A B C D * Matrix.fromBlocks U 0 0 V =
      Matrix.fromBlocks (Uᵀ * A * U) (Uᵀ * B * V)
        (Vᵀ * C * U) (Vᵀ * D * V) := by
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

lemma orthogonal_congruence_inv (V D : Mat3)
    (hVVt : V * Vᵀ = 1) (hVtV : Vᵀ * V = 1) :
    (Vᵀ * D * V)⁻¹ = Vᵀ * D⁻¹ * V := by
  have hVinv : V⁻¹ = Vᵀ := Matrix.inv_eq_right_inv hVVt
  have hVtinv : Vᵀ⁻¹ = V := Matrix.inv_eq_right_inv hVtV
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hVinv, hVtinv]
  noncomm_ring

lemma triangular_factor_cometric
    (A B D E M F : Mat3) (hF : IsUnit F)
    (hFF : Fᵀ * F = D) (hMF : Mᵀ * F = B)
    (hEE : Eᵀ * E = A - B * D⁻¹ * Bᵀ) :
    (Matrix.fromBlocks E 0 M F : Mat6)ᵀ *
        Matrix.fromBlocks E 0 M F =
      Matrix.fromBlocks A B Bᵀ D := by
  have hFt : IsUnit Fᵀ := (Matrix.isUnit_transpose F).2 hF
  have hD : IsUnit D := by rw [← hFF]; exact hFt.mul hF
  letI : Invertible F := hF.invertible
  letI : Invertible Fᵀ := hFt.invertible
  have hFinvL : F⁻¹ * F = 1 := Matrix.inv_mul_of_invertible F
  have hFinvR : F * F⁻¹ = 1 := Matrix.mul_inv_of_invertible F
  have hFtinvL : Fᵀ⁻¹ * Fᵀ = 1 := Matrix.inv_mul_of_invertible Fᵀ
  have hFtinvR : Fᵀ * Fᵀ⁻¹ = 1 := Matrix.mul_inv_of_invertible Fᵀ
  have hDinv : D⁻¹ = F⁻¹ * Fᵀ⁻¹ := by
    rw [← hFF, Matrix.mul_inv_rev]
  have hBM : Bᵀ = Fᵀ * M := by
    rw [← hMF, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hMM' : B * D⁻¹ * Bᵀ = Mᵀ * M := by
    rw [hBM, ← hMF, hDinv]
    calc
      Mᵀ * F * (F⁻¹ * Fᵀ⁻¹) * (Fᵀ * M) =
          Mᵀ * (F * F⁻¹) * (Fᵀ⁻¹ * Fᵀ) * M := by noncomm_ring
      _ = Mᵀ * M := by
        rw [hFinvR, hFtinvL]
        simp
  have hMM : Mᵀ * M = B * D⁻¹ * Bᵀ := hMM'.symm
  rw [triangular_frame_cometric, hFF, hMF, hBM, hMM]
  congr 1
  rw [hEE]
  noncomm_ring

end S3xS3.Z2

namespace S3xS3.Z2

structure RawParameters where
  a₀ : ℝ
  b₀ : ℝ
  c₀ : ℝ
  d₀ : ℝ
  e₀ : ℝ
  f₀ : ℝ
  x₀ : ℝ
  y₀ : ℝ
  z₀ : ℝ
  w₀ : ℝ
  t₀ : ℝ

structure RawPositive (r : RawParameters) : Prop where
  a₀_pos : 0 < r.a₀
  b₀_pos : 0 < r.b₀
  c₀_pos : 0 < r.c₀
  d₀_pos : 0 < r.d₀
  e₀_pos : 0 < r.e₀
  f₀_pos : 0 < r.f₀

namespace RawParameters

def eDiag (r : RawParameters) : Mat3 :=
  Matrix.diagonal ![r.a₀, r.b₀, r.c₀]

def fDiag (r : RawParameters) : Mat3 :=
  Matrix.diagonal ![r.d₀, r.e₀, r.f₀]

def mixing (r : RawParameters) : Mat3 :=
  !![r.x₀, 0, 0; 0, r.y₀, r.w₀; 0, r.t₀, r.z₀]

def frame (r : RawParameters) : Mat6 :=
  Matrix.fromBlocks r.eDiag 0 r.mixing r.fDiag

noncomputable def toParameters (r : RawParameters) : Parameters where
  a := r.b₀ * r.c₀ / r.a₀
  b := r.a₀ * r.c₀ / r.b₀
  c := r.a₀ * r.b₀ / r.c₀
  d := r.e₀ * r.f₀ / r.d₀
  e := r.d₀ * r.f₀ / r.e₀
  f := r.d₀ * r.e₀ / r.f₀
  x := r.x₀ / r.a₀
  y := r.y₀ / r.b₀
  z := r.z₀ / r.c₀
  w := r.w₀ / r.c₀
  t := r.t₀ / r.b₀

end RawParameters

lemma raw_toParameters_positive {r : RawParameters} (h : RawPositive r) :
    PositiveParameters r.toParameters := by
  constructor
  · exact div_pos (mul_pos h.b₀_pos h.c₀_pos) h.a₀_pos
  · exact div_pos (mul_pos h.a₀_pos h.c₀_pos) h.b₀_pos
  · exact div_pos (mul_pos h.a₀_pos h.b₀_pos) h.c₀_pos
  · exact div_pos (mul_pos h.e₀_pos h.f₀_pos) h.d₀_pos
  · exact div_pos (mul_pos h.d₀_pos h.f₀_pos) h.e₀_pos
  · exact div_pos (mul_pos h.d₀_pos h.e₀_pos) h.f₀_pos

lemma sqrt_raw_ab {r : RawParameters} (h : RawPositive r) :
    Real.sqrt (r.toParameters.a * r.toParameters.b) = r.c₀ := by
  have ha : r.a₀ ≠ 0 := ne_of_gt h.a₀_pos
  have hb : r.b₀ ≠ 0 := ne_of_gt h.b₀_pos
  have hc : 0 ≤ r.c₀ := h.c₀_pos.le
  have hp := raw_toParameters_positive h
  apply (Real.sqrt_eq_iff_eq_sq
    (mul_nonneg hp.a_pos.le hp.b_pos.le) hc).2
  dsimp [RawParameters.toParameters]
  field_simp

lemma sqrt_raw_ac {r : RawParameters} (h : RawPositive r) :
    Real.sqrt (r.toParameters.a * r.toParameters.c) = r.b₀ := by
  have ha : r.a₀ ≠ 0 := ne_of_gt h.a₀_pos
  have hc : r.c₀ ≠ 0 := ne_of_gt h.c₀_pos
  have hb : 0 ≤ r.b₀ := h.b₀_pos.le
  have hp := raw_toParameters_positive h
  apply (Real.sqrt_eq_iff_eq_sq
    (mul_nonneg hp.a_pos.le hp.c_pos.le) hb).2
  dsimp [RawParameters.toParameters]
  field_simp

lemma sqrt_raw_bc {r : RawParameters} (h : RawPositive r) :
    Real.sqrt (r.toParameters.b * r.toParameters.c) = r.a₀ := by
  have hb : r.b₀ ≠ 0 := ne_of_gt h.b₀_pos
  have hc : r.c₀ ≠ 0 := ne_of_gt h.c₀_pos
  have ha : 0 ≤ r.a₀ := h.a₀_pos.le
  have hp := raw_toParameters_positive h
  apply (Real.sqrt_eq_iff_eq_sq
    (mul_nonneg hp.b_pos.le hp.c_pos.le) ha).2
  dsimp [RawParameters.toParameters]
  field_simp

lemma sqrt_raw_de {r : RawParameters} (h : RawPositive r) :
    Real.sqrt (r.toParameters.d * r.toParameters.e) = r.f₀ := by
  have hd : r.d₀ ≠ 0 := ne_of_gt h.d₀_pos
  have he : r.e₀ ≠ 0 := ne_of_gt h.e₀_pos
  have hf : 0 ≤ r.f₀ := h.f₀_pos.le
  have hp := raw_toParameters_positive h
  apply (Real.sqrt_eq_iff_eq_sq
    (mul_nonneg hp.d_pos.le hp.e_pos.le) hf).2
  dsimp [RawParameters.toParameters]
  field_simp

lemma sqrt_raw_df {r : RawParameters} (h : RawPositive r) :
    Real.sqrt (r.toParameters.d * r.toParameters.f) = r.e₀ := by
  have hd : r.d₀ ≠ 0 := ne_of_gt h.d₀_pos
  have hf : r.f₀ ≠ 0 := ne_of_gt h.f₀_pos
  have he : 0 ≤ r.e₀ := h.e₀_pos.le
  have hp := raw_toParameters_positive h
  apply (Real.sqrt_eq_iff_eq_sq
    (mul_nonneg hp.d_pos.le hp.f_pos.le) he).2
  dsimp [RawParameters.toParameters]
  field_simp

lemma sqrt_raw_ef {r : RawParameters} (h : RawPositive r) :
    Real.sqrt (r.toParameters.e * r.toParameters.f) = r.d₀ := by
  have he : r.e₀ ≠ 0 := ne_of_gt h.e₀_pos
  have hf : r.f₀ ≠ 0 := ne_of_gt h.f₀_pos
  have hd : 0 ≤ r.d₀ := h.d₀_pos.le
  have hp := raw_toParameters_positive h
  apply (Real.sqrt_eq_iff_eq_sq
    (mul_nonneg hp.e_pos.le hp.f_pos.le) hd).2
  dsimp [RawParameters.toParameters]
  field_simp

lemma parameters_frame_eq_raw {r : RawParameters} (h : RawPositive r) :
    r.toParameters.frame = r.frame := by
  rw [Parameters.frame, RawParameters.frame]
  congr 1
  · rw [Parameters.eDiag, sqrt_raw_bc h, Parameters.planeE,
      sqrt_raw_ac h, sqrt_raw_ab h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [liftPlane, diag2, RawParameters.eDiag]
  · rw [Parameters.mixing, sqrt_raw_bc h, Parameters.planeN,
      sqrt_raw_ac h, sqrt_raw_ab h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [liftPlane, RawParameters.mixing,
        RawParameters.toParameters] <;>
      field_simp [ne_of_gt h.a₀_pos, ne_of_gt h.b₀_pos,
        ne_of_gt h.c₀_pos]
  · rw [Parameters.fDiag, sqrt_raw_ef h, Parameters.planeF,
      sqrt_raw_df h, sqrt_raw_de h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [liftPlane, diag2, RawParameters.fDiag]

theorem standard_invariant_cometric_normal_form {K : Mat6}
    (hKpos : K.PosDef)
    (hKfix : (innerMatrix diagonalTurn1)ᵀ * K *
      innerMatrix diagonalTurn1 = K) :
    ∃ q : InnerAction, ∃ r : RawParameters, RawPositive r ∧
      (innerMatrix q)ᵀ * K * innerMatrix q = r.frameᵀ * r.frame := by
  let A : Mat3 := K.toBlocks₁₁
  let B : Mat3 := K.toBlocks₁₂
  let D : Mat3 := K.toBlocks₂₂
  let S : Mat3 := A - B * D⁻¹ * Bᵀ
  have hDpos : D.PosDef := block22_posDef hKpos
  have hSpos : S.PosDef := by
    simpa [S, A, B, D] using schur_posDef hKpos
  rcases fixed_by_standard_turn_blocks hKfix with ⟨hAfix, hBfix, -, hDfix⟩
  have hSfix : (halfTurn1 : Mat3)ᵀ * S * halfTurn1 = S := by
    simpa [S, A, B, D] using schur_fixed_by_standard_turn hKfix
  let d : ℝ := D 0 0
  let DP : Mat2 := planePart D
  let s : ℝ := S 0 0
  let SP : Mat2 := planePart S
  have eD : D = liftPlane d DP :=
    (halfTurn1_fixed_iff_liftPlane D).mp hDfix
  have eS : S = liftPlane s SP :=
    (halfTurn1_fixed_iff_liftPlane S).mp hSfix
  have hd : 0 < d := hDpos.diag_pos
  have hs : 0 < s := hSpos.diag_pos
  have hDP : DP.PosDef := planePart_posDef hDpos
  have hSP : SP.PosDef := planePart_posDef hSpos
  obtain ⟨qD, d₁, d₂, hd₁, hd₂, hqD⟩ := diagonalize_posDef_two hDP
  obtain ⟨qS, s₁, s₂, hs₁, hs₂, hqS⟩ := diagonalize_posDef_two hSP
  let U : Mat3 := extendSO2 qS
  let V : Mat3 := extendSO2 qD
  have hUtU : Uᵀ * U = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff' I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp (extendSO2 qS).property).1
  have hUUt : U * Uᵀ = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp (extendSO2 qS).property).1
  have hVtV : Vᵀ * V = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff' I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp (extendSO2 qD).property).1
  have hVVt : V * Vᵀ = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff I3 ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp (extendSO2 qD).property).1
  have hSrot : Uᵀ * S * U = liftPlane s (diag2 s₁ s₂) := by
    change (extendSO2Matrix qS)ᵀ * S * extendSO2Matrix qS = _
    rw [extendSO2Matrix_eq_liftPlane, liftPlane_transpose, eS,
      liftPlane_mul, liftPlane_mul]
    simpa [Matrix.mul_assoc] using congrArg (liftPlane s) hqS
  have hDrot : Vᵀ * D * V = liftPlane d (diag2 d₁ d₂) := by
    change (extendSO2Matrix qD)ᵀ * D * extendSO2Matrix qD = _
    rw [extendSO2Matrix_eq_liftPlane, liftPlane_transpose, eD,
      liftPlane_mul, liftPlane_mul]
    simpa [Matrix.mul_assoc] using congrArg (liftPlane d) hqD
  let b : ℝ := B 0 0
  let BP : Mat2 := planePart B
  have eB : B = liftPlane b BP :=
    (halfTurn1_fixed_iff_liftPlane B).mp hBfix
  let N : Mat2 := (qS : Mat2)ᵀ * BP * (qD : Mat2)
  have hBrot : Uᵀ * B * V = liftPlane b N := by
    change (extendSO2Matrix qS)ᵀ * B * extendSO2Matrix qD = _
    rw [extendSO2Matrix_eq_liftPlane qS,
      extendSO2Matrix_eq_liftPlane qD, liftPlane_transpose, eB,
      liftPlane_mul, liftPlane_mul]
    simp [N]
  let r : RawParameters :=
    { a₀ := Real.sqrt s
      b₀ := Real.sqrt s₁
      c₀ := Real.sqrt s₂
      d₀ := Real.sqrt d
      e₀ := Real.sqrt d₁
      f₀ := Real.sqrt d₂
      x₀ := b / Real.sqrt d
      y₀ := N 0 0 / Real.sqrt d₁
      z₀ := N 1 1 / Real.sqrt d₂
      w₀ := N 1 0 / Real.sqrt d₁
      t₀ := N 0 1 / Real.sqrt d₂ }
  have hrpos : RawPositive r := by
    constructor <;> dsimp [r] <;> exact Real.sqrt_pos.2 ‹_›
  have hsd : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  have hsd₁ : Real.sqrt d₁ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd₁)
  have hsd₂ : Real.sqrt d₂ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd₂)
  have hFF : r.fDiagᵀ * r.fDiag = Vᵀ * D * V := by
    rw [hDrot]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [r, RawParameters.fDiag, liftPlane, diag2,
        Matrix.mul_apply, Fin.sum_univ_succ,
        Real.mul_self_sqrt hd.le, Real.mul_self_sqrt hd₁.le,
        Real.mul_self_sqrt hd₂.le]
  have hMF : r.mixingᵀ * r.fDiag = Uᵀ * B * V := by
    rw [hBrot]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [r, RawParameters.mixing, RawParameters.fDiag,
        liftPlane, N, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp [hsd, hsd₁, hsd₂]
  have hEGram : r.eDiagᵀ * r.eDiag = Uᵀ * S * U := by
    rw [hSrot]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [r, RawParameters.eDiag, liftPlane, diag2,
        Matrix.mul_apply, Fin.sum_univ_succ,
        Real.mul_self_sqrt hs.le, Real.mul_self_sqrt hs₁.le,
        Real.mul_self_sqrt hs₂.le]
  have hBinvTerm :
      (Uᵀ * B * V) * (Vᵀ * D * V)⁻¹ * (Uᵀ * B * V)ᵀ =
        Uᵀ * (B * D⁻¹ * Bᵀ) * U := by
    rw [orthogonal_congruence_inv V D hVVt hVtV,
      Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    calc
      (Uᵀ * B * V) * (Vᵀ * D⁻¹ * V) *
            (Vᵀ * (Bᵀ * U)) =
          Uᵀ * B * (V * Vᵀ) * D⁻¹ * (V * Vᵀ) * Bᵀ * U := by
            noncomm_ring
      _ = Uᵀ * (B * D⁻¹ * Bᵀ) * U := by
        rw [hVVt]
        noncomm_ring
  have hSchurRot :
      Uᵀ * A * U -
          (Uᵀ * B * V) * (Vᵀ * D * V)⁻¹ * (Uᵀ * B * V)ᵀ =
        Uᵀ * S * U := by
    rw [hBinvTerm]
    dsimp [S]
    noncomm_ring
  have hEE : r.eDiagᵀ * r.eDiag =
      Uᵀ * A * U -
        (Uᵀ * B * V) * (Vᵀ * D * V)⁻¹ * (Uᵀ * B * V)ᵀ :=
    hEGram.trans hSchurRot.symm
  have hFdet : r.fDiag.det ≠ 0 := by
    rw [RawParameters.fDiag, Matrix.det_diagonal]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    exact mul_ne_zero (ne_of_gt hrpos.d₀_pos)
      (mul_ne_zero (ne_of_gt hrpos.e₀_pos) (ne_of_gt hrpos.f₀_pos))
  have hFunit : IsUnit r.fDiag :=
    (Matrix.isUnit_iff_isUnit_det r.fDiag).2 (isUnit_iff_ne_zero.mpr hFdet)
  have hfactor := triangular_factor_cometric
    (Uᵀ * A * U) (Uᵀ * B * V) (Vᵀ * D * V)
    r.eDiag r.mixing r.fDiag hFunit hFF hMF hEE
  let q : InnerAction := (extendSO2 qS, extendSO2 qD)
  refine ⟨q, r, hrpos, ?_⟩
  have hform : K = Matrix.fromBlocks A B Bᵀ D := by
    rw [← Matrix.fromBlocks_toBlocks K]
    congr 1
    simpa [A, B, D] using block21_eq_transpose_block12 hKpos.isHermitian
  rw [hform]
  change (Matrix.fromBlocks U 0 0 V : Mat6)ᵀ *
      Matrix.fromBlocks A B Bᵀ D * Matrix.fromBlocks U 0 0 V =
    r.frameᵀ * r.frame
  rw [block_diagonal_congruence]
  have hBt : (Uᵀ * B * V)ᵀ = Vᵀ * Bᵀ * U := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    noncomm_ring
  rw [← hBt]
  simpa only [RawParameters.frame, Matrix.mul_assoc] using hfactor.symm

theorem standard_fixed_metric_normal_form (g : LeftInvariantMetric)
    (hfix : Fixes diagonalTurn1 g) :
    ∃ q : InnerAction, ∃ p : Parameters, ∃ hp : PositiveParameters p,
      pullbackMetric q g = metricOfPositiveParameters p hp := by
  have hKfix := fixes_cometric hfix
  obtain ⟨q, r, hr, hnormal⟩ :=
    standard_invariant_cometric_normal_form g.posDef.inv hKfix
  let p : Parameters := r.toParameters
  let hp : PositiveParameters p := raw_toParameters_positive hr
  refine ⟨q, p, hp, ?_⟩
  apply LeftInvariantMetric.ext_of_inv_eq
  rw [pullbackMetric_gram_inv]
  change (innerMatrix q)ᵀ * g.gram⁻¹ * innerMatrix q =
    (metricOfFrame p.frame (frame_det_ne_zero_of_positive hp)).gram⁻¹
  rw [metricOfFrame_gram_inv]
  rw [parameters_frame_eq_raw hr]
  exact hnormal

end S3xS3.Z2

open scoped Matrix BigOperators

namespace S3xS3.Z2

open S3xS3.Naturality

def frameVec (V : Mat6) (i : I6) : LieVec := V *ᵥ basisVec i

@[simp] lemma frameVec_apply (V : Mat6) (i j : I6) :
    frameVec V i j = V j i := by
  simp [frameVec, basisVec, Matrix.mulVec, dotProduct]

lemma vec_eq_sum_frame {V D : Mat6} (hVD : V * D = 1) (x : LieVec) :
    x = ∑ i, (D *ᵥ x) i • frameVec V i := by
  have hx : V *ᵥ (D *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hVD]
    simp
  calc
    x = V *ᵥ (D *ᵥ x) := hx.symm
    _ = ∑ i, (D *ᵥ x) i • frameVec V i := by
      funext j
      simp [frameVec, basisVec, Matrix.mulVec, dotProduct, mul_comm]

noncomputable def rawEInv (r : RawParameters) : Mat3 :=
  Matrix.diagonal ![r.a₀⁻¹, r.b₀⁻¹, r.c₀⁻¹]

noncomputable def rawFInv (r : RawParameters) : Mat3 :=
  Matrix.diagonal ![r.d₀⁻¹, r.e₀⁻¹, r.f₀⁻¹]

noncomputable def rawInverseTransposeMix (r : RawParameters) : Mat3 :=
  !![-r.x₀ / (r.a₀ * r.d₀), 0, 0;
     0, -r.y₀ / (r.b₀ * r.e₀), -r.t₀ / (r.b₀ * r.f₀);
     0, -r.w₀ / (r.c₀ * r.e₀), -r.z₀ / (r.c₀ * r.f₀)]

/-- The explicit inverse of the transpose of the raw lower-triangular frame. -/
noncomputable def rawInverseTranspose (r : RawParameters) : Mat6 :=
  Matrix.fromBlocks (rawEInv r) (rawInverseTransposeMix r) 0 (rawFInv r)

lemma raw_inverseTranspose_mul (r : RawParameters) (h : RawPositive r) :
    rawInverseTranspose r * r.frameᵀ = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [rawInverseTranspose, RawParameters.frame,
      rawEInv, rawFInv,
      rawInverseTransposeMix, RawParameters.eDiag,
      RawParameters.fDiag, RawParameters.mixing, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt h.a₀_pos, ne_of_gt h.b₀_pos,
      ne_of_gt h.c₀_pos, ne_of_gt h.d₀_pos, ne_of_gt h.e₀_pos,
      ne_of_gt h.f₀_pos] <;> ring

lemma raw_mul_inverseTranspose (r : RawParameters) (h : RawPositive r) :
    r.frameᵀ * rawInverseTranspose r = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [rawInverseTranspose, RawParameters.frame,
      rawEInv, rawFInv,
      rawInverseTransposeMix, RawParameters.eDiag,
      RawParameters.fDiag, RawParameters.mixing, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt h.a₀_pos, ne_of_gt h.b₀_pos,
      ne_of_gt h.c₀_pos, ne_of_gt h.d₀_pos, ne_of_gt h.e₀_pos,
      ne_of_gt h.f₀_pos] <;> ring

lemma frameMetric_gram_congruence (C : Mat6) (hC : C.det ≠ 0) :
    C * (metricOfFrame C hC).gram * Cᵀ = 1 := by
  have hunitDet : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  have hunitC : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr hunitDet
  have hunitCt : IsUnit Cᵀ := (Matrix.isUnit_transpose C).2 hunitC
  letI : Invertible C := hunitC.invertible
  letI : Invertible Cᵀ := hunitCt.invertible
  rw [metricOfFrame_gram, Matrix.mul_inv_rev]
  simp

lemma frameMetric_orthonormal (C : Mat6) (hC : C.det ≠ 0) (i j : I6) :
    metricInner (metricOfFrame C hC) (frameVec Cᵀ i) (frameVec Cᵀ j) =
      if i = j then 1 else 0 := by
  have hcong := congrArg (fun M : Mat6 ↦ M i j)
    (frameMetric_gram_congruence C hC)
  rw [metricInner]
  have hi : frameVec Cᵀ i = C i := by
    funext k
    simp [frameVec_apply]
  have hj : frameVec Cᵀ j = C j := by
    funext k
    simp [frameVec_apply]
  rw [hi, hj]
  rw [Matrix.mul_mul_apply] at hcong
  simpa [Matrix.one_apply] using hcong

lemma raw_frame_det_ne_zero (r : RawParameters) (h : RawPositive r) :
    r.frame.det ≠ 0 := by
  rw [← parameters_frame_eq_raw h]
  exact frame_det_ne_zero_of_positive (raw_toParameters_positive h)

noncomputable def rawMetric (r : RawParameters) (h : RawPositive r) :
    LeftInvariantMetric := metricOfFrame r.frame (raw_frame_det_ne_zero r h)

noncomputable def rawBracketCoeff (r : RawParameters) (i j k : I6) : ℝ :=
  (rawInverseTranspose r *ᵥ
    bracket (frameVec r.frameᵀ i) (frameVec r.frameᵀ j)) k

noncomputable def metricInnerLeftLinear (g : LeftInvariantMetric) (y : LieVec) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := fun x ↦ metricInner g x y
  map_add' := fun x x' ↦ metricInner_add_left g x x' y
  map_smul' c x := by
    simp only [metricInner_smul_left, RingHom.id_apply, smul_eq_mul]

lemma raw_vec_eq_sum_frame (r : RawParameters) (h : RawPositive r)
    (x : LieVec) :
    x = ∑ i, (rawInverseTranspose r *ᵥ x) i • frameVec r.frameᵀ i :=
  vec_eq_sum_frame (raw_mul_inverseTranspose r h) x

lemma raw_coordinate_eq_metric (r : RawParameters) (h : RawPositive r)
    (x : LieVec) (k : I6) :
    (rawInverseTranspose r *ᵥ x) k =
      metricInner (rawMetric r h) x (frameVec r.frameᵀ k) := by
  conv_rhs => rw [raw_vec_eq_sum_frame r h x]
  change (rawInverseTranspose r *ᵥ x) k =
    metricInnerLeftLinear (rawMetric r h) (frameVec r.frameᵀ k)
      (∑ i, (rawInverseTranspose r *ᵥ x) i • frameVec r.frameᵀ i)
  rw [map_sum]
  simp [metricInnerLeftLinear, rawMetric, frameMetric_orthonormal]

lemma raw_bracket_metric (r : RawParameters) (h : RawPositive r)
    (i j k : I6) :
    metricInner (rawMetric r h)
        (bracket (frameVec r.frameᵀ i) (frameVec r.frameᵀ j))
        (frameVec r.frameᵀ k) = rawBracketCoeff r i j k := by
  rw [← raw_coordinate_eq_metric r h]
  rfl

noncomputable def rawGamma (r : RawParameters) (i j k : I6) : ℝ :=
  (rawBracketCoeff r i j k - rawBracketCoeff r j k i +
    rawBracketCoeff r k i j) / 2

lemma raw_connection_coordinate (r : RawParameters) (h : RawPositive r)
    (i j k : I6) :
    (rawInverseTranspose r *ᵥ
      connectionVec (rawMetric r h) (frameVec r.frameᵀ i)
        (frameVec r.frameᵀ j)) k = rawGamma r i j k := by
  rw [raw_coordinate_eq_metric r h, metricInner_connectionVec]
  rw [koszulForm, raw_bracket_metric r h, raw_bracket_metric r h,
    raw_bracket_metric r h]
  rfl

lemma raw_connection_expansion (r : RawParameters) (h : RawPositive r)
    (i j : I6) :
    connectionVec (rawMetric r h) (frameVec r.frameᵀ i)
        (frameVec r.frameᵀ j) =
      ∑ k, rawGamma r i j k • frameVec r.frameᵀ k := by
  conv_lhs =>
    rw [raw_vec_eq_sum_frame r h
      (connectionVec (rawMetric r h) (frameVec r.frameᵀ i)
        (frameVec r.frameᵀ j))]
  simp only [raw_connection_coordinate]

noncomputable def coordinateLinear (D : Mat6) (n : I6) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := fun x ↦ (D *ᵥ x) n
  map_add' x y := by rw [Matrix.mulVec_add]; rfl
  map_smul' c x := by rw [Matrix.mulVec_smul]; rfl

lemma raw_nested_connection_coordinate (r : RawParameters) (h : RawPositive r)
    (i j k n : I6) :
    (rawInverseTranspose r *ᵥ
      connectionVec (rawMetric r h) (frameVec r.frameᵀ i)
        (connectionVec (rawMetric r h) (frameVec r.frameᵀ j)
          (frameVec r.frameᵀ k))) n =
      ∑ m, rawGamma r j k m * rawGamma r i m n := by
  rw [raw_connection_expansion r h j k]
  change coordinateLinear (rawInverseTranspose r) n
      (connectionRight (rawMetric r h) (frameVec r.frameᵀ i)
        (∑ m, rawGamma r j k m • frameVec r.frameᵀ m)) = _
  rw [map_sum]
  simp only [map_smul]
  change coordinateLinear (rawInverseTranspose r) n
      (∑ m, rawGamma r j k m •
        connectionVec (rawMetric r h) (frameVec r.frameᵀ i)
          (frameVec r.frameᵀ m)) = _
  rw [map_sum]
  simp [coordinateLinear, raw_connection_coordinate]

lemma raw_bracket_expansion (r : RawParameters) (h : RawPositive r)
    (i j : I6) :
    bracket (frameVec r.frameᵀ i) (frameVec r.frameᵀ j) =
      ∑ m, rawBracketCoeff r i j m • frameVec r.frameᵀ m := by
  conv_lhs =>
    rw [raw_vec_eq_sum_frame r h
      (bracket (frameVec r.frameᵀ i) (frameVec r.frameᵀ j))]
  rfl

lemma raw_bracket_connection_coordinate (r : RawParameters) (h : RawPositive r)
    (i j k n : I6) :
    (rawInverseTranspose r *ᵥ
      connectionVec (rawMetric r h)
        (bracket (frameVec r.frameᵀ i) (frameVec r.frameᵀ j))
        (frameVec r.frameᵀ k)) n =
      ∑ m, rawBracketCoeff r i j m * rawGamma r m k n := by
  rw [raw_bracket_expansion r h i j]
  change coordinateLinear (rawInverseTranspose r) n
      (connectionLeft (rawMetric r h) (frameVec r.frameᵀ k)
        (∑ m, rawBracketCoeff r i j m • frameVec r.frameᵀ m)) = _
  rw [map_sum]
  simp only [map_smul]
  change coordinateLinear (rawInverseTranspose r) n
      (∑ m, rawBracketCoeff r i j m •
        connectionVec (rawMetric r h) (frameVec r.frameᵀ m)
          (frameVec r.frameᵀ k)) = _
  rw [map_sum]
  simp [coordinateLinear, raw_connection_coordinate]

noncomputable def rawCurvatureCoeff (r : RawParameters)
    (i j k n : I6) : ℝ :=
  (∑ m, rawGamma r j k m * rawGamma r i m n) -
    (∑ m, rawGamma r i k m * rawGamma r j m n) -
      ∑ m, rawBracketCoeff r i j m * rawGamma r m k n

lemma raw_curvature_coordinate (r : RawParameters) (h : RawPositive r)
    (i j k n : I6) :
    (rawInverseTranspose r *ᵥ
      curvatureVec (rawMetric r h) (frameVec r.frameᵀ i)
        (frameVec r.frameᵀ j) (frameVec r.frameᵀ k)) n =
      rawCurvatureCoeff r i j k n := by
  simp only [curvatureVec, Matrix.mulVec_sub, Pi.sub_apply,
    raw_nested_connection_coordinate, raw_bracket_connection_coordinate,
    rawCurvatureCoeff]

noncomputable def rawRicciCoeff (r : RawParameters) (j k : I6) : ℝ :=
  ∑ i, rawCurvatureCoeff r i j k i

lemma raw_ricciForm_eq (r : RawParameters) (h : RawPositive r) (j k : I6) :
    ricciForm (rawMetric r h) (frameVec r.frameᵀ j) (frameVec r.frameᵀ k) =
      rawRicciCoeff r j k := by
  let V : Mat6 := r.frameᵀ
  let D : Mat6 := rawInverseTranspose r
  let M : Mat6 := curvatureEndomorphism (rawMetric r h)
    (frameVec V j) (frameVec V k)
  have hVD : V * D = 1 := raw_mul_inverseTranspose r h
  have htrace : Matrix.trace M = Matrix.trace (D * M * V) := by
    symm
    rw [Matrix.trace_mul_cycle, hVD]
    simp
  rw [ricciForm]
  change Matrix.trace M = rawRicciCoeff r j k
  rw [htrace]
  simp only [Matrix.trace, rawRicciCoeff]
  apply Finset.sum_congr rfl
  intro i _
  change (D * M * V) i i = rawCurvatureCoeff r i j k i
  rw [Matrix.mul_mul_apply]
  have hcol : Vᵀ i = frameVec V i := by
    funext n
    simp [frameVec_apply]
  rw [hcol, curvatureEndomorphism_mulVec]
  change (D *ᵥ curvatureVec (rawMetric r h) (frameVec V i)
    (frameVec V j) (frameVec V k)) i = rawCurvatureCoeff r i j k i
  exact raw_curvature_coordinate r h i j k i

lemma rawRicciCoeff_of_Einstein (r : RawParameters) (h : RawPositive r)
    {einsteinConstant : ℝ}
    (hEin : ricci (rawMetric r h) =
      einsteinConstant • (rawMetric r h).gram) (j k : I6) :
  rawRicciCoeff r j k = if j = k then einsteinConstant else 0 := by
  rw [← raw_ricciForm_eq r h, ricciForm_eq_matrix, hEin]
  rw [Matrix.smul_mulVec, dotProduct_smul]
  change einsteinConstant *
    metricInner (rawMetric r h) (frameVec r.frameᵀ j)
      (frameVec r.frameᵀ k) = _
  simp [rawMetric, frameMetric_orthonormal]

set_option maxHeartbeats 800000 in
lemma raw_pairYZ1_certificate (r : RawParameters) (h : RawPositive r) :
    2 * rawRicciCoeff r (Sum.inr 1) (Sum.inl 1) =
      -(r.toParameters.r1 * r.toParameters.y -
        r.toParameters.u * r.toParameters.z) := by
  simp [rawRicciCoeff, rawCurvatureCoeff, rawGamma, rawBracketCoeff,
    rawInverseTranspose, rawEInv, rawFInv, rawInverseTransposeMix,
    RawParameters.frame, RawParameters.eDiag, RawParameters.fDiag,
    RawParameters.mixing, frameVec, basisVec, bracket, cross_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Parameters.r1, Parameters.u, Parameters.Pi, Parameters.delta,
    RawParameters.toParameters]
  field_simp [ne_of_gt h.a₀_pos, ne_of_gt h.b₀_pos,
    ne_of_gt h.c₀_pos, ne_of_gt h.d₀_pos, ne_of_gt h.e₀_pos,
    ne_of_gt h.f₀_pos]
  ring

set_option maxHeartbeats 800000 in
lemma raw_pairYZ2_certificate (r : RawParameters) (h : RawPositive r) :
    2 * rawRicciCoeff r (Sum.inr 2) (Sum.inl 2) =
      -(r.toParameters.s1 * r.toParameters.z -
        r.toParameters.u * r.toParameters.y) := by
  simp [rawRicciCoeff, rawCurvatureCoeff, rawGamma, rawBracketCoeff,
    rawInverseTranspose, rawEInv, rawFInv, rawInverseTransposeMix,
    RawParameters.frame, RawParameters.eDiag, RawParameters.fDiag,
    RawParameters.mixing, frameVec, basisVec, bracket, cross_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Parameters.s1, Parameters.u, Parameters.Pi, Parameters.delta,
    RawParameters.toParameters]
  field_simp [ne_of_gt h.a₀_pos, ne_of_gt h.b₀_pos,
    ne_of_gt h.c₀_pos, ne_of_gt h.d₀_pos, ne_of_gt h.e₀_pos,
    ne_of_gt h.f₀_pos]
  ring

set_option maxHeartbeats 800000 in
lemma raw_pairWT1_certificate (r : RawParameters) (h : RawPositive r) :
    2 * rawRicciCoeff r (Sum.inr 1) (Sum.inl 2) =
      -(r.toParameters.r2 * r.toParameters.w -
        r.toParameters.v * r.toParameters.t) := by
  simp [rawRicciCoeff, rawCurvatureCoeff, rawGamma, rawBracketCoeff,
    rawInverseTranspose, rawEInv, rawFInv, rawInverseTransposeMix,
    RawParameters.frame, RawParameters.eDiag, RawParameters.fDiag,
    RawParameters.mixing, frameVec, basisVec, bracket, cross_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Parameters.r2, Parameters.v, Parameters.Omega, Parameters.delta,
    RawParameters.toParameters]
  field_simp [ne_of_gt h.a₀_pos, ne_of_gt h.b₀_pos,
    ne_of_gt h.c₀_pos, ne_of_gt h.d₀_pos, ne_of_gt h.e₀_pos,
    ne_of_gt h.f₀_pos]
  ring

set_option maxHeartbeats 800000 in
lemma raw_pairWT2_certificate (r : RawParameters) (h : RawPositive r) :
    2 * rawRicciCoeff r (Sum.inr 2) (Sum.inl 1) =
      -(r.toParameters.s2 * r.toParameters.t -
        r.toParameters.v * r.toParameters.w) := by
  simp [rawRicciCoeff, rawCurvatureCoeff, rawGamma, rawBracketCoeff,
    rawInverseTranspose, rawEInv, rawFInv, rawInverseTransposeMix,
    RawParameters.frame, RawParameters.eDiag, RawParameters.fDiag,
    RawParameters.mixing, frameVec, basisVec, bracket, cross_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Parameters.s2, Parameters.v, Parameters.Omega, Parameters.delta,
    RawParameters.toParameters]
  field_simp [ne_of_gt h.a₀_pos, ne_of_gt h.b₀_pos,
    ne_of_gt h.c₀_pos, ne_of_gt h.d₀_pos, ne_of_gt h.e₀_pos,
    ne_of_gt h.f₀_pos]
  ring

set_option maxHeartbeats 800000 in
lemma raw_xEquation_certificate (r : RawParameters) (h : RawPositive r) :
    2 * rawRicciCoeff r (Sum.inr 0) (Sum.inl 0) =
      -(r.toParameters.x * r.toParameters.H -
        (r.toParameters.Pi * (r.toParameters.y * r.toParameters.z) -
          r.toParameters.Omega * (r.toParameters.w * r.toParameters.t))) := by
  simp [rawRicciCoeff, rawCurvatureCoeff, rawGamma, rawBracketCoeff,
    rawInverseTranspose, rawEInv, rawFInv, rawInverseTransposeMix,
    RawParameters.frame, RawParameters.eDiag, RawParameters.fDiag,
    RawParameters.mixing, frameVec, basisVec, bracket, cross_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Parameters.H, Parameters.Pi, Parameters.Omega,
    RawParameters.toParameters]
  field_simp [ne_of_gt h.a₀_pos, ne_of_gt h.b₀_pos,
    ne_of_gt h.c₀_pos, ne_of_gt h.d₀_pos, ne_of_gt h.e₀_pos,
    ne_of_gt h.f₀_pos]
  ring

set_option maxHeartbeats 1200000 in
lemma raw_diagonalDifference_certificate (r : RawParameters) (h : RawPositive r) :
    r.toParameters.diagonalDifference =
      rawRicciCoeff r (Sum.inl 2) (Sum.inl 2) -
        rawRicciCoeff r (Sum.inl 1) (Sum.inl 1) +
        r.toParameters.w * rawRicciCoeff r (Sum.inr 1) (Sum.inl 2) +
        r.toParameters.z * rawRicciCoeff r (Sum.inr 2) (Sum.inl 2) -
        r.toParameters.y * rawRicciCoeff r (Sum.inr 1) (Sum.inl 1) -
        r.toParameters.t * rawRicciCoeff r (Sum.inr 2) (Sum.inl 1) := by
  simp [rawRicciCoeff, rawCurvatureCoeff, rawGamma, rawBracketCoeff,
    rawInverseTranspose, rawEInv, rawFInv, rawInverseTransposeMix,
    RawParameters.frame, RawParameters.eDiag, RawParameters.fDiag,
    RawParameters.mixing, frameVec, basisVec, bracket, cross_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Parameters.diagonalDifference, RawParameters.toParameters]
  field_simp [ne_of_gt h.a₀_pos, ne_of_gt h.b₀_pos,
    ne_of_gt h.c₀_pos, ne_of_gt h.d₀_pos, ne_of_gt h.e₀_pos,
    ne_of_gt h.f₀_pos]
  ring

set_option maxHeartbeats 1200000 in
lemma raw_scalarD_certificate (r : RawParameters) (h : RawPositive r) :
    r.toParameters.d * r.toParameters.scalarD =
      rawRicciCoeff r (Sum.inr 1) (Sum.inr 1) +
        rawRicciCoeff r (Sum.inr 2) (Sum.inr 2) -
        r.toParameters.y * rawRicciCoeff r (Sum.inr 1) (Sum.inl 1) -
        r.toParameters.w * rawRicciCoeff r (Sum.inr 1) (Sum.inl 2) -
        r.toParameters.t * rawRicciCoeff r (Sum.inr 2) (Sum.inl 1) -
        r.toParameters.z * rawRicciCoeff r (Sum.inr 2) (Sum.inl 2) := by
  simp [rawRicciCoeff, rawCurvatureCoeff, rawGamma, rawBracketCoeff,
    rawInverseTranspose, rawEInv, rawFInv, rawInverseTransposeMix,
    RawParameters.frame, RawParameters.eDiag, RawParameters.fDiag,
    RawParameters.mixing, frameVec, basisVec, bracket, cross_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Parameters.scalarD, Parameters.delta, RawParameters.toParameters]
  field_simp [ne_of_gt h.a₀_pos, ne_of_gt h.b₀_pos,
    ne_of_gt h.c₀_pos, ne_of_gt h.d₀_pos, ne_of_gt h.e₀_pos,
    ne_of_gt h.f₀_pos]
  ring

lemma rawMetric_eq_metricOfPositiveParameters (r : RawParameters)
    (h : RawPositive r) :
    rawMetric r h =
      metricOfPositiveParameters r.toParameters (raw_toParameters_positive h) := by
  apply LeftInvariantMetric.ext
  simp only [rawMetric, metricOfPositiveParameters, metricOfFrame_gram]
  rw [parameters_frame_eq_raw h]

theorem raw_einstein_criticalPoint (r : RawParameters) (h : RawPositive r)
    {einsteinConstant : ℝ}
    (hEin : ricci (rawMetric r h) =
      einsteinConstant • (rawMetric r h).gram)
    (hConstant : 0 < einsteinConstant) : CriticalPoint r.toParameters := by
  let p := r.toParameters
  have hp : PositiveParameters p := raw_toParameters_positive h
  have h41 : rawRicciCoeff r (Sum.inr 1) (Sum.inl 1) = 0 := by
    simpa using rawRicciCoeff_of_Einstein r h hEin (Sum.inr 1) (Sum.inl 1)
  have h52 : rawRicciCoeff r (Sum.inr 2) (Sum.inl 2) = 0 := by
    simpa using rawRicciCoeff_of_Einstein r h hEin (Sum.inr 2) (Sum.inl 2)
  have h42 : rawRicciCoeff r (Sum.inr 1) (Sum.inl 2) = 0 := by
    simpa using rawRicciCoeff_of_Einstein r h hEin (Sum.inr 1) (Sum.inl 2)
  have h51 : rawRicciCoeff r (Sum.inr 2) (Sum.inl 1) = 0 := by
    simpa using rawRicciCoeff_of_Einstein r h hEin (Sum.inr 2) (Sum.inl 1)
  have h30 : rawRicciCoeff r (Sum.inr 0) (Sum.inl 0) = 0 := by
    simpa using rawRicciCoeff_of_Einstein r h hEin (Sum.inr 0) (Sum.inl 0)
  have h11 : rawRicciCoeff r (Sum.inl 1) (Sum.inl 1) = einsteinConstant := by
    simpa using rawRicciCoeff_of_Einstein r h hEin (Sum.inl 1) (Sum.inl 1)
  have h22 : rawRicciCoeff r (Sum.inl 2) (Sum.inl 2) = einsteinConstant := by
    simpa using rawRicciCoeff_of_Einstein r h hEin (Sum.inl 2) (Sum.inl 2)
  have h44 : rawRicciCoeff r (Sum.inr 1) (Sum.inr 1) = einsteinConstant := by
    simpa using rawRicciCoeff_of_Einstein r h hEin (Sum.inr 1) (Sum.inr 1)
  have h55 : rawRicciCoeff r (Sum.inr 2) (Sum.inr 2) = einsteinConstant := by
    simpa using rawRicciCoeff_of_Einstein r h hEin (Sum.inr 2) (Sum.inr 2)
  have hyz1 := raw_pairYZ1_certificate r h
  have hyz2 := raw_pairYZ2_certificate r h
  have hwt1 := raw_pairWT1_certificate r h
  have hwt2 := raw_pairWT2_certificate r h
  have hx := raw_xEquation_certificate r h
  have hdiag := raw_diagonalDifference_certificate r h
  have hsd := raw_scalarD_certificate r h
  rw [h41] at hyz1
  rw [h52] at hyz2
  rw [h42] at hwt1
  rw [h51] at hwt2
  rw [h30] at hx
  rw [h22, h11, h42, h52, h41, h51] at hdiag
  rw [h44, h55, h41, h42, h51, h52] at hsd
  ring_nf at hdiag hsd
  refine
    { toPositiveParameters := hp
      pairYZ₁ := by change p.r1 * p.y = p.u * p.z; dsimp [p]; linarith [hyz1]
      pairYZ₂ := by change p.s1 * p.z = p.u * p.y; dsimp [p]; linarith [hyz2]
      pairWT₁ := by change p.r2 * p.w = p.v * p.t; dsimp [p]; linarith [hwt1]
      pairWT₂ := by change p.s2 * p.t = p.v * p.w; dsimp [p]; linarith [hwt2]
      xEquation := by
        change p.x * p.H = p.Pi * (p.y * p.z) - p.Omega * (p.w * p.t)
        dsimp [p]
        linarith [hx]
      diagonalBC := by simpa [p] using hdiag
      scalarD_pos := by
        change 0 < p.scalarD
        have hd : 0 < p.d := hp.d_pos
        change p.d * p.scalarD = einsteinConstant * 2 at hsd
        nlinarith }

noncomputable def rawKillingDerivativeCoeff (r : RawParameters)
    (i a k : I6) : ℝ :=
  ∑ j, rawInverseTranspose r j a *
    (rawGamma r i j k + rawBracketCoeff r j i k)

noncomputable def rawKillingEnergy (r : RawParameters) : ℝ :=
  ∑ i, ∑ a, ∑ k, rawKillingDerivativeCoeff r i a k ^ 2

noncomputable def rawBackgroundRicciTrace (r : RawParameters) : ℝ :=
  ∑ a, ∑ j, ∑ k,
    rawInverseTranspose r j a * rawInverseTranspose r k a *
      rawRicciCoeff r j k

set_option maxHeartbeats 6000000 in
lemma raw_bochner_certificate (r : RawParameters) (h : RawPositive r) :
    rawBackgroundRicciTrace r = rawKillingEnergy r := by
  simp [rawBackgroundRicciTrace, rawKillingEnergy,
    rawKillingDerivativeCoeff, rawRicciCoeff, rawCurvatureCoeff,
    rawGamma, rawBracketCoeff, rawInverseTranspose, rawEInv, rawFInv,
    rawInverseTransposeMix, RawParameters.frame, RawParameters.eDiag,
    RawParameters.fDiag, RawParameters.mixing, frameVec, basisVec,
    bracket, cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  field_simp [ne_of_gt h.a₀_pos, ne_of_gt h.b₀_pos,
    ne_of_gt h.c₀_pos, ne_of_gt h.d₀_pos, ne_of_gt h.e₀_pos,
    ne_of_gt h.f₀_pos]
  ring

lemma rawBracketCoeff_swap (r : RawParameters) (i j k : I6) :
    rawBracketCoeff r j i k = -rawBracketCoeff r i j k := by
  simp [rawBracketCoeff, rawInverseTranspose, rawEInv, rawFInv,
    rawInverseTransposeMix, RawParameters.frame, RawParameters.eDiag,
    RawParameters.fDiag, RawParameters.mixing, frameVec, basisVec,
    bracket, cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

lemma rawGamma_torsion (r : RawParameters) (i j k : I6) :
    rawGamma r i j k - rawGamma r j i k = rawBracketCoeff r i j k := by
  rw [rawGamma, rawGamma]
  rw [rawBracketCoeff_swap r j i k, rawBracketCoeff_swap r k j i,
    rawBracketCoeff_swap r i k j]
  ring

lemma rawBracketCoeff_012_pos (r : RawParameters) (h : RawPositive r) :
    0 < rawBracketCoeff r (Sum.inl 0) (Sum.inl 1) (Sum.inl 2) := by
  simp [rawBracketCoeff, rawInverseTranspose, rawEInv, rawFInv,
    rawInverseTransposeMix, RawParameters.frame, RawParameters.eDiag,
    RawParameters.fDiag, RawParameters.mixing, frameVec, basisVec,
    bracket, cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simpa [div_eq_inv_mul, mul_comm] using
    (div_pos (mul_pos h.a₀_pos h.b₀_pos) h.c₀_pos)

lemma rawKillingEnergy_nonneg (r : RawParameters) : 0 ≤ rawKillingEnergy r := by
  simp only [rawKillingEnergy]
  positivity

lemma rawKillingEnergy_pos (r : RawParameters) (h : RawPositive r) :
    0 < rawKillingEnergy r := by
  have hnonneg := rawKillingEnergy_nonneg r
  apply lt_of_le_of_ne hnonneg
  intro hzero'
  have hzero : rawKillingEnergy r = 0 := hzero'.symm
  have houter :
      (fun i : I6 ↦ ∑ a, ∑ k, rawKillingDerivativeCoeff r i a k ^ 2) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg (fun i ↦ by positivity)).mp hzero
  have hall : ∀ i a k : I6, rawKillingDerivativeCoeff r i a k = 0 := by
    intro i a k
    have hi : ∑ a, ∑ k, rawKillingDerivativeCoeff r i a k ^ 2 = 0 :=
      congrFun houter i
    have hmiddle :
        (fun a : I6 ↦ ∑ k, rawKillingDerivativeCoeff r i a k ^ 2) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (fun a ↦ by positivity)).mp hi
    have ha : ∑ k, rawKillingDerivativeCoeff r i a k ^ 2 = 0 :=
      congrFun hmiddle a
    have hinner :
        (fun k : I6 ↦ rawKillingDerivativeCoeff r i a k ^ 2) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (fun k ↦ sq_nonneg _)).mp ha
    have hk := congrFun hinner k
    simp only [Pi.zero_apply, sq_eq_zero_iff] at hk
    exact hk
  have hKzero : ∀ i j k : I6,
      rawGamma r i j k + rawBracketCoeff r j i k = 0 := by
    intro i j k
    let K : LieVec := fun l ↦ rawGamma r i l k + rawBracketCoeff r l i k
    have hDK : (rawInverseTranspose r)ᵀ *ᵥ K = 0 := by
      funext a
      simpa [K, rawKillingDerivativeCoeff, Matrix.mulVec, dotProduct] using
        hall i a k
    have hDt : r.frame * (rawInverseTranspose r)ᵀ = 1 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_one] using
        congrArg Matrix.transpose (raw_inverseTranspose_mul r h)
    have hh := congrArg (fun v : LieVec ↦ r.frame *ᵥ v) hDK
    simp only [Matrix.mulVec_mulVec, hDt, Matrix.one_mulVec,
      Matrix.mulVec_zero] at hh
    exact congrFun hh j
  let i : I6 := Sum.inl 0
  let j : I6 := Sum.inl 1
  let k : I6 := Sum.inl 2
  have hij := hKzero i j k
  have hji := hKzero j i k
  have hswap := rawBracketCoeff_swap r i j k
  have htorsion := rawGamma_torsion r i j k
  have hpos := rawBracketCoeff_012_pos r h
  change 0 < rawBracketCoeff r i j k at hpos
  linarith

noncomputable def rawBackgroundNorm (r : RawParameters) : ℝ :=
  ∑ a, ∑ j, rawInverseTranspose r j a ^ 2

lemma rawBackgroundNorm_pos (r : RawParameters) (h : RawPositive r) :
    0 < rawBackgroundNorm r := by
  let a : I6 := Sum.inr 0
  let j : I6 := Sum.inr 0
  have hentry : rawInverseTranspose r j a = r.d₀⁻¹ := by
    simp [a, j, rawInverseTranspose, rawFInv]
  have hterm : 0 < rawInverseTranspose r j a ^ 2 := by
    rw [hentry]
    exact sq_pos_of_ne_zero (inv_ne_zero (ne_of_gt h.d₀_pos))
  have hinner : rawInverseTranspose r j a ^ 2 ≤
      ∑ q, rawInverseTranspose r q a ^ 2 := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun q ↦ rawInverseTranspose r q a ^ 2)
      (fun q _ ↦ sq_nonneg _) (Finset.mem_univ j)
  have houter : (∑ q, rawInverseTranspose r q a ^ 2) ≤
      rawBackgroundNorm r := by
    rw [rawBackgroundNorm]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun q ↦ ∑ z, rawInverseTranspose r z q ^ 2)
      (fun q _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
      (Finset.mem_univ a)
  exact lt_of_lt_of_le hterm (hinner.trans houter)

lemma rawBackgroundRicciTrace_of_Einstein (r : RawParameters)
    (h : RawPositive r) {einsteinConstant : ℝ}
    (hEin : ricci (rawMetric r h) =
      einsteinConstant • (rawMetric r h).gram) :
    rawBackgroundRicciTrace r =
      einsteinConstant * rawBackgroundNorm r := by
  simp only [rawBackgroundRicciTrace, rawBackgroundNorm]
  simp_rw [rawRicciCoeff_of_Einstein r h hEin]
  simp
  simp [Fin.sum_univ_succ]
  ring

theorem raw_einsteinConstant_pos (r : RawParameters) (h : RawPositive r)
    {einsteinConstant : ℝ}
    (hEin : ricci (rawMetric r h) =
      einsteinConstant • (rawMetric r h).gram) :
    0 < einsteinConstant := by
  have henergy : 0 < rawKillingEnergy r := rawKillingEnergy_pos r h
  have hbochner := raw_bochner_certificate r h
  have htrace := rawBackgroundRicciTrace_of_Einstein r h hEin
  have hproduct : 0 < einsteinConstant * rawBackgroundNorm r := by
    rw [← htrace, hbochner]
    exact henergy
  have hnorm : 0 < rawBackgroundNorm r := rawBackgroundNorm_pos r h
  nlinarith

noncomputable def pullbackIsotropyEquiv (a : InnerAction)
    (g : LeftInvariantMetric) :
    innerIsotropy (pullbackMetric a g) ≃* innerIsotropy g where
  toFun b := ⟨a * b.1 * a⁻¹,
    (fixes_conjugate_iff a b.1 g).2 b.2⟩
  invFun c := ⟨a⁻¹ * c.1 * a, by
    apply (fixes_conjugate_iff a (a⁻¹ * c.1 * a) g).1
    have hc : Fixes c.1 g := c.2
    have heq : a * (a⁻¹ * c.1 * a) * a⁻¹ = c.1 := by group
    rw [heq]
    exact hc⟩
  left_inv b := by
    apply Subtype.ext
    change a⁻¹ * (a * b.1 * a⁻¹) * a = b.1
    group
  right_inv c := by
    apply Subtype.ext
    change a * (a⁻¹ * c.1 * a) * a⁻¹ = c.1
    group
  map_mul' b c := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem containsKleinFour_of_pullback {g : LeftInvariantMetric}
    (a : InnerAction) (hK : ContainsKleinFour (pullbackMetric a g)) :
    ContainsKleinFour g := by
  obtain ⟨H, hH⟩ := hK
  let e := pullbackIsotropyEquiv a g
  let H' : Subgroup (innerIsotropy g) := H.map (e : _ →* _)
  let eH : H ≃* H' := e.subgroupMap H
  letI : IsKleinFour H' := {
    card_four := by
      calc
        Nat.card H' = Nat.card H := (Nat.card_congr eH.toEquiv).symm
        _ = 4 := hH.card_four
    exponent_two := by
      calc
        Monoid.exponent H' = Monoid.exponent H :=
          (Monoid.exponent_eq_of_mulEquiv eH).symm
        _ = 2 := hH.exponent_two
  }
  exact ⟨H', inferInstance⟩

theorem standard_fixed_metric_raw_normal_form (g : LeftInvariantMetric)
    (hfix : Fixes diagonalTurn1 g) :
    ∃ q : InnerAction, ∃ r : RawParameters, ∃ hr : RawPositive r,
      pullbackMetric q g = rawMetric r hr := by
  have hKfix := fixes_cometric hfix
  obtain ⟨q, r, hr, hnormal⟩ :=
    standard_invariant_cometric_normal_form g.posDef.inv hKfix
  refine ⟨q, r, hr, ?_⟩
  apply LeftInvariantMetric.ext_of_inv_eq
  rw [pullbackMetric_gram_inv]
  change (innerMatrix q)ᵀ * g.gram⁻¹ * innerMatrix q =
    (metricOfFrame r.frame (raw_frame_det_ne_zero r hr)).gram⁻¹
  rw [metricOfFrame_gram_inv]
  exact hnormal

lemma metricOfParameters_eq_rawMetric (r : RawParameters) (h : RawPositive r)
    (hc : CriticalPoint r.toParameters) :
    metricOfParameters r.toParameters hc = rawMetric r h := by
  apply LeftInvariantMetric.ext
  simp only [metricOfParameters, metricOfPositiveParameters, rawMetric,
    metricOfFrame_gram]
  rw [parameters_frame_eq_raw h]

theorem standard_fixed_einstein_containsKleinFour (g : LeftInvariantMetric)
    (hEinstein : Einstein g) (hfix : Fixes diagonalTurn1 g) :
    ContainsKleinFour g := by
  obtain ⟨q, r, hr, hnormal⟩ := standard_fixed_metric_raw_normal_form g hfix
  have hEinPull : Einstein (pullbackMetric q g) :=
    S3xS3.Naturality.Einstein.pullback hEinstein q
  rw [hnormal] at hEinPull
  obtain ⟨einsteinConstant, hEin⟩ := hEinPull
  have hConstant : 0 < einsteinConstant :=
    raw_einsteinConstant_pos r hr hEin
  have hc : CriticalPoint r.toParameters :=
    raw_einstein_criticalPoint r hr hEin hConstant
  have hKraw : ContainsKleinFour (rawMetric r hr) := by
    rw [← metricOfParameters_eq_rawMetric r hr hc]
    exact criticalPoint_containsKleinFour hc
  have hKpull : ContainsKleinFour (pullbackMetric q g) := by
    rw [hnormal]
    exact hKraw
  exact containsKleinFour_of_pullback q hKpull

/-- End-to-end trace `-2` symmetry enhancement, from the genuine Ricci
equation and an arbitrary inner involution to a Klein four subgroup. -/
theorem einstein_involution_trace_neg_two_containsKleinFour
    (g : LeftInvariantMetric) (sigma : InnerAction)
    (hEinstein : Einstein g) (hfix : Fixes sigma g)
    (hsquare : sigma * sigma = 1) (_hne : sigma ≠ 1)
    (htrace : innerTrace sigma = -2) : ContainsKleinFour g := by
  obtain ⟨q, hq⟩ := standardize_trace_neg_two_involution sigma hsquare htrace
  have hsigma : q * diagonalTurn1 * q⁻¹ = sigma := by
    rw [← hq]
    group
  have hfixStandard : Fixes diagonalTurn1 (pullbackMetric q g) := by
    apply (fixes_conjugate_iff q diagonalTurn1 g).1
    rw [hsigma]
    exact hfix
  have hEinStandard : Einstein (pullbackMetric q g) :=
    S3xS3.Naturality.Einstein.pullback hEinstein q
  have hKStandard : ContainsKleinFour (pullbackMetric q g) :=
    standard_fixed_einstein_containsKleinFour (pullbackMetric q g)
      hEinStandard hfixStandard
  exact containsKleinFour_of_pullback q hKStandard

end S3xS3.Z2

namespace S3xS3.Geometry

open MatrixGroupLeftInvariantMetric

noncomputable section

/-- Trace of the differential of a literal inner automorphism on the actual
six-dimensional Lie algebra. -/
def actualInnerTrace (sigma : MatrixS3xS3InnerAutomorphismGroup) : ℝ :=
  (LinearMap.toMatrix actualLieBasis actualLieBasis
    (innerAutomorphismDerivative sigma)).trace

theorem actualInnerTrace_eq_coordinate
    (sigma : MatrixS3xS3InnerAutomorphismGroup) :
    actualInnerTrace sigma =
      S3xS3.Z2.innerTrace
        (matrixS3xS3InnerAutomorphismEquivInnerAction sigma) := by
  rw [actualInnerTrace, innerAutomorphismDerivative_toMatrix]
  rfl

/-- **Theorem 1.2 (trace `-2` symmetry enhancement), on the concrete matrix
group.**

For a left-invariant Einstein metric on Mathlib's matrix
`SU(2) × SU(2)`, a nonidentity inner involution of trace `-2` forces the
literal inner-isotropy group to contain a Klein four subgroup. -/
theorem theorem_1_2_trace_neg_two_symmetry_enhancement
    (g : MatrixGroupLeftInvariantMetric)
    (sigma : MatrixS3xS3InnerAutomorphismGroup)
    (hEinstein : g.Einstein)
    (hisometry : IsInnerIsometry sigma g)
    (hsquare : sigma * sigma = 1)
    (hne : sigma ≠ 1)
    (htrace : actualInnerTrace sigma = -2) :
    g.ContainsKleinFour := by
  let a : InnerAction :=
    matrixS3xS3InnerAutomorphismEquivInnerAction sigma
  have hCoordinateEinstein : S3xS3.Einstein g.toCoordinateMetric :=
    (g.einstein_iff_coordinate).mp hEinstein
  have hCoordinateFix : S3xS3.Fixes a g.toCoordinateMetric := by
    have hfix : MatrixGroupLeftInvariantMetric.Fixes sigma g :=
      (isInnerIsometry_iff_fixes sigma g).mp hisometry
    exact (fixes_iff_coordinate sigma g).mp hfix
  have hCoordinateSquare : a * a = 1 := by
    have h := congrArg matrixS3xS3InnerAutomorphismEquivInnerAction hsquare
    simpa [a] using h
  have hCoordinateNe : a ≠ 1 := by
    intro ha
    apply hne
    apply matrixS3xS3InnerAutomorphismEquivInnerAction.injective
    simpa [a] using ha
  have hCoordinateTrace : S3xS3.Z2.innerTrace a = -2 := by
    rw [← actualInnerTrace_eq_coordinate sigma]
    exact htrace
  have hCoordinateKlein :
      S3xS3.ContainsKleinFour g.toCoordinateMetric :=
    S3xS3.Z2.einstein_involution_trace_neg_two_containsKleinFour
      g.toCoordinateMetric a hCoordinateEinstein hCoordinateFix
      hCoordinateSquare hCoordinateNe hCoordinateTrace
  exact g.containsKleinFour_of_coordinate hCoordinateKlein

end

end S3xS3.Geometry
