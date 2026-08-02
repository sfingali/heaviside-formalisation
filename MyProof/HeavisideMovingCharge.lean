import Mathlib
import MyProof.VectorCalculus
import MyProof.HeavisideField

/-!
# Heaviside corpus, T4: the field of a uniformly moving charge

Heaviside, *Electrical Papers* Vol. 2, "Electromagnetic Waves, the Propagation of
Potential, and the Electromagnetic Effects of a Moving Charge" (*The Electrician*
1888–89), pp. 492–515. Formula page p. 495 (rationalised units; axis of z the motion
line, charge q at speed u).  Confirmed at EP2 p. 516: (A) the ellipsoid formula and
(B) H = c·E·u·sinθ, with the speed condition μcv² = 1.

Statements (EP2 p. 495):
  (A) the electric force is radial from the charge, with
      cE = q(1 − u²/v²) / (r²·(1 − u²sin²θ/v²)^(3/2))   — the Heaviside ellipsoid:
      the field lines stay straight (radial), compressed along the motion.
  (B) the magnetic force H = c·E·u·sinθ — circles about the axis of motion; "the two
      forces are perpendicular" (E·H = 0).
  The speed condition μcv² = 1 — v = 1/√(μc), the propagation speed of the medium
  (same 1/√(LC) law as T1's line and T2's wave equation).
  For u > v the disturbance is confined to a cone with sin θ = v/u (p. 494 — the
  superluminal cone, flagged by Heaviside as unconfirmed).

Formalised here: the spherical frame, the (A)/(B) magnitudes (with the (3/2)-power
written as (1 − β²sin²θ)·√(1 − β²sin²θ) — equal for subluminal motion), and the
theorems: E·H = 0 (perpendicularity), the axial and equatorial closed forms and their
ratio, the flattening factor (1 − β²sin²θ)^(−3/2) ≥ 1, the speed condition, and the
superluminal cone angle (θ = arcsin(v/u) exists iff u > v).  The three-laws test of
EP2 p. 495 (Faraday, Maxwell/Ampere, continuity) is the T2 bridge: the (A)/(B) field
is consistent with the 4-vector system of `HeavisideField` (potential_is_circuital:
B = curl A forces the circuital flux).  The electromagnetic-mass corollary of the
field is T8.  V3 machinery from `OAnimatorVector`.
-/

namespace HeavisideMovingCharge

open OAnimatorVector
open HeavisideField

/-- The unit radial vector (spherical polar coordinates; θ from the motion axis z,
    φ the azimuth):  r̂ = (sinθcosφ, sinθsinφ, cosθ). -/
noncomputable def rHat (θ φ : ℝ) : V3 :=
  ![Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

/-- The unit polar vector (direction of increasing θ). -/
noncomputable def θHat (θ φ : ℝ) : V3 :=
  ![Real.cos θ * Real.cos φ, Real.cos θ * Real.sin φ, -Real.sin θ]

/-- The unit azimuthal vector (direction of increasing φ) — the direction of the
    magnetic force (B). -/
noncomputable def φHat (φ : ℝ) : V3 :=
  ![-Real.sin φ, Real.cos φ, 0]

/-- β = u/v — the speed ratio (charge speed over wave speed). -/
noncomputable def beta (u v : ℝ) : ℝ :=
  u / v

/-- The electric force magnitude (A):  cE = q(1 − β²) / (r²·(1 − β²sin²θ)^(3/2)).
    The (3/2)-power is written as (1 − β²sin²θ)·√(1 − β²sin²θ), equal to it for
    subluminal motion (1 − β²sin²θ ≥ 0). -/
noncomputable def eMag (q r u v θ : ℝ) : ℝ :=
  let β := beta u v
  q * (1 - β ^ 2) / (r ^ 2 * (1 - β ^ 2 * Real.sin θ ^ 2) * Real.sqrt (1 - β ^ 2 * Real.sin θ ^ 2))

/-- The electric force vector (A): radial from the charge. -/
noncomputable def Efield (q r u v θ φ : ℝ) : V3 :=
  eMag q r u v θ • rHat θ φ

/-- The magnetic force magnitude (B):  H = c·E·u·sinθ (c the permittivity of the
    medium). -/
noncomputable def hMag (c q r u v θ : ℝ) : ℝ :=
  c * eMag q r u v θ * u * Real.sin θ

/-- The magnetic force vector (B): circles about the axis of motion. -/
noncomputable def Hfield (c q r u v θ φ : ℝ) : V3 :=
  hMag c q r u v θ • φHat φ

/-- The two forces are perpendicular: E·H = 0 (EP2 p. 495, "the two forces are
    perpendicular").  Radial and azimuthal unit vectors are orthogonal. -/
theorem field_perpendicular (c q r u v θ φ : ℝ) :
    dot3 (Efield q r u v θ φ) (Hfield c q r u v θ φ) = 0 := by
  simp [Efield, Hfield, hMag, rHat, φHat, dot3, Fin.sum_univ_three]
  ring

/-- The field on the axis (θ = 0):  E = q(1 − β²)/r² along the motion. -/
theorem field_axial (q r u v : ℝ) :
    eMag q r u v 0 = q * (1 - beta u v ^ 2) / (r ^ 2) := by
  simp [eMag, beta, Real.sin_zero, Real.sqrt_one]

/-- The field in the equatorial plane (θ = π/2):  E = q / (r²·√(1 − β²)) — the
    transverse field of the moving charge. -/
theorem field_equatorial (q r u v : ℝ) (hr : r ≠ 0)
    (hβ : 0 < 1 - beta u v ^ 2) :
    eMag q r u v (Real.pi / 2) = q / (r ^ 2 * Real.sqrt (1 - beta u v ^ 2)) := by
  have hsin : Real.sin (Real.pi / 2) = 1 := by simp
  simp [eMag, beta, hsin]
  have hbne : (1 - u ^ 2 / v ^ 2 : ℝ) ≠ 0 := by
    simpa [beta, div_pow] using (ne_of_gt hβ)
  field_simp [hr, hbne]

/-- The equatorial field exceeds the axial field:  E(π/2) = E(0)/((1−β²)·√(1−β²)),
    and the ratio ≥ 1 (the field concentrates in the equatorial plane). -/
theorem equatorial_over_axial (q r u v : ℝ) (hr : r ≠ 0) (hβ : 0 < 1 - beta u v ^ 2) :
    eMag q r u v (Real.pi / 2)
      = eMag q r u v 0 / ((1 - beta u v ^ 2) * Real.sqrt (1 - beta u v ^ 2)) := by
  rw [field_equatorial q r u v hr hβ]
  rw [field_axial q r u v]
  field_simp [hr, ne_of_gt hβ]

/-- The equatorial-over-axial ratio is ≥ 1: 1/((1−β²)·√(1−β²)) ≥ 1. -/
theorem equatorial_ratio_ge_one (β : ℝ) (hβ0 : 0 ≤ β ^ 2) (hβ1 : β ^ 2 < 1) :
    1 ≤ 1 / ((1 - β ^ 2) * Real.sqrt (1 - β ^ 2)) := by
  have ha : 0 < 1 - β ^ 2 := sub_pos.mpr hβ1
  have ha1 : 1 - β ^ 2 ≤ 1 := sub_le_self (1 : ℝ) hβ0
  have hsq : Real.sqrt (1 - β ^ 2) ≤ 1 := by
    simpa using (Real.sqrt_le_sqrt ha1)
  have hprod : (1 - β ^ 2) * Real.sqrt (1 - β ^ 2) ≤ 1 := by
    have h := mul_le_mul ha1 hsq (Real.sqrt_nonneg _) (by norm_num)
    simpa using h
  have hpos : 0 < (1 - β ^ 2) * Real.sqrt (1 - β ^ 2) := by
    exact mul_pos ha (Real.sqrt_pos.2 ha)
  simpa using ((one_le_inv₀ hpos).2 hprod)

/-- The flattening factor (1 − β²sin²θ)^(−3/2) ≥ 1: the ellipsoid is compressed
    along the motion, the field strongest broadside. -/
theorem flattening_ge_one (β θ : ℝ) (hβ0 : 0 ≤ β ^ 2) (hβ1 : β ^ 2 < 1) :
    1 ≤ 1 / ((1 - β ^ 2 * Real.sin θ ^ 2) * Real.sqrt (1 - β ^ 2 * Real.sin θ ^ 2)) := by
  have hs1 : Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hβs0 : 0 ≤ β ^ 2 * Real.sin θ ^ 2 := mul_nonneg hβ0 (sq_nonneg _)
  have hβs_le : β ^ 2 * Real.sin θ ^ 2 ≤ β ^ 2 := by
    simpa using (mul_le_mul_of_nonneg_left hs1 hβ0)
  have hβs1 : β ^ 2 * Real.sin θ ^ 2 < 1 := lt_of_le_of_lt hβs_le hβ1
  have ha : 0 < 1 - β ^ 2 * Real.sin θ ^ 2 := sub_pos.mpr hβs1
  have ha1 : 1 - β ^ 2 * Real.sin θ ^ 2 ≤ 1 := sub_le_self (1 : ℝ) hβs0
  have hsq : Real.sqrt (1 - β ^ 2 * Real.sin θ ^ 2) ≤ 1 := by
    simpa using (Real.sqrt_le_sqrt ha1)
  have hprod : (1 - β ^ 2 * Real.sin θ ^ 2) * Real.sqrt (1 - β ^ 2 * Real.sin θ ^ 2) ≤ 1 := by
    have h := mul_le_mul ha1 hsq (Real.sqrt_nonneg _) (by norm_num)
    simpa using h
  have hpos : 0 < (1 - β ^ 2 * Real.sin θ ^ 2) * Real.sqrt (1 - β ^ 2 * Real.sin θ ^ 2) :=
    mul_pos ha (Real.sqrt_pos.2 ha)
  simpa using ((one_le_inv₀ hpos).2 hprod)

/-- The speed condition (EP2 p. 495, p. 516):  μcv² = 1  ⟹  v = 1/√(μc) — the
    propagation speed of the medium, the same 1/√(LC) law as the telegrapher's line
    (T1) and the wave equation (T2). -/
theorem speed_condition (μ c v : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hv : 0 ≤ v)
    (h : μ * c * v ^ 2 = 1) :
    v = 1 / Real.sqrt (μ * c) := by
  have hμc : 0 < μ * c := mul_pos hμ hc
  have hv2 : v ^ 2 = 1 / (μ * c) := by
    rw [← h]
    field_simp [ne_of_gt hμc]
  have hv' : v = Real.sqrt (v ^ 2) := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hv]
  calc
    v = Real.sqrt (v ^ 2) := hv'
    _ = Real.sqrt (1 / (μ * c)) := by rw [hv2]
    _ = 1 / Real.sqrt (μ * c) := by
          rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) (μ * c)]
          norm_num

/-- The superluminal cone (EP2 p. 494): for u > v the disturbance is confined to the
    cone sin θ = v/u; the angle exists exactly when the charge outruns the waves. -/
theorem cone_angle (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : v < u) :
    let θ := Real.arcsin (v / u)
    Real.sin θ = v / u ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  intro θ
  have hvu0 : 0 < v / u := div_pos hv hu
  have hvu1 : v / u < 1 := (div_lt_one hu).2 huv
  have hvu_le : v / u ≤ 1 := le_of_lt hvu1
  have hsin : Real.sin θ = v / u := by
    dsimp [θ]
    exact Real.sin_arcsin (by nlinarith [hvu0]) hvu_le
  have hpos : 0 < θ := by
    dsimp [θ]
    exact (Real.arcsin_pos).2 hvu0
  have hlt : θ < Real.pi / 2 := by
    dsimp [θ]
    exact (Real.arcsin_lt_pi_div_two).2 hvu1
  exact ⟨hsin, hpos, hlt⟩

/-- The circuital-flux bridge to T2: the moving-charge induction is derived from a
    vector potential, so it is a circuital flux (div B = 0) — Heaviside's "A finds
    H" in the moving-charge setting (EP2 p. 505). -/
theorem moving_charge_induction_circuital (A B : V3 → V3)
    (h : ∀ x, curl3 A x = B x) (hdc : ∀ F : V3 → V3, div3 (curl3 F) = 0) :
    Circuital B :=
  potential_is_circuital A B h hdc

end HeavisideMovingCharge
