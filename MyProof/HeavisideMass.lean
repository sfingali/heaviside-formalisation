import Mathlib
import MyProof.HeavisideMovingCharge
import MyProof.HeavisideEnergyFlux

/-!
# Heaviside corpus, T8: electromagnetic mass and momentum (1889)

Source: EP2 "On the Electromagnetic Effects due to the Motion of Electrification
through a Dielectric" (Phil. Mag. April 1889; EP2 djvu 796, pp. 494–512 area) — the
companion paper to the moving-charge field of T4 (EP2 pp. 492–515).  Adjacent to
T4 but a separate claim: the moving-charge field carries momentum, and its energy
grows with speed exactly like the kinetic energy of a mass that increases with
velocity — the first velocity-dependent "electromagnetic mass".

Heaviside's result (in the notation of T4, β = u/v): the field energy of the moving
charge scales with the relativistic factor

  E(v) / E(0) = 1 / √(1 − β²),

and the field momentum is parallel to the motion (the transverse parts cancel by
the azimuthal symmetry of the (A)/(B) field).  The small-speed coefficient gives
the "rest mass" of the electrification (the 4/3-type coefficient of the
electrostatic energy).

Formalised here (the honest kernel-verified core — the integral of the field energy
over all space is an analysis lift, so the ratio statement is the definition and
the factor's properties are the proved theorems):
  1. `massFactor` — the relativistic factor 1/√(1 − β²) (the mass/energy growth).
  2. `mass_factor_ge_one` — the factor ≥ 1: the field mass rises with speed.
  3. `mass_factor_mono` — the factor strictly increases with β: faster motion means
     heavier field (the velocity-dependent mass).
  4. `moving_energy_ratio` — the statement of the energy growth E(v)/E(0) = the
     factor (the integral origin documented; the factor properties kernel-verified).
  5. `equatorial_density_ratio` — from the T4 field: the energy density broadside
     exceeds the axial density by (1 − β²)⁻³ — the field concentrates equatorially
     as the speed rises.
  6. `MomentumAlongMotion` — the momentum-direction statement: the transverse
     components of the field momentum vanish by the azimuthal symmetry (the
     premise-structured integral cancellation).
-/

namespace HeavisideMass

open OAnimatorVector
open HeavisideMovingCharge

/-- The relativistic factor of the moving field:  1/√(1 − β²) — the velocity
    dependence of the field energy and mass (Heaviside's 1889 result; β = u/v the
    speed ratio of T4). -/
noncomputable def massFactor (β : ℝ) : ℝ :=
  1 / Real.sqrt (1 - β ^ 2)

/-- The factor ≥ 1 for subluminal motion: the field mass rises with speed. -/
theorem mass_factor_ge_one (β : ℝ) (hβ0 : 0 ≤ β ^ 2) (hβ1 : β ^ 2 < 1) :
    1 ≤ massFactor β := by
  unfold massFactor
  have ha : 0 < 1 - β ^ 2 := sub_pos.mpr hβ1
  have ha1 : 1 - β ^ 2 ≤ 1 := sub_le_self (1 : ℝ) hβ0
  have hsq : Real.sqrt (1 - β ^ 2) ≤ 1 := by
    simpa using (Real.sqrt_le_sqrt ha1)
  have hpos : 0 < Real.sqrt (1 - β ^ 2) := Real.sqrt_pos.2 ha
  simpa using ((one_le_inv₀ hpos).2 hsq)

/-- The factor strictly increases with speed: for 0 ≤ β₁ < β₂ < 1,
    1/√(1 − β₁²) < 1/√(1 − β₂²) — the faster the charge, the heavier the field. -/
theorem mass_factor_mono (β₁ β₂ : ℝ) (h₁0 : 0 ≤ β₁) (h₁₂ : β₁ < β₂) (h₂1 : β₂ < 1) :
    massFactor β₁ < massFactor β₂ := by
  unfold massFactor
  have h₂0 : 0 ≤ β₂ := le_trans h₁0 (le_of_lt h₁₂)
  have hsq1 : 0 < 1 - β₁ ^ 2 := by
    nlinarith [sq_nonneg β₁]
  have hsq2 : 0 < 1 - β₂ ^ 2 := by
    have hb2 : β₂ ^ 2 < 1 := by
      nlinarith [h₂0, h₂1]
    exact sub_pos.mpr hb2
  have h12 : 1 - β₂ ^ 2 < 1 - β₁ ^ 2 := by
    have hb : β₁ ^ 2 < β₂ ^ 2 := by nlinarith [h₁0, h₁₂]
    nlinarith [hb]
  have hsqrt : Real.sqrt (1 - β₂ ^ 2) < Real.sqrt (1 - β₁ ^ 2) :=
    Real.sqrt_lt_sqrt hsq2.le h12
  have hpos1 : 0 < Real.sqrt (1 - β₁ ^ 2) := Real.sqrt_pos.2 hsq1
  have hpos2 : 0 < Real.sqrt (1 - β₂ ^ 2) := Real.sqrt_pos.2 hsq2
  simpa using ((inv_lt_inv₀ hpos1 hpos2).2 hsqrt)

/-- The energy growth of the moving charge:  E(v)/E(0) = 1/√(1 − β²) — Heaviside's
    1889 result (the field energy of the moving electrification scales with the
    relativistic factor; the ratio is the statement, the integral over all space of
    the T4 field energy is the documented origin). -/
noncomputable def movingEnergyRatio (β : ℝ) : ℝ :=
  massFactor β

/-- The energy-density concentration: from the T4 field, the equatorial energy
    density exceeds the axial by the factor (1 − β²)⁻³ — the field energy piles up
    broadside as the speed rises (the geometric content of the mass growth). -/
theorem equatorial_density_ratio (q r u v : ℝ) (hr : r ≠ 0) (hβ : 0 < 1 - beta u v ^ 2) :
    eMag q r u v (Real.pi / 2) ^ 2
      = eMag q r u v 0 ^ 2 / ((1 - beta u v ^ 2) ^ 3) := by
  have hratio := equatorial_over_axial q r u v hr hβ
  -- hratio : eMag(π/2) = eMag(0) / ((1-β²)·√(1-β²))
  calc
    eMag q r u v (Real.pi / 2) ^ 2
        = (eMag q r u v 0 / ((1 - beta u v ^ 2) * Real.sqrt (1 - beta u v ^ 2))) ^ 2 := by
          rw [hratio]
    _ = eMag q r u v 0 ^ 2 / ((1 - beta u v ^ 2) ^ 2 * (1 - beta u v ^ 2)) := by
          field_simp [ne_of_gt hβ]
          rw [Real.sq_sqrt hβ.le]
    _ = eMag q r u v 0 ^ 2 / ((1 - beta u v ^ 2) ^ 3) := by
          congr 1

/-- The field momentum is along the motion: the transverse components of the total
    field momentum vanish — the azimuthal symmetry of the (A)/(B) field (E radial,
    H azimuthal) cancels them in the integral (the premise-structured statement; the
    momentum density is the T5 flux E × H, whose pointwise transverse parts are the
    integrands). -/
def MomentumAlongMotion (P : V3) : Prop :=
  P 0 = 0 ∧ P 1 = 0

end HeavisideMass
