import Mathlib
import MyProof.HeavisideMovingCharge
import MyProof.HeavisideEnergyFlux

/-!
# Heaviside corpus, T8: the field energy and momentum of the moving charge (1889/1897)

Source: EP2 "On the Electromagnetic Effects due to the Motion of Electrification
through a Dielectric" (Phil. Mag. April 1889; EP2 djvu 796, pp. 494–512 area) — the
companion paper to the moving-charge field of T4 (EP2 pp. 492–515).  Adjacent to
T4 but a separate claim: the moving-charge field carries momentum, and its energy
depends on the speed in a way that behaves like a velocity-dependent mass.

Attribution note (the framing IS the claim in a transcription dossier): the
γ = 1/√(1 − β²) shape in `HeavisideMovingCharge` is Heaviside's own 1889
EQUATORIAL FIELD ENHANCEMENT (E = qγ/r² at θ = π/2) — that factor is not a mass.
The γ-shaped mass formula is Lorentz's deformable electron (1899/1904).  Heaviside's
field energy is instead the Searle coefficient (Searle 1897, completing Heaviside's
program): the moving sphere's energy is W(β) = W₀·[(1+β²)/(2β)·ln((1+β)/(1−β)) − 1],
whose small-speed expansion carries the classic 4/3-type coefficient.

Formalised here (the honest kernel-verified core — the field-energy integral and the
log-expansion are analysis lifts, so the coefficient is the definition and the
documented statements carry the attribution):
  1. `excessEnergyCoefficient` — the β-dependence of the moving sphere's field energy (g-bracket, neutral name; the Abraham/Kaufmann/Searle attribution lives in the docstring).
  2. `movingEnergyRatio` — the statement of the energy growth (the integral origin
     documented; the coefficient's role kernel-defined).
  3. `equatorial_density_ratio` — from the T4 field: the energy density broadside
     exceeds the axial density by (1 − β²)⁻³ — the field concentrates equatorially
     as the speed rises (the geometric content of the energy growth).
  4. `MomentumAlongMotion` — the momentum-direction statement: the transverse
     components of the field momentum vanish by the azimuthal symmetry (the
     premise-structured integral cancellation).
-/

namespace HeavisideMass

open OAnimatorVector
open HeavisideMovingCharge

/-- The excess-energy coefficient of the moving sphere's field (the g-bracket):
    g(β) = (1+β²)/(2β)·ln((1+β)/(1−β)) − 1, with W(β) = W₀·(1 + g(β)) for the rest
    energy W₀ — g(0) = 0, so g is the EXCESS over the rest energy, not the total.
    The small-speed expansion is g(β) = (4/3)β² + O(β⁴) — the classic velocity-
    dependent mass coefficient; NOT the γ of Lorentz's deformable electron (γ is
    Heaviside's equatorial FIELD enhancement, T4).  Attribution is contested in the
    secondary literature: Kaufmann's ψ(β) = g(β)/β² writes the bracket as Abraham's,
    introduced as the correction to Searle's field-energy formula — the name here is
    deliberately neutral.  (The log-expansion limit is a documented analysis lift.) -/
noncomputable def excessEnergyCoefficient (β : ℝ) : ℝ :=
  (1 + β ^ 2) / (2 * β) * Real.log ((1 + β) / (1 - β)) - 1

/-- The energy growth statement of the moving charge:  W(β) = W₀·g(β) with g the
    Searle coefficient — the field energy of the moving electrification (the
    integral over all space of the T4 field energy is the documented origin). -/
noncomputable def movingEnergyRatio (β : ℝ) : ℝ :=
  excessEnergyCoefficient β

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
