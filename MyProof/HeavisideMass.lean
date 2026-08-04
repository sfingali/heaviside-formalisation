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

open scoped Topology
open Filter
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

theorem excess_small_beta_limit :
    Tendsto (fun β : ℝ => excessEnergyCoefficient β / β ^ 2) (𝓝[>] 0) (𝓝 (4 / 3)) := by
  have hrem (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
      |β + β ^ 2 / 2 + β ^ 3 / 3 + Real.log (1 - β)| ≤ β ^ 4 / (1 - β) := by
    have hx : |β| < 1 := by simpa [abs_of_pos hβ0] using hβ1
    have h := Real.abs_log_sub_add_sum_range_le hx 3
    have hsum : (∑ i ∈ Finset.range 3, β ^ (i + 1) / (i + 1)) = β + β ^ 2 / 2 + β ^ 3 / 3 := by
      norm_num [Finset.sum_range_succ, pow_succ]
    rw [hsum] at h
    simpa [abs_of_pos hβ0] using h
  have hrem2 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
      |-β + β ^ 2 / 2 - β ^ 3 / 3 + Real.log (1 + β)| ≤ β ^ 4 / (1 - β) := by
    have hx : |(-β : ℝ)| < 1 := by simpa [abs_of_pos hβ0] using hβ1
    have h := Real.abs_log_sub_add_sum_range_le hx 3
    have hsum : (∑ i ∈ Finset.range 3, (-β) ^ (i + 1) / (i + 1)) = -β + β ^ 2 / 2 - β ^ 3 / 3 := by
      norm_num [Finset.sum_range_succ, pow_succ]
      ring
    rw [hsum] at h
    simpa [abs_of_pos hβ0] using h
  have hL (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
      |Real.log (1 + β) - Real.log (1 - β) - 2 * β - (2 / 3) * β ^ 3| ≤ 2 * β ^ 4 / (1 - β) := by
    have e1 : |Real.log (1 - β) + (β + β ^ 2 / 2 + β ^ 3 / 3)| ≤ β ^ 4 / (1 - β) := by
      simpa [add_comm] using hrem β hβ0 hβ1
    have e2 : |Real.log (1 + β) + (-β + β ^ 2 / 2 - β ^ 3 / 3)| ≤ β ^ 4 / (1 - β) := by
      simpa [add_comm] using hrem2 β hβ0 hβ1
    have hcombo : Real.log (1 + β) - Real.log (1 - β) - 2 * β - (2 / 3) * β ^ 3
        = (Real.log (1 + β) + (-β + β ^ 2 / 2 - β ^ 3 / 3)) - (Real.log (1 - β) + (β + β ^ 2 / 2 + β ^ 3 / 3)) := by
      ring
    rw [hcombo]
    calc
      |(Real.log (1 + β) + (-β + β ^ 2 / 2 - β ^ 3 / 3)) - (Real.log (1 - β) + (β + β ^ 2 / 2 + β ^ 3 / 3))|
          ≤ |Real.log (1 + β) + (-β + β ^ 2 / 2 - β ^ 3 / 3)| + |Real.log (1 - β) + (β + β ^ 2 / 2 + β ^ 3 / 3)| := abs_sub _ _
      _ ≤ β ^ 4 / (1 - β) + β ^ 4 / (1 - β) := add_le_add e2 e1
      _ = 2 * β ^ 4 / (1 - β) := by ring
  have hb0 : Tendsto (fun β : ℝ => β) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hp : Tendsto (fun β : ℝ => 2 * β + 2 * β ^ 3 + (1 / 3) * β ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun β : ℝ => 2 * β) (𝓝[>] 0) (𝓝 0) := by simpa using hb0.const_mul 2
    have h2 : Tendsto (fun β : ℝ => 2 * β ^ 3) (𝓝[>] 0) (𝓝 0) := by simpa using (hb0.pow 3).const_mul 2
    have h3 : Tendsto (fun β : ℝ => (1 / 3) * β ^ 2) (𝓝[>] 0) (𝓝 0) := by simpa [one_div] using (hb0.pow 2).const_mul (1 / 3 : ℝ)
    simpa using (h1.add h2).add h3
  have hbound (β : ℝ) (hβ0 : 0 < β) (hβ12 : β < 1 / 2) :
      |excessEnergyCoefficient β / β ^ 2 - 4 / 3| ≤ 2 * β + 2 * β ^ 3 + (1 / 3) * β ^ 2 := by
    have hβ1 : β < 1 := lt_trans hβ12 (by norm_num)
    have hLb := hL β hβ0 hβ1
    have hL2 : |Real.log (1 + β) - Real.log (1 - β) - 2 * β| ≤ 2 * β ^ 4 / (1 - β) + (2 / 3) * β ^ 3 := by
      have hsplit : |Real.log (1 + β) - Real.log (1 - β) - 2 * β| ≤
          |Real.log (1 + β) - Real.log (1 - β) - 2 * β - (2 / 3) * β ^ 3| + (2 / 3) * β ^ 3 := by
        have h' : Real.log (1 + β) - Real.log (1 - β) - 2 * β =
            (Real.log (1 + β) - Real.log (1 - β) - 2 * β - (2 / 3) * β ^ 3) + (2 / 3) * β ^ 3 := by ring
        calc
          |Real.log (1 + β) - Real.log (1 - β) - 2 * β|
              = |(Real.log (1 + β) - Real.log (1 - β) - 2 * β - (2 / 3) * β ^ 3) + (2 / 3) * β ^ 3| := congrArg abs h'
          _ ≤ |Real.log (1 + β) - Real.log (1 - β) - 2 * β - (2 / 3) * β ^ 3| + |(2 / 3) * β ^ 3| := abs_add_le _ _
          _ = |Real.log (1 + β) - Real.log (1 - β) - 2 * β - (2 / 3) * β ^ 3| + (2 / 3) * β ^ 3 := by
                rw [abs_of_nonneg (by positivity : 0 ≤ (2 / 3) * β ^ 3)]
      exact le_trans hsplit (by simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hLb ((2 / 3) * β ^ 3))
    have hle2 : 1 / (1 - β) ≤ 2 := by
      have hd : 1 - β ≥ 1 / 2 := by linarith
      have hpos : 0 < 1 - β := by linarith
      rw [div_le_iff₀ hpos]
      linarith
    have hnum : |(1 + β ^ 2) * (Real.log (1 + β) - Real.log (1 - β)) - 2 * β - (8 / 3) * β ^ 3|
        ≤ 2 * β ^ 4 / (1 - β) + β ^ 2 * (2 * β ^ 4 / (1 - β) + (2 / 3) * β ^ 3) := by
      have hsplit2 : (1 + β ^ 2) * (Real.log (1 + β) - Real.log (1 - β)) - 2 * β - (8 / 3) * β ^ 3
          = (Real.log (1 + β) - Real.log (1 - β) - 2 * β - (2 / 3) * β ^ 3) + β ^ 2 * (Real.log (1 + β) - Real.log (1 - β) - 2 * β) := by
        ring
      rw [hsplit2]
      have habs : |β ^ 2 * (Real.log (1 + β) - Real.log (1 - β) - 2 * β)| ≤ β ^ 2 * (2 * β ^ 4 / (1 - β) + (2 / 3) * β ^ 3) := by
        rw [abs_mul]
        rw [abs_of_nonneg (by positivity : 0 ≤ β ^ 2)]
        exact mul_le_mul_of_nonneg_left hL2 (by positivity : 0 ≤ β ^ 2)
      calc
        |(Real.log (1 + β) - Real.log (1 - β) - 2 * β - (2 / 3) * β ^ 3) + β ^ 2 * (Real.log (1 + β) - Real.log (1 - β) - 2 * β)|
            ≤ |Real.log (1 + β) - Real.log (1 - β) - 2 * β - (2 / 3) * β ^ 3| + |β ^ 2 * (Real.log (1 + β) - Real.log (1 - β) - 2 * β)| := abs_add_le _ _
        _ ≤ 2 * β ^ 4 / (1 - β) + β ^ 2 * (2 * β ^ 4 / (1 - β) + (2 / 3) * β ^ 3) := add_le_add hLb habs
    have hnum2 : |excessEnergyCoefficient β / β ^ 2 - 4 / 3| = |(1 + β ^ 2) * (Real.log (1 + β) - Real.log (1 - β)) - 2 * β - (8 / 3) * β ^ 3| / (2 * β ^ 3) := by
      unfold excessEnergyCoefficient
      have hlog : Real.log ((1 + β) / (1 - β)) = Real.log (1 + β) - Real.log (1 - β) := by
        rw [Real.log_div]
        · positivity
        · positivity
      rw [hlog]
      have h' : ((1 + β ^ 2) / (2 * β) * (Real.log (1 + β) - Real.log (1 - β)) - 1) / β ^ 2 - 4 / 3
          = ((1 + β ^ 2) * (Real.log (1 + β) - Real.log (1 - β)) - 2 * β - (8 / 3) * β ^ 3) / (2 * β ^ 3) := by
        field_simp [ne_of_gt hβ0]
        ring
      rw [h']
      rw [abs_div]
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * β ^ 3)]
    rw [hnum2]
    have hden : 0 < 2 * β ^ 3 := by positivity
    have hstep1 : |(1 + β ^ 2) * (Real.log (1 + β) - Real.log (1 - β)) - 2 * β - (8 / 3) * β ^ 3| / (2 * β ^ 3)
        ≤ (2 * β ^ 4 / (1 - β) + β ^ 2 * (2 * β ^ 4 / (1 - β) + (2 / 3) * β ^ 3)) / (2 * β ^ 3) := by
      exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
    refine le_trans hstep1 ?_
    have h1 : 2 * β ^ 4 / (1 - β) ≤ 4 * β ^ 4 := by
      calc
        2 * β ^ 4 / (1 - β) ≤ 2 * β ^ 4 * 2 := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hle2) (by positivity : 0 ≤ 2 * β ^ 4)
        _ = 4 * β ^ 4 := by ring
    have h2 : β ^ 2 * (2 * β ^ 4 / (1 - β) + (2 / 3) * β ^ 3) ≤ β ^ 2 * (4 * β ^ 4 + (2 / 3) * β ^ 3) := by
      exact mul_le_mul_of_nonneg_left (by simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right h1 ((2 / 3) * β ^ 3)) (by positivity : 0 ≤ β ^ 2)
    have htop : 2 * β ^ 4 / (1 - β) + β ^ 2 * (2 * β ^ 4 / (1 - β) + (2 / 3) * β ^ 3)
        ≤ 4 * β ^ 4 + β ^ 2 * (4 * β ^ 4 + (2 / 3) * β ^ 3) := add_le_add h1 h2
    have hdiv : (4 * β ^ 4 + β ^ 2 * (4 * β ^ 4 + (2 / 3) * β ^ 3)) / (2 * β ^ 3) ≤ 2 * β + 2 * β ^ 3 + (1 / 3) * β ^ 2 := by
      field_simp [ne_of_gt hden]
      nlinarith [sq_nonneg β, sq_nonneg (β ^ 2)]
    exact le_trans (div_le_div_of_nonneg_right htop (le_of_lt hden)) hdiv
  have hb : ∀ᶠ (β : ℝ) in 𝓝[>] 0, |excessEnergyCoefficient β / β ^ 2 - 4 / 3| ≤ 2 * β + 2 * β ^ 3 + (1 / 3) * β ^ 2 := by
    have hhalf : ∀ᶠ (β : ℝ) in 𝓝[>] 0, β < 1 / 2 := by
      have hd : ∀ᶠ (β : ℝ) in 𝓝[>] 0, dist β 0 < (1 / 2 : ℝ) := (Metric.tendsto_nhds.mp hb0) (1 / 2 : ℝ) (by norm_num)
      filter_upwards [hd] with β hdβ
      exact (abs_lt.mp (by simpa [Real.dist_eq, sub_zero] using hdβ)).2
    have hpos : ∀ᶠ (β : ℝ) in 𝓝[>] 0, 0 < β := by
      filter_upwards [self_mem_nhdsWithin] with β hβ
      exact hβ
    filter_upwards [hhalf, hpos] with β hβ12 hβ0
    exact hbound β hβ0 hβ12
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hpε : ∀ᶠ (β : ℝ) in 𝓝[>] 0, 2 * β + 2 * β ^ 3 + (1 / 3) * β ^ 2 < ε := by
    have hd : ∀ᶠ (β : ℝ) in 𝓝[>] 0, dist (2 * β + 2 * β ^ 3 + (1 / 3) * β ^ 2) 0 < ε := (Metric.tendsto_nhds.mp hp) ε hε
    filter_upwards [hd] with β hdβ
    exact (abs_lt.mp (by simpa [Real.dist_eq, sub_zero] using hdβ)).2
  filter_upwards [hb, hpε] with β hbd hpe
  simpa [Real.dist_eq] using lt_of_le_of_lt hbd hpe

end HeavisideMass
