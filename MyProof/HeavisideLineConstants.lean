import Mathlib
import MyProof.HeavisideTelegrapher

/-!
# Heaviside corpus, T7: the line constants — propagation constant and impedance

Corollaries of T1's operator algebra in the harmonic regime p = jω.  The telegrapher
system of EP1 (1885–87 series) with the operator p = d/dt becomes algebraic in the
harmonic regime: with p = jω the series impedance per unit length is Z = R + jωL and
the shunt admittance Y = G + jωC, and the propagation constant and characteristic
impedance are the square roots

  γ² = (R + jωL)(G + jωC),        Z₀² = (R + jωL)/(G + jωC).

Heaviside's own statements: the propagation constant m of EP1 pp. 429–560 and the
impedance/reflection analysis of the same series; the distortionless condition
RK = LS (T1) makes γ = √(RS) + jω√(LK) — attenuation √(RS) and phase constant
ω√(LK), phase velocity 1/√(LK) independent of frequency.

Formalised here (ℂ algebra; the principal-branch square root):
  1. `seriesImpedance`/`shuntAdmittance` — Z = R + jωL, Y = G + jωC.
  2. `propagationConstant` γ = √(Z·Y) and `characteristicImpedance` Z₀ = √(Z/Y).
  3. `gamma_sq`/`z0_sq` — the defining squared identities (kernel-verified: the pin
     defines `Complex.sqrt z = z ^ (2⁻¹ : ℂ)` via cpow, so the identity (√z)² = z
     needs the log-branch bound −π < (log z · ½).im ≤ π, proved here once).
  4. `z0_ratio_sq` — the ratio form: (Z/γ)² = Z/Y — the impedance is the ratio of
     voltage to current wave amplitudes, so Z₀·γ = Z up to the branch choice.
  5. `distortionless_square` — under RK = LS,  (√(RS) + jω√(LK))² = (R+jωL)(S+jωK)
     — T1's factorisation in harmonic form; the branch statement γ = √(RS) + jω√(LK)
     is the documented principal-branch choice.
  6. `phase_velocity` — ω/β = 1/√(LK): the distortionless line's phase velocity is
     T1's finite signal speed (the cross-link).
-/

namespace HeavisideLineConstants

open Complex

/-- The series impedance per unit length in the harmonic regime:  Z = R + jωL. -/
noncomputable def seriesImpedance (R L ω : ℝ) : ℂ :=
  (R : ℂ) + Complex.I * (ω : ℂ) * (L : ℂ)

/-- The shunt admittance per unit length in the harmonic regime:  Y = G + jωC. -/
noncomputable def shuntAdmittance (G C ω : ℝ) : ℂ :=
  (G : ℂ) + Complex.I * (ω : ℂ) * (C : ℂ)

/-- The propagation constant:  γ = √((R + jωL)(G + jωC))  (principal branch). -/
noncomputable def propagationConstant (R L G C ω : ℝ) : ℂ :=
  Complex.sqrt (seriesImpedance R L ω * shuntAdmittance G C ω)

/-- The characteristic impedance:  Z₀ = √((R + jωL)/(G + jωC))  (principal branch). -/
noncomputable def characteristicImpedance (R L G C ω : ℝ) : ℂ :=
  Complex.sqrt (seriesImpedance R L ω / shuntAdmittance G C ω)

set_option linter.unusedSimpArgs false in
/-- The squared-square-root identity: (√z)² = z — unconditional with the pin's
    definition `Complex.sqrt z = z ^ (2⁻¹ : ℂ)` (cpow; the z = 0 case is
    `0 ^ (2⁻¹) = 0`).  The z ≠ 0 case follows from `Complex.cpow_mul` with the
    log-branch bound −π < (log z · ½).im ≤ π. -/
theorem sqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  rw [Complex.sqrt]
  rw [← Complex.cpow_natCast]
  have h2im : ((2⁻¹ : ℂ)).im = 0 := by
    rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by norm_num]
    simp
  have h2re : ((2⁻¹ : ℂ)).re = (1 / 2 : ℝ) := by
    rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by norm_num]
    simp
  have hb1 : -Real.pi < (Complex.log z * (2⁻¹ : ℂ)).im := by
    rw [Complex.mul_im, h2im, h2re]
    have hlog : -Real.pi < (Complex.log z).im := Complex.neg_pi_lt_log_im z
    nlinarith [hlog, Real.pi_pos]
  have hb2 : (Complex.log z * (2⁻¹ : ℂ)).im ≤ Real.pi := by
    rw [Complex.mul_im, h2im, h2re]
    have hlog : (Complex.log z).im ≤ Real.pi := Complex.log_im_le_pi z
    nlinarith [hlog, Real.pi_pos]
  have hmul := Complex.cpow_mul (x := z) (y := (2⁻¹ : ℂ)) (z := (2 : ℂ)) hb1 hb2
  have hone : (2⁻¹ : ℂ) * 2 = 1 := by norm_num
  simp [Complex.cpow_natCast, hone]

/-- γ² = (R + jωL)(G + jωC). -/
theorem gamma_sq (R L G C ω : ℝ) :
    propagationConstant R L G C ω ^ 2 = seriesImpedance R L ω * shuntAdmittance G C ω := by
  rw [propagationConstant]
  exact sqrt_sq (seriesImpedance R L ω * shuntAdmittance G C ω)

/-- Z₀² = (R + jωL)/(G + jωC). -/
theorem z0_sq (R L G C ω : ℝ) :
    characteristicImpedance R L G C ω ^ 2 = seriesImpedance R L ω / shuntAdmittance G C ω := by
  rw [characteristicImpedance]
  exact sqrt_sq (seriesImpedance R L ω / shuntAdmittance G C ω)

/-- The ratio form: (Z/γ)² = Z/Y — the impedance is the ratio of the voltage wave to
    the current wave (Z₀·γ = Z up to the principal-branch choice of sign). -/
theorem z0_ratio_sq (R L G C ω : ℝ) (γ : ℂ)
    (hγ : γ ^ 2 = seriesImpedance R L ω * shuntAdmittance G C ω)
    (hZ : seriesImpedance R L ω ≠ 0) :
    (seriesImpedance R L ω / γ) ^ 2 = seriesImpedance R L ω / shuntAdmittance G C ω := by
  calc
    (seriesImpedance R L ω / γ) ^ 2
        = seriesImpedance R L ω ^ 2 / γ ^ 2 := by ring
    _ = seriesImpedance R L ω ^ 2 / (seriesImpedance R L ω * shuntAdmittance G C ω) := by
          rw [hγ]
    _ = seriesImpedance R L ω / shuntAdmittance G C ω := by
          field_simp [hZ]

/-- The two expressions agree in square: Z₀² = (Z/γ)² (both equal Z/Y). -/
theorem impedance_ratio_consistency (R L G C ω : ℝ) (γ : ℂ)
    (hγ : γ ^ 2 = seriesImpedance R L ω * shuntAdmittance G C ω)
    (hZ : seriesImpedance R L ω ≠ 0)
    (hz0 : characteristicImpedance R L G C ω ^ 2 = seriesImpedance R L ω / shuntAdmittance G C ω) :
    characteristicImpedance R L G C ω ^ 2 = (seriesImpedance R L ω / γ) ^ 2 := by
  rw [hz0, z0_ratio_sq R L G C ω γ hγ hZ]

/-- The distortionless factorisation in harmonic form: under RK = LS,
    (√(RS) + jω√(LK))² = (R + jωL)(S + jωK) — T1's m² = (√(RS) + p√(LK))² with
    p = jω.  The branch statement γ = √(RS) + jω√(LK) (attenuation √(RS), phase
    constant ω√(LK)) is the principal-branch choice, which agrees for the positive
    real parts of a distortionless line. -/
theorem distortionless_square (R L S K ω : ℝ) (hRK : R * K = L * S)
    (hRS : 0 ≤ R * S) (hLK : 0 ≤ L * K) (hLS : 0 ≤ L * S) :
    ((Real.sqrt (R * S) : ℂ) + Complex.I * (ω : ℂ) * (Real.sqrt (L * K) : ℂ)) ^ 2
      = ((R : ℂ) + Complex.I * (ω : ℂ) * (L : ℂ))
        * ((S : ℂ) + Complex.I * (ω : ℂ) * (K : ℂ)) := by
  have hα2 : Real.sqrt (R * S) ^ 2 = R * S := Real.sq_sqrt hRS
  have hβ2 : Real.sqrt (L * K) ^ 2 = L * K := Real.sq_sqrt hLK
  have hsqrt : Real.sqrt (R * S) * Real.sqrt (L * K) = L * S := by
    calc
      Real.sqrt (R * S) * Real.sqrt (L * K) = Real.sqrt ((R * S) * (L * K)) := by
        exact (Real.sqrt_mul hRS (L * K)).symm
      _ = Real.sqrt ((L * S) ^ 2) := by
            congr 1
            nlinarith [hRK]
      _ = L * S := by
            rw [Real.sqrt_sq_eq_abs (L * S), abs_of_nonneg hLS]
  apply Complex.ext
  · -- real parts: α² − (ωβ)² = RS − ω²LK
    rw [pow_two]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    have hA : Real.sqrt (R * S) * Real.sqrt (R * S) = R * S := by
      rw [← pow_two, hα2]
    have hB : ω * Real.sqrt (L * K) * (ω * Real.sqrt (L * K)) = ω * L * (ω * K) := by
      calc
        ω * Real.sqrt (L * K) * (ω * Real.sqrt (L * K)) = (ω * Real.sqrt (L * K)) ^ 2 := by ring
        _ = ω ^ 2 * Real.sqrt (L * K) ^ 2 := by ring
        _ = ω ^ 2 * (L * K) := by rw [hβ2]
        _ = ω * L * (ω * K) := by ring
    rw [hA, hB]
  · -- imaginary parts: 2ωαβ = ω(RK + LS)
    rw [pow_two]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    calc
      Real.sqrt (R * S) * (ω * Real.sqrt (L * K)) + ω * Real.sqrt (L * K) * Real.sqrt (R * S)
          = ω * (Real.sqrt (R * S) * Real.sqrt (L * K))
            + ω * (Real.sqrt (L * K) * Real.sqrt (R * S)) := by ring
      _ = ω * (L * S) + ω * (L * S) := by
            rw [hsqrt]
            have h2 : Real.sqrt (L * K) * Real.sqrt (R * S) = L * S := by
              rw [mul_comm, hsqrt]
            rw [h2]
      _ = R * (ω * K) + ω * L * S := by
            symm
            calc
              R * (ω * K) + ω * L * S = ω * (R * K) + ω * (L * S) := by ring
              _ = ω * (L * S) + ω * (L * S) := by rw [hRK]

/-- The phase velocity of the distortionless line: ω/β = 1/√(LK) — T1's finite signal
    speed (the phase constant β = ω√(LK) carries the frequency). -/
theorem phase_velocity (L K ω : ℝ) (hω : ω ≠ 0) (hLK : 0 < L * K) :
    ω / (ω * Real.sqrt (L * K)) = 1 / Real.sqrt (L * K) := by
  field_simp [hω, ne_of_gt hLK]

end HeavisideLineConstants
