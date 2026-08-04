import Mathlib
import MyProof.HeavisideOperational
import MyProof.DistributionLaws

/-!
# Heaviside corpus, T9: fractional operators and the impulse function

Sources: ET2 §223–230 "On Operators in Physical Mathematics" (fractional
differentiations; djvu 3577–3589: "the direction of fractional differentiation");
ET2 §274–278 (the impulse function; djvu 5116–5396: "The idea of an impulse is well
known…"); ET3 §483 (Q₀ = Q/p — the step encoding, T3).

(a) The fractional operator p^½.  In the operational calculus the diffusive (cable)
equation  ∂V/∂t = (1/KR)·∂²V/∂x²  solves with the complementary error function: the
response to a steady force switched on at t = 0 is  V = V₀·erfc(x/(2√(KRt)))-like.
The pinned mathlib has NO `erf`/`erfc` (verified by probe: positive control
`Real.sqrt` resolves; `Real.erfc`, `Real.erf`, `Gaussian`, `pdfNormal`,
`MeasureTheory.pdfNormal`, `Real.gaussian` all unknown; file-level search of
`Mathlib/` finds no erfc def; the Gaussian density `gaussianPDFReal` in
`Probability/Distributions/Gaussian/Real.lean` is the CDF's building block but no
CDF/erfc is defined on it).  The honest kernel-verified core is therefore the heat
kernel — the fundamental solution, whose x-derivative profile is exactly the erfc
response's derivative:

  G(x,t) = exp(−x²/(4Dt)) / √(4πDt) = exp(−x²/(4Dt)) / (2√(πDt))

  satisfies   ∂G/∂t = D·∂²G/∂x².

The cable response erfc(x/(2√(Dt))) = (2/√π)·∫ₓ^∞ e^{−t²}dt is the accumulated
kernel profile (the x-antiderivative of a heat-equation solution is again a
heat-equation solution — the plan for the completed T9).  The correspondence is
NOT "p^½ ↦ erfc": the erfc is the operational image of e^{−x√(pRK)}/p, the
exponential-of-the-half-power, not of p^½ itself.

(b) The impulse function.  Differentiating the unit step u(t) gives the impulse —
the δ function, three decades before Dirac (ET2 §274–278 is 1893–95; Dirac 1926–27;
the impulse had Kirchhoff/Cauchy antecedents).  The rigorous distributional form is
the adjoint ⟨u′, f⟩ = −⟨u, f′⟩ = f(0) = ⟨δ, f⟩ (the
`DistributionLaws.delta_deriv_adjoint` machinery).  Kernel-verified here: the
totalized derivative of the step vanishes on both half-lines (the step is locally
constant away from the jump) — the jump at t = 0 is the impulse.

Formalised here:
  1. `heatKernel` — G(x,t) as above (sqrt split for the algebra).
  2. `heat_kernel_x_deriv` — ∂G/∂x = −(x/2Dt)·G (the chain).
  3. `heat_kernel_xx_deriv` — ∂²G/∂x² = (x²/(4D²t²) − 1/(2Dt))·G.
  4. `heat_kernel_heat_equation` — ∂G/∂t = D·∂²G/∂x²: the fundamental solution of
     the cable equation (the p^½ content, kernel-verified).
  5. `cable_equation` — the cable form with D = 1/(KR).
  6. `deriv_unitStep_pos`/`deriv_unitStep_neg` — the step's derivative vanishes on
     both half-lines (the impulse is concentrated at the jump).
-/

namespace HeavisideFractional

open scoped Topology
open HeavisideOperational

/-- The heat kernel (fundamental solution of the cable/diffusion equation):
    G(x,t) = exp(−x²/(4Dt)) / √(4πDt) = exp(−x²/(4Dt)) / (2√(πDt)) — the second form
    is the definition (the √4 split keeps the algebra definitionally consistent).
    Its x-derivative profile is the erfc response's derivative — Heaviside's p^½
    cable solution in Gaussian form (erfc absent from the pinned mathlib). -/
noncomputable def heatKernel (D x t : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (4 * D * t)) / (2 * Real.sqrt (Real.pi * D * t))

/-- ∂G/∂x = −(x/2Dt)·G — the chain rule for the kernel. -/
theorem heat_kernel_x_deriv (D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    deriv (fun y => heatKernel D y t) x
      = -(x / (2 * D * t)) * heatKernel D x t := by
  have hD4 : 4 * D * t ≠ 0 := by positivity
  have hsqrt_ne : 2 * Real.sqrt (Real.pi * D * t) ≠ 0 := by positivity
  have hpow : HasDerivAt (fun z => -(z ^ 2)) (-(2 * x)) x := by
    convert ((hasDerivAt_pow 2 x).neg) using 1
    all_goals try ring
    all_goals try rfl
  have hg : HasDerivAt (fun z => -(z ^ 2) / (4 * D * t)) (-(2 * x) / (4 * D * t)) x := by
    convert hpow.div_const (4 * D * t) using 1
  have hE : HasDerivAt (fun z => Real.exp (-(z ^ 2) / (4 * D * t)))
      (Real.exp (-(x ^ 2) / (4 * D * t)) * (-(2 * x) / (4 * D * t))) x := hg.exp
  have hW : HasDerivAt (fun _ : ℝ => (1 / (2 * Real.sqrt (Real.pi * D * t)) : ℝ)) 0 x := by
    convert hasDerivAt_const x (1 / (2 * Real.sqrt (Real.pi * D * t))) using 1
  have hG : HasDerivAt (fun y => Real.exp (-(y ^ 2) / (4 * D * t))
        * (1 / (2 * Real.sqrt (Real.pi * D * t))))
      (Real.exp (-(x ^ 2) / (4 * D * t)) * (-(2 * x) / (4 * D * t))
        * (1 / (2 * Real.sqrt (Real.pi * D * t)))) x := by
    convert (hE.mul hW) using 1
    all_goals try rfl
    all_goals try simp
  have hG' : HasDerivAt (fun y => heatKernel D y t)
      (Real.exp (-(x ^ 2) / (4 * D * t)) * (-(2 * x) / (4 * D * t))
        * (1 / (2 * Real.sqrt (Real.pi * D * t)))) x := by
    convert hG using 1
    all_goals try simp [heatKernel]
    all_goals try ring_nf
    all_goals try (funext y; rw [show Real.exp (y ^ 2 * D⁻¹ * t⁻¹ * (-1 / 4)) = Real.exp (D⁻¹ * t⁻¹ * y ^ 2 * (-1 / 4)) by exact congrArg Real.exp (by ring)]; ring)
  have hv : Real.exp (-(x ^ 2) / (4 * D * t)) * (-(2 * x) / (4 * D * t))
        * (1 / (2 * Real.sqrt (Real.pi * D * t)))
      = -(x / (2 * D * t)) * heatKernel D x t := by
    simp [heatKernel]
    field_simp [hD4, hsqrt_ne]
    ring
  rw [← hv]
  exact hG'.deriv

/-- ∂²G/∂x² = (x²/(4D²t²) − 1/(2Dt))·G — the second x-derivative. -/
theorem heat_kernel_xx_deriv (D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    deriv (fun y => deriv (fun z => heatKernel D z t) y) x
      = (x ^ 2 / (4 * D ^ 2 * t ^ 2) - 1 / (2 * D * t)) * heatKernel D x t := by
  have hD4 : 4 * D * t ≠ 0 := by positivity
  have hDt : 2 * D * t ≠ 0 := by positivity
  have hsqrt_ne : 2 * Real.sqrt (Real.pi * D * t) ≠ 0 := by positivity
  have hGx : ∀ y, HasDerivAt (fun z => heatKernel D z t)
      (-(y / (2 * D * t)) * heatKernel D y t) y := by
    intro y
    have hpow : HasDerivAt (fun z => -(z ^ 2)) (-(2 * y)) y := by
      convert ((hasDerivAt_pow 2 y).neg) using 1
      all_goals try ring
      all_goals try rfl
    have hg : HasDerivAt (fun z => -(z ^ 2) / (4 * D * t)) (-(2 * y) / (4 * D * t)) y := by
      convert hpow.div_const (4 * D * t) using 1
    have hE : HasDerivAt (fun z => Real.exp (-(z ^ 2) / (4 * D * t)))
        (Real.exp (-(y ^ 2) / (4 * D * t)) * (-(2 * y) / (4 * D * t))) y := hg.exp
    have hW : HasDerivAt (fun _ : ℝ => (1 / (2 * Real.sqrt (Real.pi * D * t)) : ℝ)) 0 y := by
      convert hasDerivAt_const y (1 / (2 * Real.sqrt (Real.pi * D * t))) using 1
    have hG : HasDerivAt (fun z => heatKernel D z t)
        (Real.exp (-(y ^ 2) / (4 * D * t)) * (-(2 * y) / (4 * D * t))
          * (1 / (2 * Real.sqrt (Real.pi * D * t)))) y := by
      convert (hE.mul hW) using 1
      all_goals try rfl
      all_goals try simp [heatKernel]
      all_goals try norm_num
      all_goals try ring_nf
      all_goals try (field_simp [hD4, hsqrt_ne]; ring)
      all_goals try (funext z; simp; ring)
    convert hG using 1
    all_goals try simp [heatKernel]
    all_goals try field_simp [hD4, hsqrt_ne]
    all_goals try ring
  have hlin : HasDerivAt (fun y => -y / (2 * D * t)) (-(1 / (2 * D * t))) x := by
    convert ((hasDerivAt_id x).neg.div_const (2 * D * t)) using 1
    all_goals try ring
    all_goals try rfl
    all_goals try simp
    all_goals try norm_num
    all_goals try (funext y; ring)
  have hprod := (hlin.mul (hGx x))
  have hGx' : deriv (fun y => deriv (fun z => heatKernel D z t) y) x
      = deriv (fun y => -(y / (2 * D * t)) * heatKernel D y t) x := by
    congr 2
    funext y
    exact (heat_kernel_x_deriv D y t hD ht)
  rw [hGx']
  rw [show deriv (fun y => -(y / (2 * D * t)) * heatKernel D y t) x
        = deriv ((fun y => -y / (2 * D * t)) * fun z => heatKernel D z t) x by
      congr 2
      funext y
      simp
      ring_nf]
  rw [hprod.deriv]
  field_simp [hDt]
  ring

/-- The heat equation:  ∂G/∂t = D·∂²G/∂x² — the fundamental solution of the cable
    equation, the kernel-verified content of Heaviside's p^½ solution. -/
theorem heat_kernel_heat_equation (D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    deriv (fun s => heatKernel D x s) t
      = D * deriv (fun y => deriv (fun z => heatKernel D z t) y) x := by
  have hD4 : 4 * D * t ≠ 0 := by positivity
  have hDt : 2 * D * t ≠ 0 := by positivity
  have hD4t2 : 4 * D * t ^ 2 ≠ 0 := by positivity
  have hsqrt_ne : 2 * Real.sqrt (Real.pi * D * t) ≠ 0 := by positivity
  have hinv : HasDerivAt (fun s => (s : ℝ)⁻¹) (-(t ^ 2)⁻¹) t := by
    convert hasDerivAt_inv ht.ne' using 1
  have hg : HasDerivAt (fun s => -(x ^ 2) / (4 * D * s))
      (x ^ 2 / (4 * D * t ^ 2)) t := by
    have hlin : HasDerivAt (fun s => -(x ^ 2 / (4 * D)) * (s : ℝ)⁻¹)
        (-(x ^ 2 / (4 * D)) * (-(t ^ 2)⁻¹)) t := by
      exact hinv.const_mul (-(x ^ 2 / (4 * D)))
    convert hlin using 1
    all_goals try simp
    all_goals try ring_nf
  have hE : HasDerivAt (fun s => Real.exp (-(x ^ 2) / (4 * D * s)))
      (Real.exp (-(x ^ 2) / (4 * D * t)) * (x ^ 2 / (4 * D * t ^ 2))) t := hg.exp
  have hsqrt : HasDerivAt (fun s => Real.sqrt (Real.pi * D * s))
      (1 / (2 * Real.sqrt (Real.pi * D * t)) * (Real.pi * D)) t := by
    have hsq := Real.hasDerivAt_sqrt (by positivity : Real.pi * D * t ≠ 0)
    have hlin : HasDerivAt (fun s => Real.pi * D * s) (Real.pi * D) t := by
      convert ((hasDerivAt_id t).const_mul (Real.pi * D)) using 1
      all_goals try ring
      all_goals try rfl
    convert (hsq.comp t hlin) using 1
    all_goals try rfl
  have hw : HasDerivAt (fun s => (1 / 2) * (Real.sqrt (Real.pi * D * s))⁻¹)
      (-(1 / (2 * t)) * (1 / (2 * Real.sqrt (Real.pi * D * t)))) t := by
    have hne : Real.sqrt (Real.pi * D * t) ≠ 0 := by positivity
    have hw' := hsqrt.inv hne
    have hw'' := HasDerivAt.const_mul (1 / 2 : ℝ) hw'
    convert hw'' using 1
    all_goals try rfl
    all_goals try simp
    all_goals try (rw [Real.sq_sqrt (by positivity : 0 ≤ Real.pi * D * t)])
    all_goals try field_simp [hsqrt_ne, (by positivity : Real.pi * D * t ≠ 0)]
  have hGt0 : HasDerivAt (fun s => Real.exp (-(x ^ 2) / (4 * D * s))
        * ((1 / 2) * (Real.sqrt (Real.pi * D * s))⁻¹))
      (Real.exp (-(x ^ 2) / (4 * D * t)) * (x ^ 2 / (4 * D * t ^ 2))
        * ((1 / 2) * (Real.sqrt (Real.pi * D * t))⁻¹)
        + Real.exp (-(x ^ 2) / (4 * D * t))
          * (-(1 / (2 * t)) * ((1 / 2) * (Real.sqrt (Real.pi * D * t))⁻¹))) t := by
    convert (hE.mul hw) using 1
    all_goals try rfl
    all_goals try simp
    all_goals try norm_num
    all_goals try ring_nf
    all_goals try exact Or.inl trivial
  have hGt : HasDerivAt (fun s => heatKernel D x s)
      ((x ^ 2 / (4 * D * t ^ 2) - 1 / (2 * t)) * heatKernel D x t) t := by
    convert hGt0 using 1
    all_goals try simp [heatKernel]
    all_goals try field_simp [hD4, hsqrt_ne]
    all_goals try ring
    all_goals try (funext s; rw [show Real.sqrt (D * s * Real.pi) = Real.sqrt (D * Real.pi * s) by exact congrArg Real.sqrt (by ring)])
  have hxx := heat_kernel_xx_deriv D x t hD ht
  have hv : (x ^ 2 / (4 * D * t ^ 2) - 1 / (2 * t)) * heatKernel D x t
      = D * ((x ^ 2 / (4 * D ^ 2 * t ^ 2) - 1 / (2 * D * t)) * heatKernel D x t) := by
    field_simp [hD4, hDt]
  rw [hGt.deriv]
  rw [hv]
  rw [← hxx]

/-- The cable equation in Heaviside's form: with the diffusivity D = 1/(KR) of the
    submarine cable (R the resistance, K the capacitance per unit length), the kernel
    satisfies ∂G/∂t = (1/(KR))·∂²G/∂x² — the p^½ diffusion of ET2 §223–230. -/
theorem cable_equation (K R x t : ℝ) (hK : 0 < K) (hR : 0 < R) (ht : 0 < t) :
    deriv (fun s => heatKernel (1 / (K * R)) x s) t
      = (1 / (K * R)) * deriv (fun y => deriv (fun z => heatKernel (1 / (K * R)) z t) y) x := by
  have hD : 0 < 1 / (K * R) := by positivity
  exact heat_kernel_heat_equation (1 / (K * R)) x t hD ht

/-- The derivative of the unit step vanishes on the positive half-line: u is
    constantly 1 there, so the impulse is NOT distributed — it is concentrated at
    the jump t = 0 (the δ of ET2 §274–278; the distributional adjoint
    ⟨u′, f⟩ = f(0) is the DistributionLaws cross-link). -/
theorem deriv_unitStep_pos (t : ℝ) (ht : 0 < t) : deriv unitStep t = 0 := by
  have h_eq : unitStep =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi ht] with t' ht'
    exact unitStep_pos t' ht'
  have h := (hasDerivAt_const t (1 : ℝ)).deriv
  rw [h_eq.deriv_eq]
  exact h

/-- The derivative of the unit step vanishes on the negative half-line. -/
theorem deriv_unitStep_neg (t : ℝ) (ht : t < 0) : deriv unitStep t = 0 := by
  have h_eq : unitStep =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Iio ht] with t' ht'
    exact unitStep_neg t' ht'
  have h := (hasDerivAt_const t (0 : ℝ)).deriv
  rw [h_eq.deriv_eq]
  exact h

end HeavisideFractional
