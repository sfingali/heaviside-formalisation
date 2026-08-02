import Mathlib

/-!
# T5: the δ-distribution's core laws (Dubovik–Tugushev [2] foundation) — on the new pin

The pin upgrade delivered mathlib's distribution theory (`Analysis/Distribution`:
`Distribution`, `TestFunction`, `delta`, `lineDerivCLM`, and the distributional
derivative's adjoint `lineDerivOp_apply_apply`).  This file assembles the
corpus-facing statements of the δ-laws that [2]'s multipole derivation rests on
(the delta-function sources, the smearing of the point charge, the
distributional derivative):

  · ⟨δ_x, f⟩ = f(x)          — the defining smearing law of the Dirac delta
  · ⟨q·δ_x, f⟩ = q·f(x)      — the point-charge density ρ = q·δ smears to q·f(x)
  · ⟨δ_x, f + g⟩ = ⟨δ_x,f⟩ + ⟨δ_x,g⟩ — the evaluation is linear
  · δ_x = 0 for x ∉ Ω        — the delta is supported at the single point
  · ⟨∂_v δ_x, g⟩ = −∂_v g(x) — the distributional derivative of the delta:
    the adjoint ⟨∂_v T, g⟩ = ⟨T, −∂_v g⟩ evaluated at the delta.

All five are kernel-verified against the mathlib API (the first, third and
fifth restate mathlib facts at the corpus's notation; the second and the fifth's
delta-application are derived here).
-/

namespace OAnimatorDistribution

open scoped Distributions

-- ⟨δ_x, f⟩ = f(x) — the defining smearing law.
theorem delta_smear {Ω : TopologicalSpace.Opens ℝ} {n : ℕ∞} (x : ℝ)
    (f : 𝓓^{n}(Ω, ℝ)) : Distribution.delta x f = f x :=
  Distribution.delta_apply x f

-- The point-charge density ρ = q·δ smears to q·f(x).
theorem pointCharge_smear {Ω : TopologicalSpace.Opens ℝ} {n : ℕ∞} (q x : ℝ)
    (f : 𝓓^{n}(Ω, ℝ)) : (q • Distribution.delta x) f = q * f x := by
  simp [Distribution.delta_apply, smul_eq_mul]

-- The evaluation at the delta is linear in the test function.
theorem delta_add {Ω : TopologicalSpace.Opens ℝ} {n : ℕ∞} (x : ℝ)
    (f g : 𝓓^{n}(Ω, ℝ)) :
    Distribution.delta x (f + g) = Distribution.delta x f + Distribution.delta x g := by
  simp [Distribution.delta_apply]

-- The delta is supported at the single point: δ_x = 0 for x ∉ Ω.
theorem delta_zero_outside {Ω : TopologicalSpace.Opens ℝ} {n : ℕ∞} (x : ℝ)
    (hx : x ∉ Ω) : (Distribution.delta x : 𝓓'^{n}(Ω, ℝ)) = 0 :=
  Distribution.delta_eq_zero_of_notMem x hx

-- The distributional derivative of the delta: ⟨∂_v δ_x, g⟩ = −∂_v g(x),
-- via the adjoint ⟨∂_v T, g⟩ = ⟨T, −∂_v g⟩.
theorem delta_deriv_adjoint {Ω : TopologicalSpace.Opens ℝ} (x v : ℝ)
    (g : 𝓓(Ω, ℝ)) :
    Distribution.lineDerivCLM v (Distribution.delta (n := ⊤) x) g =
      -((LineDeriv.lineDerivOp v g) x) := by
  have h := Distribution.lineDerivOp_apply_apply (f := Distribution.delta (n := ⊤) x) (g := g) (m := v)
  -- h : LineDeriv.lineDerivOp v (delta x) g = (delta x) (-LineDeriv.lineDerivOp v g)
  rw [Distribution.delta_apply] at h
  rw [← Distribution.lineDerivOp_eq_lineDerivCLM]
  rw [h]
  simp

end OAnimatorDistribution
