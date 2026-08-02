import Mathlib

/-!
# Heaviside corpus, T3: the operational calculus and the step function

Heaviside's operational calculus treats p = d/dt as an algebraic symbol. Sources:
- ET2 §282–283 "The Expansion Theorem. Operational Way of getting Expansions in Normal
  Functions" (pp. 126–130): "when e is steady, beginning at the moment t = 0, the C due
  to e is expressed by C = (Z₀/p)·e + Σᵢ [Zᵢ/(pᵢ·(dZ/dp)ᵢ)]·e^{pᵢt}·e" over the roots pᵢ
  of Z(p) = 0 — the partial-fraction expansion whose inverse image is the sum of normal
  modes.
- EP2 p. 500: "p⁻¹ meaning integration from 0 to t with respect to t".
- ET3 §483 (p. 83, "Algebrisation of the Operational Solution"): a charge Q passing the
  origin at t = 0 is "Q₀ = Q/p operationally expressed" — the step-function encoding:
  the unit step is the operational image of p⁻¹.

Formalised here (the algebraic core the kernel can check; the analytic correspondence
p ↦ d/dt is the Laplace transform, absent from the pin, so it is documented, not
claimed):
  1. `unitStep` — the Heaviside unit step u(t) = 1 (t > 0), 0 (t < 0), via `Set.indicator`;
     `unitStep_pos`/`unitStep_neg`/`unitStep_add_neg` (the switching-pair identity).
  2. `expansion_two_pole_const` — the expansion-theorem partial fractions for the unit
     response, two distinct poles:
       1/(p(p−a)(p−b)) = 1/(p·ab) + 1/(a(a−b)(p−a)) + 1/(b(b−a)(p−b)).
  3. `expansion_two_pole_poly2` — the same identity with a quadratic numerator
     Q(p) = q₀ + q₁p + q₂p² (the residue coefficients Q(0)/P(0), Q(pᵢ)/(pᵢ·P′(pᵢ))).
  4. `exp_solves_ode` — the normal-mode correspondence: the image of (p − a)⁻¹ is e^{at},
     the solution of y′ = a·y (the exponential law of the operational calculus).

The distributional identity u′ = δ — the rigorous form of "p·u = 1" — is the adjoint
⟨u′, f⟩ = −⟨u, f′⟩ = f(0) = ⟨δ, f⟩, whose δ-machinery is in the O-Animator corpus
(`MyProof/DistributionLaws.delta_deriv_adjoint`). Cross-link: the operator factorisation
m² = (R + Lp)(S + Kp) of T1 is the same algebra in circuit form.
-/

namespace HeavisideOperational

/-- The Heaviside unit step: u(t) = 1 for t > 0, and 0 for t < 0.  Heaviside's "1/p" —
    the operational image of the unit impulse (ET3 §483: "Q₀ = Q/p operationally
    expressed"; EP2 p. 500: "p⁻¹ meaning integration from 0 to t"). -/
noncomputable def unitStep (t : ℝ) : ℝ :=
  Set.indicator (Set.Ioi (0 : ℝ)) (fun _ : ℝ => (1 : ℝ)) t

/-- u(t) = 1 for t > 0. -/
theorem unitStep_pos (t : ℝ) (ht : 0 < t) : unitStep t = 1 := by
  rw [unitStep]
  exact Set.indicator_of_mem (by simpa using ht) (fun _ : ℝ => (1 : ℝ))

/-- u(t) = 0 for t < 0. -/
theorem unitStep_neg (t : ℝ) (ht : t < 0) : unitStep t = 0 := by
  rw [unitStep]
  exact Set.indicator_of_notMem (by simpa using not_lt_of_gt ht) (fun _ : ℝ => (1 : ℝ))

/-- The switching-pair identity: u(t) + u(−t) = 1 for t ≠ 0 — the step pair splits the
    line. -/
theorem unitStep_add_neg (t : ℝ) (ht : t ≠ 0) : unitStep t + unitStep (-t) = 1 := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hpos : 0 < -t := by linarith
    rw [unitStep, unitStep]
    rw [Set.indicator_of_notMem (by simpa using not_lt_of_gt ht) (fun _ : ℝ => (1 : ℝ))]
    rw [Set.indicator_of_mem (by simpa using hpos) (fun _ : ℝ => (1 : ℝ))]
    norm_num
  · have hneg : -t < 0 := by linarith
    rw [unitStep, unitStep]
    rw [Set.indicator_of_mem (by simpa using ht) (fun _ : ℝ => (1 : ℝ))]
    rw [Set.indicator_of_notMem (by simpa using not_lt_of_gt hneg) (fun _ : ℝ => (1 : ℝ))]
    norm_num

/-- The expansion-theorem partial fractions for the unit response (Q = 1), two distinct
    poles:  1/(p(p−a)(p−b)) = 1/(p·ab) + 1/(a(a−b)(p−a)) + 1/(b(b−a)(p−b)).
    The three terms are the steady part (pole at p = 0, i.e. Z(0)/p) and the two normal
    modes 1/(pᵢ·P′(pᵢ)·(p − pᵢ)) of ET2 §282. -/
theorem expansion_two_pole_const (a b p : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hp : p ≠ 0) (hpa : p ≠ a) (hpb : p ≠ b) :
    1 / (p * (p - a) * (p - b))
      = 1 / (p * a * b) + 1 / (a * (a - b) * (p - a)) + 1 / (b * (b - a) * (p - b)) := by
  field_simp [ha, hb, hab, hp, hpa, hpb]
  ring

/-- The expansion-theorem partial fractions with a quadratic numerator
    Q(p) = q₀ + q₁p + q₂p²: the coefficients are the residues
    Q(0)/(P(0)), Q(a)/(a·P′(a)), Q(b)/(b·P′(b)) with P(p) = (p−a)(p−b). -/
theorem expansion_two_pole_poly2 (q0 q1 q2 a b p : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hp : p ≠ 0) (hpa : p ≠ a) (hpb : p ≠ b) :
    (q0 + q1 * p + q2 * p ^ 2) / (p * (p - a) * (p - b))
      = q0 / (p * a * b)
        + (q0 + q1 * a + q2 * a ^ 2) / (a * (a - b) * (p - a))
        + (q0 + q1 * b + q2 * b ^ 2) / (b * (b - a) * (p - b)) := by
  field_simp [ha, hb, hab, hp, hpa, hpb]
  ring

/-- The normal-mode correspondence: the image of (p − a)⁻¹ is e^{at} — the exponential
    solves its own differential equation y′ = a·y (with y(0) = 1).  This is the
    operational-calculus law under which the partial fractions of the expansion theorem
    become the sum of normal modes e^{pᵢt}. -/
theorem exp_solves_ode (a : ℝ) :
    deriv (fun t => Real.exp (a * t)) = fun t => a * Real.exp (a * t) := by
  funext t
  have h : HasDerivAt (fun s => Real.exp (a * s)) (a * Real.exp (a * t)) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using ((hasDerivAt_id t).const_mul a).exp
  exact h.deriv

end HeavisideOperational
