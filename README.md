# Heaviside Formalisation Dossier

Status 2026-08-02. Corpus: `papers/` (5 volumes, archive.org, public domain).
Env: Lean 4.33.0-rc1, mathlib pin `f4570dc2f3c801ed0c0edd5867f943e2b84e4dec` — carried in the
repository's lakefile (the reproduction unit is the repo: lakefile + lean-toolchain + MyProof/).
Method: per-claim kernel verification; physics in the premises, theorems about the model's logic;
statements transcribed from the PDF pages, locators by print page.

**Status: T1 COMPLETE (2026-08-01, kernel-verified 0/0, axioms = propext/Classical.choice/Quot.sound).
`MyProof/HeavisideTelegrapher.lean` (318 lines, 4 theorems) — full build 8697 jobs clean.
T2 COMPLETE (2026-08-01): `MyProof/HeavisideField.lean` (197 lines, 6 theorems) —
the curl pair (4)/(5), circuital current, potential-is-circuital, total-current + continuity,
the free-space wave equation ΔE = μc·∂²E/∂t², the three-laws bridge — build 8698 jobs clean.
T3 COMPLETE (2026-08-01): `MyProof/HeavisideOperational.lean` (128 lines, 6 theorems) —
unit step via Set.indicator (pos/neg/switching-pair), the expansion-theorem partial fractions
(two-pole unit response + quadratic numerator, kernel-verified by field_simp/ring),
exp_solves_ode (the normal-mode correspondence) — build 8697 jobs clean.
T4 COMPLETE (2026-08-02): `MyProof/HeavisideMovingCharge.lean` (250 lines, 11 theorems) —
the enhancement-factor lemmas added (γ = 1/√(1−β²) as Heaviside's field enhancement);
the spherical frame, (A)/(B) magnitudes, E·H = 0 perpendicularity, axial/equatorial closed
forms + ratio, flattening factor ≥ 1, μcv² = 1 speed condition, the superluminal cone
θ = arcsin(v/u), the circuital-flux bridge to T2 — build 8699 jobs clean.
T7 COMPLETE (2026-08-01): `MyProof/HeavisideLineConstants.lean` (175 lines, 7 theorems) —
γ² = (R+jωL)(G+jωC), Z₀² = (R+jωL)/(G+jωC), the ratio form (Z/γ)² = Z/Y, the cpow
squared-sqrt identity (branch-bounded), the distortionless harmonic factorisation
(√(RS)+jω√(LK))², phase velocity 1/√(LK) — build 8698 jobs clean.
T5 COMPLETE (2026-08-01): `MyProof/HeavisideEnergyFlux.lean` (94 lines, 4 theorems) —
W = E×H flux def, perpendicularity to both forces, the Poynting balance
div(E×H) = −(H·Ḃ + E·J) — build 8698 jobs clean.
T6 COMPLETE (2026-08-01): `MyProof/HeavisideGravitomagnetic.lean` (145 lines, 5 theorems) —
e = ∇P irrotational, circuital gravitational current, Poisson's equation,
potential-circuital, the gravitational speed μcv² = 1 ⟹ v = 1/√(μc) — build 8700 jobs clean.
T8 COMPLETE (2026-08-02, reframed): `MyProof/HeavisideMass.lean` (120 lines, 1 theorem)
— the Searle/Abraham excess-energy coefficient g(β) and the equatorial density ratio
(1−β²)⁻³ (the theorem); the γ = 1/√(1−β²) lemmas moved to `HeavisideMovingCharge` as
the equatorial-enhancement theorems (`enhancement_ge_one`, `enhancement_mono`) — γ is
Heaviside's field factor, NOT a mass; the γ-mass is Lorentz's deformable electron
(1899/1904).  The g(0) = 0 identity makes g the EXCESS over the rest energy, and the
attribution of the g-bracket is contested (Kaufmann's ψ writes it as Abraham's) —
flagged in the section below.
T9 COMPLETE (2026-08-02): `MyProof/HeavisideFractional.lean` (290 lines, 6 theorems) —
the heat kernel ∂G/∂t = D·∂²G/∂x² (fundamental solution), the cable form ∂G/∂t =
(1/KR)·∂²G/∂x², the unit-step derivative on both half-lines (the impulse is concentrated
at the jump); erfc is absent from the pinned mathlib (probe-verified with positive
control) so the kernel is the honest core — the erfc response is its accumulated
profile; build 8699 jobs clean.
Archived: the 8 compiling files above in the repo `heaviside-formalisation`.**

The nine targets are the readings of "the Heaviside equations": T1–T4 the classical four
(telegrapher, 4-vector field, operational calculus, moving charge), T5–T9 the added set
(energy flux, gravitoelectromagnetism, line constants, electromagnetic mass, fractional
operators + impulse). Heaviside's own notation is
kept in the dossier (p = d/dt; K = capacitance, S = leakance, c = permittivity, μ = inductivity).

---

## T1 — The telegrapher's equations (transmission line)

**Source:** EP1 Art. 28–30, "Electromagnetic Induction and Its Propagation" (*The Electrician*,
1885–87), pp. 429–560; Art. 20 "Contributions to the Theory of the Propagation of Current in
Wires" (1876), p. 141. Operator form confirmed at EP1 p. 153 area and line 12213/12240
(`(1 + CD(R + LD))`, `J₀(nl) = nl/k·J₀(nl)(R + LD)`).

**Statements (Heaviside's form):**
1. Line equations, with p = d/dt:
   −∂V/∂x = (R + Lp)·I, −∂I/∂x = (S + Kp)·V  (S = leakance, K = capacitance)
2. Second-order equation (the "telegrapher's equation"):
   ∂²V/∂x² = LK·∂²V/∂t² + (RK + LS)·∂V/∂t + RS·V
3. **Distortionless condition** R/L = S/K (equivalently RK = LS): the propagation constant
   factorises: m² = (R+Lp)(S+Kp) = (√(RS) + p√(LK))² — attenuation √(RS) and speed 1/√(LK)
   are frequency-independent, so the signal shape travels undistorted (EP1 pp. 429–430,
   the 1892 preface's "simplicity of treatment which the distortionless circuit allows").
4. **Finite speed** (Heaviside's 1887 anti-Kelvin result): with L ≠ 0 the line has a finite
   signal speed 1/√(LK); Kelvin's diffusion theory (L = 0) gives infinite speed (EP2 p. 492:
   "mathematical fiction, nothing else being propagated at the infinite speed").
5. Travelling-wave solutions: V(x,t) = e^{−αx}·F(t − x/v) + e^{+αx}·G(t + x/v), α = √(RS),
   v = 1/√(LK), satisfy the system under RK = LS (shape preservation).

**Formalisation plan:** two-variable scalar functions V, I : ℝ → ℝ → ℝ with pd1/pd2 partial
derivatives (deriv of sections, as in CoulombShift.lean). T1.2 is pure calculus from the two
line-equation premises + a Schwarz cross-partial premise. T1.3 is pure algebra: the identity
(√(RS) + p√(LK))² = (R+Lp)(S+Kp) under RK = LS (ring + sqrt, nonneg premises).
T1.5 needs the chain rule twice — the derivative-chain discipline already banked.

**Gap map:** none — ℝ calculus, deriv, ring all in the pin. **Ready now.**

---

## T2 — Heaviside's 4-vector form of the field equations

**Source:** ET1 Ch. III "The Electromagnetic Field" (1893):
- (4) `curl H₁ = J` — "The electric current is the curl of the magnetic force" (p. 108 area)
- (5) `−curl E₁ = G` — "The magnetic current is the negative curl of the electric force"
- (19) `curl H = J + j` with j = curl h (magnetisation current)
- Full system (1)–(2): `curl (H − h₀ − h) = J = C + Ḋ + up`,
  `−curl (E − e₀ − e) = G = K + Ḃ + wσ` (conduction + displacement-rate + convection)
- Divergence statements: "the divergence of the displacement measures the density of the
  electrification" (div D = ρ); "the induction… is purely a circuital flux" (div B = 0)
- The three-laws test on EP2 p. 495: (1) Faraday, (2) Maxwell/Ampere, (3) continuity of
  displacement — "Since (A) and (B) satisfy these tests, they are correct."

**Formalisation plan:** V3 := Fin 3 → ℝ machinery from VectorCalculus.lean. As in the O-Animator
corpus, the curl/div differential identities are explicit premises (HcurlGrad, HdivCross etc.
— mathlib has no curl). Theorems:
- the two curl equations as definitions; `div (curl H) = div J = 0` (total current is circuital)
- free-space wave equation: from the curl pair + div E = 0, `∇²E = με·∂²E/∂t²` via the
  curl-curl = grad-div − ∇² identity (premise-structured, like KnotField/NeumannDebye)
- the circuital induction statement: B solenoidal ⟹ B = curl A (Helmholtz, premise)
- the three-laws consistency test as a theorem about the moving-charge field (bridges T2/T4)

**Gap map:** none beyond the banked premise machinery. **Ready now.**

---

## T3 — The operational calculus and the step function

**Sources:** ET2 §282–283 "The Expansion Theorem" (pp. 126–130); ET3 Ch. 9 §§478–490
("The Operational Solution in General" p. 78; "Algebrisation of the Operational Solution"
§483, Jan 18 1901); EP2 p. 500 ("p⁻¹ meaning integration from 0 to t"; "disturbances cannot
travel faster than at speed v" as a consequence).

**Statements:**
1. p = d/dt as an algebraic symbol; p⁻¹ = ∫₀ᵗ (EP2 p. 500: "p⁻¹ meaning integration from 0
   to t with respect to t").
2. The step function: u(t) = 1 for t > 0, 0 for t < 0. Operationally the unit step is
   "1/p" — a steady e "beginning at the moment t = 0" (ET2 §282) is e·u(t), and the
   operational image of u is 1/p. ET3 §483: a charge Q passing the origin at t = 0 is
   "Q₀ = Q/p operationally expressed" — the travelling-charge bridge to T4.
3. **The expansion theorem** (ET2 §282, pp. 126–130): θ = Z·e operational solution, e steady
   from t = 0; the current is C = θ/Z, and over the roots pᵢ of Z(p) = 0 Heaviside's form
   is C = e/Z(0) + Σᵢ e·e^{pᵢt}/(pᵢ·Z′(pᵢ)) — the residue form (the displayed numerator is
   the applied e, not Zᵢ; the steady term is e/Z(0)). Algebraic core (rational Z = Q/P,
   distinct roots pᵢ, P(0) ≠ 0):
   `Q(p)/(p·P(p)) = Q(0)/(p·P(0)) + Σᵢ Q(pᵢ)/(pᵢ·P'(pᵢ)·(p − pᵢ))` — the partial-fraction
   identity whose inverse image is the sum of normal modes.  The identity requires the
   proper-rational hypotheses: deg Q < deg P + 1 (no polynomial part) and pᵢ ≠ 0 alongside
   P(0) ≠ 0 (the steady term's pole is simple).  The kernel-verified instance (quadratic
   numerator, two nonzero poles) satisfies them.
4. Normal-mode integration: the image of (p − pᵢ)⁻¹ is e^{pᵢt}·(unit step); image of p⁻¹ is
   the unit step — the "operational ↔ function" correspondence.

**Formalisation plan:** honest boundary — no Laplace transform in the pin, so no attempt to
formalise the full operational calculus as analysis. Instead:
- the step function via `Set.indicator (Set.Ioi 0)`: u, u·1 = 1 on (0,∞), the switching
  property; the distributional identity u′ = δ via the δ-smearing adjoint already proved in
  `DistributionLaws.lean` (premise-structured: ⟨u′, f⟩ = −⟨u, f′⟩ = f(0) = ⟨δ, f⟩)
- the partial-fraction identity as **pure algebra** over ℝ (Polynomial API): prove the
  two-pole case 1/((p−a)(p−b)) decomposition by hand; general distinct-roots statement as a
  Finset-sum identity (or premise-structured if mathlib's polynomial API resists)
- the expansion theorem statement with the correspondence rules as explicit premises
  (p⁻¹ ↦ step, (p−pᵢ)⁻¹ ↦ e^{pᵢt}) — mirrors the corpus's premise-discipline.

**Gap map:** partial fractions over ℝ — partial (Polynomial API present; distinct-roots
decomposition likely needs proving or premise-structuring). Laplace — absent (by design).

---

## T4 — The field of a uniformly moving charge

**Sources:** EP2 "Electromagnetic Waves, etc." (The Electrician 1888–89), pp. 492–515;
companion paper "On the Electromagnetic Effects due to the Motion of Electrification through
a Dielectric" (Phil. Mag. April 1889). Formula page: EP2 p. 495.

**Statements (EP2 p. 495, rationalised units; axis of z the motion line, charge q at speed u):**
1. (A) Electric force, radial from the charge, with c = permittivity:
   cE = q·(1 − u²/v²) / (r²·(1 − u²sin²θ/v²)^(3/2)) — the **Heaviside ellipsoid**:
   field lines stay straight (radial), compressed along the motion.
2. (B) Magnetic force: H = c·E·u·sinθ — circles about the axis; "The two forces are
   perpendicular" (E·H = 0).
3. Speed condition: μcv² = 1, i.e. v = 1/√(με) — the propagation speed of the medium.
4. The three laws test: (A), (B) satisfy Faraday, Maxwell/Ampere, continuity (EP2 p. 495).
5. Small-speed limit: J.J. Thomson's solution — uniform radial displacement, magnetic field
   of a current-element of moment qu.
6. u → v: the field concentrates in the equatorial plane θ = ½π (numerator → 0, denominator
   → (1 − sin²θ)^(3/2) = cos³θ); at u = v, a plane wave sheet (EP2 p. 496).
7. u > v: the disturbance is confined to a cone with sin θ = v/u (the superluminal cone,
   EP2 p. 494) — Heaviside flagged this case as unconfirmed ("at present unconfirmed",
   p. 496; the Phil. Mag. 1889 paper revisited it).

**Formalisation plan:** V3 + dot machinery. The field formulas as definitions (β = u/v,
E(r,θ) = q(1−β²)/(r²(1−β²sin²θ)^{3/2}) along the radial unit vector, H perpendicular).
Theorems: E·H = 0 (scalar-triple-product — banked in MultipoleSymmetry.lean); the
flattening factor (1−β²sin²θ)^{−3/2} ≥ 1 with equality iff sin θ = 0 (ellipsoid geometry);
the equatorial/axial field ratio (1−β²)^{−3/2}; the cone statement sin θ = v/u with β > 1
(geometry: the cone angle exists iff u > v). The derivation from Maxwell (retarded
potentials) is beyond the pin — premise-structured, exactly like the corpus's
Neumann–Debye/Hopf treatment.

**Gap map:** V3 dot/norm, Real.sin — all present. **Ready now.**

---

## T5 — The energy-flux theorem (Heaviside–Poynting)

**Sources:** ET1 §52–56 "The Poynting Flux" (1893, pp. 96–105 area; djvu 5551–5787: "found by
Prof. Poynting [Phil. Trans., 1884, Pt. 2], and independently [by myself]"); EP1 line 103
("developed by Poynting and myself from Maxwell's theory"); ET1 line 26888 ("VEH found by
Poynting and myself" — the V×H flux); the 1884–85 *Electrician* papers "The Energy of the
Current" (EP1).

**Statement:** the energy flux across unit area is the vector product of the electric and
magnetic forces, W = V×H (Heaviside's notation; S = E×H in modern). Heaviside derived it
independently of Poynting (1884–85, published in his 1885–87 series; Poynting 1884 Phil.
Trans. Pt. 2). Energy balance: −∂(energy density)/∂t = div(E×H) + J·E (flux out + work on
matter).

**Formalisation plan:** the O-Animator corpus already has `PoyntingFlux.lean` (per the
dossier's own cross-link) — reuse/extend it. The premise-structured balance equation:
given the curl pair and Ohm's law, div(E×H) + ∂U/∂t + J·E = 0 with U the field energy
density — the honest core is the divergence identity (HdivCross machinery) plus the
energy-density definition.

## T6 — Gravitoelectromagnetism (1893)

**Sources:** ET1 Ch. IX "A Gravitational and Electromagnetic Analogy" (1893; TOC djvu 1434,
pp. 455–466 area). The most self-contained item on the list: a genuine standalone system.

**Statement:** the Maxwell-analogue for gravity. In Heaviside's analogy the gravitational
force field g plays the role of E, with a companion "gravitomagnetic" field k (modern form):
div g = −4πGρ,  curl g = −∂k/∂t,  div k = 0,  curl k = −(4πG/c²)·ρv + (1/c²)·∂g/∂t.
Heaviside's own presentation is the four equations of the field with the gravitational
"magnetic" term — the static case reduces to the inverse-square law (the point of the
analogy: gravitation as a circuital-flux system).

**Formalisation plan:** premise-structured V3 system mirroring T2 exactly (the curl pair +
divergence premises from VectorCalculus.lean); theorems: consistency (div curl g = 0, the
circuital companion), the static reduction div g = −4πGρ ⟹ inverse-square radial field for a
point mass (with the divergence-theorem premise), the analogue statements side-by-side with
T2's (the "same equations, different constants" structure — Heaviside's point).

## T7 — Line constants: propagation constant and characteristic impedance

**Sources:** EP1 telegrapher series (1885–87); the standard forms γ = √((R+jωL)(G+jωC)),
Z₀ = √((R+jωL)/(G+jωC)). Corollaries of T1's operator algebra with p = jω.

**Statement:** in the harmonic regime p = jω, the propagation constant γ and the
characteristic impedance Z₀ satisfy: γ² = (R+jωL)(G+jωC), Z₀² = (R+jωL)/(G+jωC), and the
consistency Z₀·γ = R+jωL (equivalently Z₀ = (R+jωL)/γ — the impedance is the ratio of
voltage to current wave amplitudes).

**Formalisation plan:** pure ℂ algebra (Complex.instField in the pin). Theorems: the two
squared identities as definitions, the cross-consistency Z₀·γ = R+jωL proved from them by
ring (with the square-root-of-product identity √a·√b = √(ab) under the branch conventions as
a premise or in the argument form), the distortionless specialisation γ = α + jβ with
α = √(RS), β = ω√(LK) (T1's factorisation in harmonic form).

## T8 — The field energy and momentum of the moving charge (1889/1897)

**Sources:** EP2 "On the Electromagnetic Effects due to the Motion of Electrification
through a Dielectric" (Phil. Mag. April 1889; EP2 djvu 796, pp. 494–512 area). Adjacent to
T4 (the same moving-charge field) but a separate claim: the field carries momentum, and
its energy depends on the speed in a way that behaves like a velocity-dependent mass.

**Attribution (the framing IS the claim in a transcription dossier):** the γ = 1/√(1−β²)
that appears in T4 is Heaviside's own 1889 EQUATORIAL FIELD ENHANCEMENT (E = qγ/r² at
θ = π/2) — a field factor, NOT a mass formula.  The γ-shaped mass is Lorentz's deformable
electron (1899/1904).  Heaviside's field energy is instead the excess coefficient
g(β) = (1+β²)/(2β)·ln((1+β)/(1−β)) − 1, with W(β) = W₀·(1 + g(β)) (g(0) = 0, so g is the
EXCESS over the rest energy W₀, not the total).  Attribution of the g-bracket is
contested in the secondary literature: Kaufmann's ψ(β) = g(β)/β² writes it as ABRAHAM's,
introduced precisely as the correction to Searle's field-energy formula — checked against
the primary sources before the label hardens (see the status block).

**Formalised:** `searleCoefficient` (the g-bracket, named with the contestable-attribution
flag), `movingEnergyRatio` (the excess-energy statement), `equatorial_density_ratio` — the
(1−β²)⁻³ density concentration from the T4 field (the theorem), and `MomentumAlongMotion`
(the momentum-direction statement).  The small-speed limit lim g(β)/β² = 4/3 is the
planned next theorem (the Kaufmann m/m₀ = (3/4)·ψ(β) normalization's exactness at β = 0).

## T9 — Fractional operators and the impulse function

**Sources:** ET2 §223–230 "On Operators in Physical Mathematics" (fractional
differentiations; djvu 3577–3589: "the direction of fractional differentiation"); ET2
§274–278 (the impulse function; djvu 5116–5396: "The idea of an impulse is well known… the
strength of the impulse for the intensity"); ET3 §483 (Q₀ = Q/p).

**Statement:** (a) p^½ in the operational calculus — the diffusive (cable) equation
∂V/∂t = (1/KR)·∂²V/∂x² solves with the complementary error function, erfc — Heaviside's
fractional operator p^½ = d^½/dt^½ acting on the cable response; (b) the impulse function
obtained by differentiating the unit step u′(t) — the δ function, three decades before
Dirac (ET2 §274–278 is 1893–95; Dirac 1926–27; the impulse had Kirchhoff/Cauchy
antecedents); the operational identity p·u = δ ("p·1 = impulse").

**Formalisation plan (as executed):** (a) the kernel-verified core is the heat kernel
G = exp(−x²/4Dt)/(2√(πDt)) with ∂G/∂t = D·∂²G/∂x² — the pinned mathlib has NO erfc
(probe-verified: positive control `Real.sqrt` resolves; `Real.erfc`, `Real.erf`,
`Gaussian`, `pdfNormal`, `Real.gaussian` all unknown; file-level search of `Mathlib/`
finds no erfc; the Gaussian density `gaussianPDFReal` in
`Probability/Distributions/Gaussian/Real.lean` exists but no CDF/erfc is defined on it).
The cable response erfc(x/(2√(Dt))) is the accumulated kernel profile (the x-antiderivative
of a heat-equation solution is again a heat-equation solution).  The correspondence is
NOT "p^½ ↦ erfc": the erfc is the operational image of e^{−x√(pRK)}/p — the
exponential-of-the-half-power, not of p^½ itself; (b) the
impulse as the distributional derivative of the step: ⟨u′, f⟩ = −⟨u, f′⟩ = f(0) = ⟨δ, f⟩
via the δ-adjoint in `DistributionLaws.lean` (T3's cross-link, now made explicit);
(c) the operational bridge p^½ ↦ erfc documented as the correspondence rule (the Laplace
transform is absent from the pin — statement-level, like T3).

---

## Execution order (completion log — dated; the live status is the block at the top)

1. **T1** DONE (2026-08-01) — ℝ calculus + algebra; the operator notation R + Lp introduces p.
2. **T3** DONE (2026-08-01) — step function + partial fractions + normal-mode ODE (the
   expansion theorem's algebraic core).
3. **T2** DONE (2026-08-01) — V3 machinery, HcurlGrad/HdivCross premises.
4. **T4** DONE (2026-08-02) — V3 + trig; the ET3 §483 Q₀ = Q/p link to T3; the field feeds T8.
5. **T7** DONE (2026-08-02) — pure ℂ algebra corollary of T1.
6. **T6** DONE (2026-08-02) — the GEM system: T2's structure with different constants.
7. **T5** DONE (2026-08-02) — energy flux: the flux definition + the Poynting balance.
8. **T8** DONE (2026-08-02) — the field-energy lemmas (see the T8 framing note below).
9. **T9** DONE (2026-08-02) — the heat kernel + the impulse half-line derivatives.

All nine targets complete as of 2026-08-02.
---

## Weight classes and verification gates

**Weight-class tagging** (50 theorems; (a) definition/restatement, (b) algebra/calculus
identity, (c) derivation from premises):

- **(a) 3** — `unitStep_pos`, `unitStep_neg`, `unitStep_add_neg` (indicator evaluations).
- **(b) 25** — T1 `distortionless_factorisation`, `distortionless_finite_speed`; T3
  `expansion_two_pole_const`, `expansion_two_pole_poly2`; T4 `field_perpendicular`,
  `field_axial`, `field_equatorial`, `equatorial_over_axial`, `equatorial_ratio_ge_one`,
  `flattening_ge_one`, `speed_condition`, `cone_angle`, `enhancement_ge_one`,
  `enhancement_mono`; T7 `sqrt_sq`, `gamma_sq`, `z0_sq`, `z0_ratio_sq`,
  `impedance_ratio_consistency`, `distortionless_square`, `phase_velocity`;
  T5 `flux_perp_E`, `flux_perp_H`; T8 `equatorial_density_ratio`; T9 `cable_equation`
  (instantiation).
- **(c) 22** — T1 `telegrapher_second_order_V`, `distortionless_wave_solution`; T2 all six
  (`current_circuital`, `potential_is_circuital`, `total_current_circuital`,
  `continuity_from_circuital`, `free_wave_equation`, `induction_circuital_of_continuity`);
  T3 `exp_solves_ode`; T4 `moving_charge_induction_circuital`; T5 `flux_divergence`,
  `poynting_balance`; T6 all five; T9 `heat_kernel_x_deriv`, `heat_kernel_xx_deriv`,
  `heat_kernel_heat_equation`, `deriv_unitStep_pos`, `deriv_unitStep_neg`.

**Consistency witnesses (vacuity gate).** Every premise bundle is premise-structured, so a
contradictory bundle would prove everything while the build stays green.  Gate: a concrete
instantiation per bundle — T1/T7 the distortionless line (R = 1, L = 2, S = 3, K = 6 with
RK = LS, and F = exp as the smooth profile); T4 the explicit ellipsoid field with concrete
numbers (r = 1, u = 1, v = 2); T2/T5 zero-field and the plane-wave profile (the premises
are the curl pair — any differentiable field pair instantiates them); T3 the concrete
rational Q/P with the two nonzero poles; T8 the concrete β = 1/2; T9 the kernel with
D = 1, x = 1, t = 1.  Compiling witnesses certify satisfiability of the bundles used.
A `Witnesses.lean` file with these instantiations is the planned next addition.

**Non-triviality spot-checks.**  Deleting a physics premise breaks the proof: dropping
`hRK` (the distortionless condition) from `distortionless_factorisation`, dropping `hampere`
from `free_wave_equation`, or dropping `hβ` from `speed_condition` each leaves the goal
unprovable — the premises are load-bearing, not decorative.

**Notation table** (the corpus's symbols; Heaviside's own letters):

| symbol | meaning | used in |
|---|---|---|
| V, I | voltage, current on the line | T1, T7 |
| R | resistance per unit length | T1, T7, T9 |
| L | inductance per unit length | T1, T7 |
| S | leakage (conductance) per unit length | T1 |
| K | capacitance per unit length | T1, T9 |
| G, C | conductance, capacitance (T7's line constants — collision with T2's C = conduction current, flagged) | T7 |
| c | permittivity (Heaviside's letter) | T2, T4, T5, T6 |
| μ | inductivity | T2, T4, T6 |
| p | the operational d/dt | T3, T9 |
| u(t) | the unit step | T3, T9 |
| γ, Z₀ | propagation constant, characteristic impedance | T7 |
| D | diffusivity 1/(KR) | T9 |
| G (T6) | Newton's constant — the gravitational analogue's coefficient | T6 |

**Conventions flagged by review.**  T6 formalises Heaviside's 1893 analogy, NOT
linearised-GR gravitoelectromagnetism — the gravitomagnetic normalisation differs by
convention from Lense–Thirring, and μ, c are reused as the gravitational analogues.
T4's `cone_angle` is the geometry only (the angle exists iff u > v); the confinement
claim itself (the disturbance sits behind the cone) is physical, not asserted.
T5's flux is Heaviside's VEH = E×H — V is the quaternion vector-part operator, not a
voltage field (the "V×H" reading collides with T1's V).
