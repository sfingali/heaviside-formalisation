# Heaviside in Lean — a kernel-verified formalisation corpus

Lean 4.33.0-rc1 + mathlib pin `f4570dc2f3c801ed0c0edd5867f943e2b84e4dec`.
A dossier-style formalisation of the equations of Oliver Heaviside (1850–1925),
public domain.  Physics lives in the premises; the kernel checks the model's logic.
Every theorem is kernel-verified (`#print axioms` = `[propext, Classical.choice, Quot.sound]` — no sorry, no axiom).

**Status: T1–T9 complete (51 theorems, 9 files, `lake build` green).**

Build: `lake build MyProof.HeavisideTelegrapher` (and the sibling modules).  The
O-Animator dependency files (`VectorCalculus`, `DistributionLaws`) are vendored in
`MyProof/` so the repo is self-contained at the pinned mathlib.
# Heaviside Formalisation Dossier

Status 2026-08-01. Corpus: `/opt/data/home/projects/heaviside/papers/` (5 volumes, archive.org).
Env: `/opt/data/lean-demo` — Lean 4.28.0, mathlib `8f9d9cff` (same pin as O-Animator/Joshi).
Method: per-claim kernel verification; physics in the premises, theorems about the model's logic;
statements transcribed from the PDF pages, locators by print page.

**Status: T1 COMPLETE (2026-08-01, kernel-verified 0/0, axioms = propext/Classical.choice/Quot.sound).
`MyProof/HeavisideTelegrapher.lean` (318 lines, 5 theorems) — full build 8697 jobs clean.
T2 COMPLETE (2026-08-01): `MyProof/HeavisideField.lean` (197 lines, 6 theorems) —
the curl pair (4)/(5), circuital current, potential-is-circuital, total-current + continuity,
the free-space wave equation ΔE = μc·∂²E/∂t², the three-laws bridge — build 8698 jobs clean.
T3 COMPLETE (2026-08-01): `MyProof/HeavisideOperational.lean` (128 lines, 6 theorems) —
unit step via Set.indicator (pos/neg/switching-pair), the expansion-theorem partial fractions
(two-pole unit response + quadratic numerator, kernel-verified by field_simp/ring),
exp_solves_ode (the normal-mode correspondence) — build 8697 jobs clean.
T4 COMPLETE (2026-08-01): `MyProof/HeavisideMovingCharge.lean` (193 lines, 9 theorems) —
the spherical frame, (A)/(B) magnitudes, E·H = 0 perpendicularity, axial/equatorial closed
forms + ratio, flattening factor ≥ 1, μcv² = 1 speed condition, the superluminal cone
θ = arcsin(v/u), the circuital-flux bridge to T2 — build 8699 jobs clean.
T7 COMPLETE (2026-08-01): `MyProof/HeavisideLineConstants.lean` (175 lines, 7 theorems) —
γ² = (R+jωL)(G+jωC), Z₀² = (R+jωL)/(G+jωC), the ratio form (Z/γ)² = Z/Y, the cpow
squared-sqrt identity (branch-bounded), the distortionless harmonic factorisation
(√(RS)+jω√(LK))², phase velocity 1/√(LK) — build 8698 jobs clean.
T5 COMPLETE (2026-08-01): `MyProof/HeavisideEnergyFlux.lean` (74 lines, 3 theorems) —
W = E×H flux def, perpendicularity to both forces, the Poynting balance
div(E×H) = −(H·Ḃ + E·J) — build 8698 jobs clean.
T6 COMPLETE (2026-08-01): `MyProof/HeavisideGravitomagnetic.lean` (145 lines, 5 theorems) —
e = ∇P irrotational, circuital gravitational current, Poisson's equation,
potential-circuital, the gravitational speed μcv² = 1 ⟹ v = 1/√(μc) — build 8700 jobs clean.
T8 COMPLETE (2026-08-01): `MyProof/HeavisideMass.lean` (118 lines, 3 theorems) —
mass factor 1/√(1−β²) ≥ 1, strictly monotone in β, equatorial density ratio
(1−β²)⁻³ — build 8701 jobs clean.
T9 IN PROGRESS (2026-08-01): `MyProof/HeavisideFractional.lean` — heat kernel
∂G/∂t = D·∂²G/∂x² (erfc absent from the pinned mathlib — the kernel is the honest core);
NOT yet in the repository build.
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
3. **The expansion theorem** (ET2 §282): θ = Z·e operational solution, e steady from t = 0;
   "the C due to e is expressed by C = (Z₀/p)·e + Σ Zᵢ/(pᵢ·(dZ/dp)|ᵢ)·e^{pᵢt}·e" over the roots
   pᵢ of Z(p) = 0. Algebraic core (rational Z = Q/P, distinct roots pᵢ, P(0) ≠ 0):
   `Q(p)/(p·P(p)) = Q(0)/(p·P(0)) + Σᵢ Q(pᵢ)/(pᵢ·P'(pᵢ)·(p − pᵢ))` — the partial-fraction
   identity whose inverse image is the sum of normal modes.
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
the equatorial/axial field ratio (1−β²); the cone statement sin θ = v/u with β > 1
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

## T8 — Electromagnetic mass and momentum (1889)

**Sources:** EP2 "On the Electromagnetic Effects due to the Motion of Electrification
through a Dielectric" (Phil. Mag. April 1889; EP2 djvu 796, pp. 494–512 area). Adjacent to
T4 (the same moving-charge field) but a separate claim: the field carries momentum, and
its energy grows with speed exactly like the kinetic energy of a mass that increases with
velocity — the first velocity-dependent "electromagnetic mass".

**Statement (Heaviside's form):** for the moving charge, the electromagnetic momentum of the
field is parallel to the motion and its energy has the form E = (mass)·v²/2-style
coefficient m(v) = m₀/√(1 − v²/c²)-like (the field mass rises with speed; Heaviside's
expressions carry the 4/3-type coefficient of the electrostatic energy).

**Formalisation plan:** from the T4 field definitions — the field-momentum integral and the
energy coefficient as definitions; the honest theorems: the momentum is along the motion
(symmetry — banked MultipoleSymmetry-style argument), the energy coefficient's dependence
on β = u/v through the factor 1/√(1−β²) (the relativistic factor as a real calculus
identity), the small-speed limit giving the rest-mass coefficient.

## T9 — Fractional operators and the impulse function

**Sources:** ET2 §223–230 "On Operators in Physical Mathematics" (fractional
differentiations; djvu 3577–3589: "the direction of fractional differentiation"); ET2
§274–278 (the impulse function; djvu 5116–5396: "The idea of an impulse is well known… the
strength of the impulse for the intensity"); ET3 §483 (Q₀ = Q/p).

**Statement:** (a) p^½ in the operational calculus — the diffusive (cable) equation
∂V/∂t = (1/KR)·∂²V/∂x² solves with the complementary error function, erfc — Heaviside's
fractional operator p^½ = d^½/dt^½ acting on the cable response; (b) the impulse function
obtained by differentiating the unit step u′(t) — the δ function a quarter-century before
Dirac; the operational identity p·u = δ ("p·1 = impulse").

**Formalisation plan:** (a) the honest kernel-verifiable core: the diffusion equation and
the erfc solution — ∂/∂t (erfc(x/(2√(D·t)))) = D·∂²/∂x² (erfc), with Real.erfc in the pin —
a genuine calculus theorem (the derivative-chain discipline already banked); (b) the
impulse as the distributional derivative of the step: ⟨u′, f⟩ = −⟨u, f′⟩ = f(0) = ⟨δ, f⟩
via the δ-adjoint in `DistributionLaws.lean` (T3's cross-link, now made explicit);
(c) the operational bridge p^½ ↦ erfc documented as the correspondence rule (the Laplace
transform is absent from the pin — statement-level, like T3).

---

## Execution order and cross-links

1. **T1** DONE — ℝ calculus + algebra; the operator notation R + Lp introduces p.
2. **T3** DONE — step function + partial fractions + normal-mode ODE (the expansion theorem's
   algebraic core).
3. **T2** DONE — V3 machinery, HcurlGrad/HdivCross premises from the O-Animator corpus.
4. **T4** NEXT — V3 + trig; the ET3 §483 Q₀ = Q/p link to T3; the three-laws test links to
   T2; the field feeds T8.
5. **T7** — the cheapest remaining: pure ℂ algebra corollary of T1.
6. **T6** — the GEM system: T2's structure with different constants (self-contained).
7. **T5** — energy flux: extend the O-Animator `PoyntingFlux.lean` (HdivCross machinery).
8. **T8** — electromagnetic mass: from the T4 field definitions.
9. **T9** — erfc solves the cable diffusion equation + the u′ = δ impulse identity.

Cross-links to existing corpus: `DistributionLaws.lean` (δ-adjoint for u′ = δ),
`VectorCalculus.lean` (V3, curl/grad/div premises), `MultipoleSymmetry.lean`
(BAC−CAB triple product), `PoyntingFlux.lean` (energy flux — T5's starting point),
`NeumannDebye.lean` (Helmholtz premise pattern), `KnotField.lean` (div-curl-consistency).
