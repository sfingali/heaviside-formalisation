import Mathlib
import MyProof.VectorCalculus
import MyProof.HeavisideField
import MyProof.HeavisideMovingCharge

/-!
# Heaviside corpus, T6: the gravitoelectromagnetic analogy (1893)

Heaviside, *Electromagnetic Theory* Vol. 1 (1893), Ch. IX "A Gravitational and
Electromagnetic Analogy" (pp. 455–466; the section text at ET1 djvu 26760–27030).
The analogy runs Maxwell's machinery for gravitation: the gravitational force field
e plays the role of the electric force, with a companion "gravitomagnetic" force h
(the analogue of the magnetic force), and the same circuital laws with different
constants.  Heaviside's own equations:

  (2)   e = ∇P            — the gravitational force is the space-variation of a
                            potential (Newton's law through Poisson's equation);
  (5bis) curl h = ρu − cė  — the first circuital law: the curl of the gravitomagnetic
                            force is the matter current ρu minus the displacement-rate;
  (17)  curl e = μḣ        — the second circuital law, forced by the hypothesis of
                            propagation at finite speed ("this, of course, might be
                            inferred from the electromagnetic case");
  μcv² = 1                 — the speed condition (p. 461 area): gravitational
                            disturbances travel at the finite speed v = 1/√(μc)
                            ("disturbances travel at speed v", the Poisson footnote).

Heaviside also derives the energy statements: ½ce² per unit volume is the "exhaustion
of potential energy", and the flux of energy depends on the gravitomagnetic force —
the gravitational Poynting flux W = e × h (the T5 cross-link).

Formalised here (premise-structured V3, mirroring T2 exactly — "the same equations,
different constants" is the point of the analogy):
  1. `GravForceOfPotential` (2), `DivForceLaw` (Newton/Poisson), the two circuital
     laws `GravCurrentLaw` (5 bis) and `GravFaradayLaw` (17), `CircuitalFlux`.
  2. `grav_force_irrotational` — e = ∇P forces curl e = 0 (the HcurlGrad identity).
  3. `grav_current_circuital` — a current that is the curl of h is circuital.
  4. `poisson_from_laws` — e = ∇P with div e = −4πGρ is Poisson's equation for P.
  5. `grav_potential_circuital` — the gravitomagnetic force from a vector potential
     is a circuital flux (the analogue of T2's potential_is_circuital).
  6. `gem_speed_condition` — μcv² = 1 gives v = 1/√(μc): the gravitational wave
     speed, the SAME law as T1's line, T2's field, T4's moving charge.
  7. `energyFlux` — the gravitational energy flux W = e × h (the T5 bridge).
-/

namespace HeavisideGEM

open OAnimatorVector
open HeavisideField

/-- (2): the gravitational force is the space-variation of a potential. -/
def GravForceOfPotential (e : V3 → V3) (P : V3 → ℝ) : Prop :=
  ∀ x, e x = grad3 P x

/-- Newton's law through Poisson: div e = −4πGρ (the gravitational force density is
    the divergence of the force field; the sign is the attraction convention). -/
def DivForceLaw (e : V3 → V3) (ρ : V3 → ℝ) (G : ℝ) : Prop :=
  ∀ x, div3 e x = -(4 * Real.pi * G) * ρ x

/-- (5 bis): the first circuital law — the curl of the gravitomagnetic force is the
    total gravitational current Jg (matter current ρu plus the displacement-rate
    c·ė, in the same notation as T2's TotalCurrent). -/
def GravCurrentLaw (h Jg : V3 → V3) : Prop :=
  ∀ x, curl3 h x = Jg x

/-- (17): the second circuital law — the curl of the gravitational force is the rate
    of increase of the gravitomagnetic induction (Heaviside: "leads to a second one,
    namely (17), if we introduce the hypothesis of propagation at finite speed"). -/
def GravFaradayLaw (e hdot : V3 → V3) (μ : ℝ) : Prop :=
  ∀ x, curl3 e x = μ • hdot x

/-- The gravitomagnetic force is a circuital flux: div h = 0 (the analogue of
    "the induction is purely a circuital flux" of T2). -/
def CircuitalFlux (h : V3 → V3) : Prop :=
  ∀ x, div3 h x = 0

/-- A gravitational force derived from a potential is irrotational: curl e = 0
    (the consistency of (2) with the first circuital law — the static force field
    of Newton's law has no circulation). -/
theorem grav_force_irrotational (e : V3 → V3) (P : V3 → ℝ)
    (hpot : GravForceOfPotential e P) (hcg : HcurlGrad) :
    ∀ x, curl3 e x = 0 := by
  intro x
  have he : e = grad3 P := by
    funext y
    exact hpot y
  rw [he]
  unfold HcurlGrad at hcg
  have h : curl3 (grad3 P) = 0 := hcg P
  simpa using congrFun h x

/-- The gravitational current is circuital: div Jg = div(curl h) = 0 — the analogue
    of T2's current_circuital ("the current is circuital"). -/
theorem grav_current_circuital (h Jg : V3 → V3) (hcur : GravCurrentLaw h Jg)
    (hdc : ∀ F : V3 → V3, div3 (curl3 F) = 0) :
    CircuitalFlux Jg := by
  intro x
  have hJ : Jg = curl3 h := by
    funext y
    exact (hcur y).symm
  calc
    div3 Jg x = div3 (curl3 h) x := by rw [hJ]
    _ = 0 := by simpa using congrFun (hdc h) x

/-- Poisson's equation: with e = ∇P and div e = −4πGρ, the potential satisfies
    ∇²P = −4πGρ — Newton's law in field form. -/
theorem poisson_from_laws (e : V3 → V3) (P : V3 → ℝ) (ρ : V3 → ℝ) (G : ℝ)
    (hpot : GravForceOfPotential e P) (hdiv : DivForceLaw e ρ G) :
    ∀ x, div3 (grad3 P) x = -(4 * Real.pi * G) * ρ x := by
  intro x
  have he : e = grad3 P := by
    funext y
    exact hpot y
  calc
    div3 (grad3 P) x = div3 e x := by rw [he]
    _ = -(4 * Real.pi * G) * ρ x := hdiv x

/-- The gravitomagnetic force from a vector potential is a circuital flux:
    h = curl A forces div h = 0 — the analogue of T2's potential_is_circuital
    ("A finds H" in the gravitational setting). -/
theorem grav_potential_circuital (A h : V3 → V3) (hA : ∀ x, curl3 A x = h x)
    (hdc : ∀ F : V3 → V3, div3 (curl3 F) = 0) :
    CircuitalFlux h :=
  potential_is_circuital A h hA hdc

/-- The gravitational wave speed:  μcv² = 1  ⟹  v = 1/√(μc) — Heaviside's speed
    condition of Ch. IX ("disturbances travel at speed v"), the SAME law as the
    telegrapher's line (T1), the field equations (T2) and the moving charge (T4):
    the analogy carries the propagation law unchanged. -/
theorem gem_speed_condition (μ c v : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hv : 0 ≤ v)
    (h : μ * c * v ^ 2 = 1) :
    v = 1 / Real.sqrt (μ * c) :=
  HeavisideMovingCharge.speed_condition μ c v hμ hc hv h

/-- The gravitational energy flux:  W = e × h — Heaviside's flux of gravitational
    energy "depends upon the magnetic force as well" (the T5 bridge: the same
    e × h structure as the electromagnetic Poynting flux). -/
noncomputable def energyFlux (e h : V3 → V3) : V3 → V3 :=
  fun x => cross3 (e x) (h x)

/-- The gravitational energy density: ½ce² per unit volume — the "exhaustion of
    potential energy" of the Ch. IX energy account. -/
noncomputable def energyDensity (c : ℝ) (e : V3 → V3) : V3 → ℝ :=
  fun x => (1 / 2 : ℝ) * c * dot3 (e x) (e x)

end HeavisideGEM
