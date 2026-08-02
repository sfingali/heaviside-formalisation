import Mathlib
import MyProof.VectorCalculus

/-!
# Heaviside corpus, T5: the energy-flux theorem (Heaviside–Poynting)

Sources: ET1 §52–56 "The Poynting Flux" (1893; the djvu text at 5551–5787):
"found by Prof. Poynting [Phil. Trans., 1884, Pt. 2], and independently [by
myself]"; ET1 line 26888: "VEH found by Poynting and myself" — the flux V×H;
EP1 line 103: the energy-current theorem "developed by Poynting and myself from
Maxwell's theory"; the 1884–85 *Electrician* papers on the energy of the current.

Statement: the energy flux across unit area is the vector product of the electric
and magnetic forces, W = E × H (Heaviside's V×H — "the energy current").  Derived
by Heaviside in the 1885–87 series, independently of Poynting (Phil. Trans. 1884).
The balance: with the curl pair and the divergence identity

  div(E × H) = H · curl E − E · curl H,

Faraday (−curl E = Ḃ...  the rate of increase of induction) and Maxwell
(curl H = J) give the Poynting balance

  div(E × H) = −(H·Ḃ + E·J)  —  flux divergence = − work on the field,

the local form of energy conservation (flux out + field work = 0; with the
energy density U = ½(μH² + cE²), ∂U/∂t = H·Ḃ + E·Ḋ, this is the full Poynting
theorem div W + ∂U/∂t + J·E = 0, whose rate terms are the premises here).

Formalised here: the flux definition, the perpendicularity of the flux to both
forces (W·E = W·H = 0 — the energy flows at right angles to the fields, along the
surfaces of constant energy), the divergence identity (HdivCross, re-exported in
Heaviside's framing), and the Poynting balance theorem.  The rate of the balance
(∂U/∂t) is the premise-structured part — the honest kernel core is the divergence
identity + the sign bookkeeping.
-/

namespace HeavisideEnergyFlux

open OAnimatorVector

/-- Heaviside's energy flux (the "energy current"):  W = E × H — "VEH found by
    Poynting and myself" (ET1); the rate of energy flow across unit area. -/
noncomputable def flux (E H : V3 → V3) : V3 → V3 :=
  fun x => cross3 (E x) (H x)

/-- The flux is perpendicular to the electric force: W·E = 0 — the energy flows at
    right angles to both fields, along the surfaces of constant energy. -/
theorem flux_perp_E (E H : V3 → V3) (x : V3) : dot3 (flux E H x) (E x) = 0 := by
  simp [flux, cross3, dot3, Fin.sum_univ_three]
  ring

/-- The flux is perpendicular to the magnetic force: W·H = 0. -/
theorem flux_perp_H (E H : V3 → V3) (x : V3) : dot3 (flux E H x) (H x) = 0 := by
  simp [flux, cross3, dot3, Fin.sum_univ_three]
  ring

/-- The divergence identity for the flux:  div(E × H) = H · curl E − E · curl H
    (the HdivCross product rule, in Heaviside's framing). -/
theorem flux_divergence (E H : V3 → V3) (hdc : HdivCross) :
    div3 (fun x => cross3 (E x) (H x))
      = fun x => dot3 (H x) (curl3 E x) - dot3 (E x) (curl3 H x) :=
  hdc E H

/-- The Poynting balance: with Faraday's law (curl E = −Ḃ, the magnetic current of
    T2's (5)) and Maxwell's law (curl H = J, T2's (4)),
    div(E × H) = −(H·Ḃ + E·J) — the flux divergence equals the negative of the work
    on the field (the local form of energy conservation; the rate of the stored
    energy is the premise part). -/
theorem poynting_balance (E H Bdot J : V3 → V3)
    (hdc : HdivCross)
    (hfaraday : ∀ x, curl3 E x = -(Bdot x))
    (hmaxwell : ∀ x, curl3 H x = J x) :
    ∀ x, div3 (fun y => cross3 (E y) (H y)) x = -(dot3 (H x) (Bdot x) + dot3 (E x) (J x)) := by
  intro x
  calc
    div3 (fun y => cross3 (E y) (H y)) x
        = dot3 (H x) (-(Bdot x)) - dot3 (E x) (J x) := by
          simpa [hfaraday, hmaxwell] using congrFun (hdc E H) x
    _ = -(dot3 (H x) (Bdot x) + dot3 (E x) (J x)) := by
          have hneg : dot3 (H x) (-(Bdot x)) = -(dot3 (H x) (Bdot x)) := by
            simp [dot3]
          rw [hneg]
          ring

end HeavisideEnergyFlux
