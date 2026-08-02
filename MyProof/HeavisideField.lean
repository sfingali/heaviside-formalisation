import Mathlib
import MyProof.VectorCalculus

/-!
# Heaviside corpus, T2: the 4-vector form of the field equations

Heaviside, *Electromagnetic Theory* Vol. 1 (1893), Ch. III "The Electromagnetic Field".
The modern 4-vector form is Heaviside's compression of Maxwell's original 20 equations.
§36 (p. 110): "if J be the electric current and G the magnetic current, the two laws are

  curl H₁ = J        (4)          −curl E₁ = G        (5)

The electric current is the curl of the magnetic force.
The magnetic current is the negative curl of the electric force."

The divergence statements (p. 113): "the divergence of the displacement measures the
density of electrification"; "there is no evidence that the flux induction has any
divergence; it is purely a circuital flux".  The full system with matter
(pp. 115–116):  curl (H − h₀ − h) = J = C + Ḋ + uρ,  −curl (E − e₀ − e) = G = K + Ḃ + wσ.

Formalised here (physics in the premises; the kernel checks the model's logic):
  1. `CurlOfH`/`CurlOfE` — the two laws (4)/(5).
  2. `current_circuital` — a current that is the curl of a field is circuital (div J = 0):
     the "current is circuital" fact behind the continuity equation.
  3. `potential_is_circuital` — an induction derived from a vector potential A (B = curl A)
     is automatically a circuital flux (div B = 0) — Heaviside's "A finds H" (EP2 p. 505).
  4. `TotalCurrent` + `total_current_circuital` + `continuity_from_circuital` — the full
     system (1): J = C + Ḋ + uρ, circuital, and the continuity equation.
  5. `free_wave_equation` — the propagation result: from the curl pair with div E = 0 and
     the curl-curl identity,  ΔE = k·∂²E/∂t²  with k = μc (permittivity × inductivity).
     With the speed condition μcv² = 1 (EP2 p. 495 — T4), v = 1/√(μc) is the propagation
     speed of the medium — the same 1/√(LC) law as the telegrapher's equations (T1).
  6. `FaradayLaw`/`MaxwellLaw`/`ContinuityLaw` — the three laws of Heaviside's test
     (EP2 p. 495: "Since (A) and (B) satisfy these tests, they are correct") — the T2/T4 bridge.

Cross-links: the premise machinery (`HcurlGrad`, `HdivCross`, …) is `OAnimatorVector`
from the O-Animator corpus. The μcv² = 1 condition and the (A)/(B) field are T4.
-/

namespace HeavisideField

open OAnimatorVector

/-- The componentwise Laplacian of a vector field:  (ΔF)ᵢ = Σⱼ ∂ⱼ∂ⱼFᵢ. -/
noncomputable def laplacian3 (F : V3 → V3) : V3 → V3 :=
  fun x i => ∑ j, pd j (fun y => pd j (fun z => F z i) y) x

/-- Heaviside's (4): the electric current is the curl of the magnetic force. -/
def CurlOfH (H J : V3 → V3) : Prop :=
  ∀ x, curl3 H x = J x

/-- Heaviside's (5): the magnetic current is the negative curl of the electric force. -/
def CurlOfE (E G : V3 → V3) : Prop :=
  ∀ x, -curl3 E x = G x

/-- A field whose divergence vanishes everywhere: a circuital (solenoidal) flux. -/
def Circuital (B : V3 → V3) : Prop :=
  ∀ x, div3 B x = 0

/-- The current of the field law (4) is circuital: div J = div(curl H) = 0.  This is the
    "the current is circuital" fact — the local form of the continuity equation. -/
theorem current_circuital (H J : V3 → V3) (h : CurlOfH H J)
    (hdc : ∀ F : V3 → V3, div3 (curl3 F) = 0) :
    Circuital J := by
  intro x
  have hJ : J = curl3 H := by
    funext y
    exact (h y).symm
  calc
    div3 J x = div3 (curl3 H) x := by rw [hJ]
    _ = 0 := by simpa using congrFun (hdc H) x

/-- An induction derived from a vector potential (B = curl A) is automatically a circuital
    flux — Heaviside's "A finds H, irrespective of Ψ" (EP2 p. 505): the potential
    representation forces div B = 0. -/
theorem potential_is_circuital (A B : V3 → V3) (h : ∀ x, curl3 A x = B x)
    (hdc : ∀ F : V3 → V3, div3 (curl3 F) = 0) :
    Circuital B := by
  intro x
  have hB : B = curl3 A := by
    funext y
    exact (h y).symm
  calc
    div3 B x = div3 (curl3 A) x := by rw [hB]
    _ = 0 := by simpa using congrFun (hdc A) x

/-- Heaviside's (1) with matter: the total electric current J = curl(H − h₀ − h) is made
    up of the conduction current C, the displacement-rate Ḋ, and the convection uρ. -/
def TotalCurrent (H J C Ddot : V3 → V3) (u : V3 → V3) (ρ : V3 → ℝ) : Prop :=
  ∀ x, curl3 H x = J x ∧ J x = C x + Ddot x + ρ x • u x

/-- The total current is circuital (given the div-curl vanishing). -/
theorem total_current_circuital (H J C Ddot : V3 → V3) (u : V3 → V3) (ρ : V3 → ℝ)
    (h : TotalCurrent H J C Ddot u ρ) (hdc : ∀ F : V3 → V3, div3 (curl3 F) = 0) :
    Circuital J := by
  intro x
  have hJ : J = curl3 H := by
    funext y
    exact (h y).1.symm
  calc
    div3 J x = div3 (curl3 H) x := by rw [hJ]
    _ = 0 := by simpa using congrFun (hdc H) x

/-- The continuity equation: with J = C + Ḋ + uρ and J circuital, the divergences of the
    three parts sum to zero (div-additivity as the premise). -/
theorem continuity_from_circuital (J C Ddot : V3 → V3) (u : V3 → V3) (ρ : V3 → ℝ)
    (hJ : ∀ x, J x = C x + Ddot x + ρ x • u x) (hdivJ : Circuital J)
    (hdivAdd : ∀ F G : V3 → V3, div3 (fun x => F x + G x) = fun x => div3 F x + div3 G x) :
    ∀ x, div3 C x + div3 Ddot x + div3 (fun y => ρ y • u y) x = 0 := by
  intro x
  have hJ' : J = fun y => C y + Ddot y + ρ y • u y := by
    funext y
    exact hJ y
  have hdivJx : div3 (fun y => C y + Ddot y + ρ y • u y) x = 0 := by
    rw [← hJ']
    exact hdivJ x
  have h1 := congrFun (hdivAdd (fun y => C y + Ddot y) (fun y => ρ y • u y)) x
  have hC := congrFun (hdivAdd C Ddot) x
  rw [h1, hC] at hdivJx
  exact hdivJx

/-- The free-space wave equation: from the curl pair with div E = 0 and the vector
    identity curl curl = grad div − Δ, the electric force satisfies ΔE = k·∂²E/∂t² with
    k = μc.  Heaviside's propagation result: with μcv² = 1 the speed is v = 1/√(μc). -/
theorem free_wave_equation (E B : ℝ → (V3 → V3)) (k : ℝ)
    (hfaraday : ∀ t, -curl3 (E t) = deriv (fun u => B u) t)
    (hampere : ∀ t, curl3 (B t) = k • deriv (fun u => E u) t)
    (hdivE : ∀ t, div3 (E t) = 0)
    (hcurlcurl : ∀ F : V3 → V3, curl3 (curl3 F) = grad3 (div3 F) - laplacian3 F)
    (hswap : ∀ t, curl3 (deriv (fun u => B u) t) = deriv (fun u => curl3 (B u)) t)
    (hcurlNeg : ∀ F : V3 → V3, curl3 (-F) = -curl3 F)
    (hsmul : ∀ F : ℝ → (V3 → V3), deriv (fun u => k • F u) = k • deriv F) :
    ∀ t, laplacian3 (E t) = k • deriv (deriv E) t := by
  have hcurlE : ∀ t, curl3 (E t) = -(deriv (fun u => B u) t) := by
    intro t
    have h := congrArg Neg.neg (hfaraday t)
    simpa using h
  intro t
  calc
    laplacian3 (E t) = grad3 (div3 (E t)) - curl3 (curl3 (E t)) := by
      have hcc := hcurlcurl (E t)
      symm
      calc
        grad3 (div3 (E t)) - curl3 (curl3 (E t))
            = grad3 (div3 (E t)) - (grad3 (div3 (E t)) - laplacian3 (E t)) := by rw [hcc]
        _ = laplacian3 (E t) := by ring
    _ = grad3 0 - curl3 (curl3 (E t)) := by rw [hdivE t]
    _ = 0 - curl3 (curl3 (E t)) := by
          have hg : grad3 (0 : V3 → ℝ) = 0 := by
            ext x
            simp [grad3, pd]
          rw [hg]
    _ = -curl3 (curl3 (E t)) := by simp
    _ = -curl3 (-(deriv (fun u => B u) t)) := by rw [hcurlE t]
    _ = -(-curl3 (deriv (fun u => B u) t)) := by rw [hcurlNeg]
    _ = curl3 (deriv (fun u => B u) t) := by simp
    _ = deriv (fun u => curl3 (B u)) t := by rw [hswap t]
    _ = deriv (fun u => k • deriv (fun s => E s) u) t := by
          congr 1
          funext u
          exact hampere u
    _ = k • deriv (deriv E) t := by
          exact congrFun (hsmul (deriv E)) t

/- The three laws of Heaviside's test (EP2 p. 495): "(1) (Faraday's law) The electromotive
    force of the field in any circuit equals the rate of decrease of the induction through
    the circuit.  (2) (Maxwell's law) The magnetomotive force of the field in any circuit
    equals the electric current through the circuit.  (3) (Maxwell) The displacement outward
    through any surface equals the enclosed charge."  In differential form: the curl pair
    and div D = ρ.  The moving-charge field (A)/(B) satisfies them (T4). -/

/-- Faraday's law in differential form: the magnetic current G is the negative curl of the
    electric force (5). -/
def FaradayLaw (E G : V3 → V3) : Prop :=
  CurlOfE E G

/-- Maxwell's law in differential form: the electric current is the curl of the magnetic
    force (4). -/
def MaxwellLaw (H J : V3 → V3) : Prop :=
  CurlOfH H J

/-- Continuity of displacement: the divergence of the displacement measures the density of
    electrification. -/
def ContinuityLaw (D : V3 → V3) (ρ : V3 → ℝ) : Prop :=
  ∀ x, div3 D x = ρ x

/-- The circuital-induction statement in the three-law system: a displacement field whose
    divergence is the electrification density vanishes in divergence when the density is
    zero (the free-space (3)-consistency). -/
theorem induction_circuital_of_continuity (D : V3 → V3) (ρ : V3 → ℝ)
    (hD : ContinuityLaw D ρ) (hρ0 : ρ = 0) :
    Circuital D := by
  intro x
  simpa [hρ0] using hD x

end HeavisideField
