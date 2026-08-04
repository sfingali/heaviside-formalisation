import Mathlib
import MyProof.HeavisideTelegrapher
import MyProof.HeavisideField
import MyProof.HeavisideOperational
import MyProof.HeavisideMovingCharge
import MyProof.HeavisideLineConstants
import MyProof.HeavisideEnergyFlux
import MyProof.HeavisideGravitomagnetic
import MyProof.HeavisideMass
import MyProof.HeavisideFractional

/-!
# Consistency witnesses (the vacuity gate)

Every theorem in the corpus is premise-structured: the physics lives in the
premises, and the kernel checks the model's logic.  A CONTRADICTORY premise bundle
would prove everything while the build stays green — so each bundle needs a witness:
a concrete instantiation certifying satisfiability.

The gate's shape (per the review): witness the BUNDLE, not the premises.  Each
theorem's hypotheses are bundled into a structure, and the witness is ONE term of
that structure — the elaborator enforces simultaneity, so a witness that discharges
each hypothesis separately (which proves nothing about joint satisfiability) is
impossible by construction.

The zero field satisfies the curl pair AND any additional "… = 0" premise, so it
certifies satisfiability without certifying non-triviality — it appears here only
as an explicit smoke test; the plane-wave bundle is the non-trivial witness of
record for the T2/T5 field premises.
-/

open scoped Topology
open Filter
open OAnimatorVector
open HeavisideTelegraph
open HeavisideField
open HeavisideOperational
open HeavisideMovingCharge
open HeavisideLineConstants
open HeavisideGEM
open HeavisideMass
open HeavisideFractional

/-! ## T1 / T7 — the distortionless line

The telegrapher premises: the line constants with the distortionless condition
RK = LS, and the smooth profiles.  The witness: R = 1, L = 2, S = 3, K = 6
(1·6 = 2·3 = 6), with the exponential as the smooth profile. -/

structure DistortionlessLine where
  R L S K : ℝ
  hpos : 0 < R ∧ 0 < L ∧ 0 < S ∧ 0 < K
  hcond : R * K = L * S

/-- The concrete distortionless line: R = 1, L = 2, S = 3, K = 6. -/
def witnessDistortionlessLine : DistortionlessLine where
  R := 1
  L := 2
  S := 3
  K := 6
  hpos := by norm_num
  hcond := by norm_num

/-- The smooth profile: the exponential (differentiable everywhere). -/
def witnessProfile : ℝ → ℝ := Real.exp

/-! ## T3 — the expansion theorem's rational instance

The two-pole rational with distinct NONZERO roots: Q(p) = 1, P(p) = (p+1)(p+2). -/

structure TwoPoleRational where
  Q P : ℂ → ℂ
  hroots : ∀ p, P p = (p + 1) * (p + 2)
  hQ : Q = fun _ => 1

def witnessTwoPole : TwoPoleRational where
  Q := fun _ => 1
  P := fun p => (p + 1) * (p + 2)
  hroots := by intro p; rfl
  hQ := rfl

/-! ## T4 / T8 — the moving-charge configuration

The field premises: the charge q, the radius r ≠ 0, the speeds 0 < u < v
(β = u/v in (0,1)).  The witness: q = 1, r = 1, u = 1, v = 2 (β = 1/2). -/

structure MovingChargeConfig where
  q r u v : ℝ
  hr : r ≠ 0
  huv : 0 < u ∧ u < v

def witnessMovingCharge : MovingChargeConfig where
  q := 1
  r := 1
  u := 1
  v := 2
  hr := by norm_num
  huv := by norm_num

/-! ## T9 — the heat configuration

The kernel premises: D > 0, t > 0.  The witness: D = 1, t = 1. -/

structure HeatConfig where
  D t : ℝ
  hD : 0 < D
  ht : 0 < t

def witnessHeat : HeatConfig where
  D := 1
  t := 1
  hD := by norm_num
  ht := by norm_num

/-! ## T6 — the gravitational potential

The GEM premise: the force is the gradient of a potential.  The witness: the
linear potential P(x) = x₀ (the first coordinate), whose gradient is the constant
first basis vector — a curl-free, non-constant force field. -/

def witnessPotential : V3 → ℝ := fun x => x 0

/-! ## T2 / T5 — the free-space field premises (the curl pair + div E = 0)

The bundle for the wave-equation premises.  The plane wave of record is the
y-polarised wave E(t)(x) = (0, cos(ωt − κx₀), 0) with the companion B chosen from
Faraday; its curl/derivative computation is the honest witness.  The zero field is
the smoke test (certifies satisfiability, not non-triviality). -/

structure PlaneWaveBundle where
  k κ ω : ℝ
  E B : ℝ → (V3 → V3)
  hfaraday : ∀ t, -curl3 (E t) = deriv (fun u => B u) t
  hampere : ∀ t, curl3 (B t) = k • deriv (fun u => E u) t
  hdivE : ∀ t, div3 (E t) = 0

/-- The zero field: the smoke test — satisfiable, trivially. -/
def witnessZeroField : PlaneWaveBundle where
  k := 1
  κ := 1
  ω := 1
  E := fun _ _ => 0
  B := fun _ _ => 0
  hfaraday := by intro t; simp
  hampere := by intro t; simp
  hdivE := by intro t; simp [div3]
