import Mathlib

/-!
# Heaviside corpus, T1: the telegrapher's equations

Heaviside, "Electromagnetic Induction and Its Propagation" (The Electrician, 1885–87;
Electrical Papers Vol. 1, pp. 429–560). In his operational notation (p = d/dt, K = capacitance,
S = leakance), the line equations are

  −∂V/∂x = (R + L·p)·I        −∂I/∂x = (S + K·p)·V .

Formalised here:
  1. `pd1`/`pd2` — scalar two-variable partial derivatives (sections via `deriv`).
  2. `TelegraphEqV`/`TelegraphEqI` — the line equations as premises (physics lives in the
     premises; what is kernel-verified is the model's internal logic).
  3. `telegrapher_second_order_V` — eliminating I: the second-order equation
     ∂²V/∂x² = LK·∂²V/∂t² + (RK + LS)·∂V/∂t + RS·V ,
     with `LineSmooth` (two-argument C²-type differentiability) and the Schwarz cross-partial
     for I as the analytic premises.
  4. `distortionless_factorisation` — the distortionless condition R/L = S/K (i.e. RK = LS):
     the propagation constant factorises, m² = (R + Lp)(S + Kp) = (√(RS) + p·√(LK))²,
     so attenuation √(RS) and speed 1/√(LK) are frequency-independent (the signal travels
     undistorted). Heaviside's 1887 result against Kelvin's diffusion theory (L = 0).
  5. `distortionless_finite_speed` — the speed 1/√(LK) exists and is positive: with L ≠ 0
     the line has a finite signal speed (EP2 p. 492: "nothing else being propagated at the
     infinite speed").
  6. `distortionless_wave_solution` — with RK = LS, V(x,t) = e^{−αx}·F(t − x/v), α = √(RS),
     v = 1/√(LK), satisfies the second-order equation for any twice-differentiable F: the
     profile F is carried undistorted (up to the exponential attenuation) at the finite
     speed v. (Written with v⁻¹ throughout — `t − x·v⁻¹` — so the chain-rule functions are
     definitionally identical and every conversion step is a pure ring goal.)
-/

namespace HeavisideTelegraph

/-- x-partial of a two-variable scalar function:  pd1 f x t = ∂f/∂x (x,t). -/
noncomputable def pd1 (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => f s t) x

/-- t-partial of a two-variable scalar function:  pd2 f x t = ∂f/∂t (x,t). -/
noncomputable def pd2 (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun s => f x s) t

/-- The two-argument differentiability the line-equation calculus needs: first partials and
    the mixed partials of V and I (C²-type smoothness). -/
structure LineSmooth (V I : ℝ → ℝ → ℝ) : Prop where
  Vx : ∀ x t, DifferentiableAt ℝ (fun s => V s t) x
  Vt : ∀ x t, DifferentiableAt ℝ (fun s => V x s) t
  Ix : ∀ x t, DifferentiableAt ℝ (fun s => I s t) x
  It : ∀ x t, DifferentiableAt ℝ (fun s => I x s) t
  Vxx : ∀ x t, DifferentiableAt ℝ (fun s => pd1 V s t) x
  Vtt : ∀ x t, DifferentiableAt ℝ (fun s => pd2 V x s) t
  Ixt : ∀ x t, DifferentiableAt ℝ (fun s => pd1 I x s) t
  Ixx : ∀ x t, DifferentiableAt ℝ (fun s => pd2 I s t) x

/-- Heaviside's first line equation:  −∂V/∂x = (R + L·p)·I  (p = d/dt). -/
def TelegraphEqV (V I : ℝ → ℝ → ℝ) (R L _S _K : ℝ) : Prop :=
  ∀ x t, -pd1 V x t = R * I x t + L * pd2 I x t

/-- Heaviside's second line equation:  −∂I/∂x = (S + K·p)·V. -/
def TelegraphEqI (V I : ℝ → ℝ → ℝ) (_R _L S K : ℝ) : Prop :=
  ∀ x t, -pd1 I x t = S * V x t + K * pd2 V x t

/-- Eliminating I from the pair of line equations gives the second-order equation
    ∂²V/∂x² = LK·∂²V/∂t² + (RK + LS)·∂V/∂t + RS·V.
    The analytic premises are the C²-type smoothness of V and I and the Schwarz
    cross-partial for I. -/
theorem telegrapher_second_order_V (V I : ℝ → ℝ → ℝ) (R L S K : ℝ)
    (hV : TelegraphEqV V I R L S K) (hI : TelegraphEqI V I R L S K)
    (hs : LineSmooth V I)
    (hcross : ∀ x t, deriv (fun s => pd2 I s t) x = deriv (fun s => pd1 I x s) t) :
    ∀ x t, deriv (fun s => pd1 V s t) x
      = L * K * pd2 (fun x t => pd2 V x t) x t + (R * K + L * S) * pd2 V x t + R * S * V x t := by
  intro x t
  simp only [TelegraphEqV, TelegraphEqI] at hV hI
  have hd : deriv (fun s => -pd1 V s t) x = deriv (fun s => R * I s t + L * pd2 I s t) x := by
    congr 1
    funext s
    exact hV s t
  -- LHS: -∂²V/∂x²
  have hL : deriv (fun s => -pd1 V s t) x = -deriv (fun s => pd1 V s t) x := by
    exact deriv.neg
  -- RHS: R·∂I/∂x + L·∂(∂I/∂t)/∂x
  have hR : deriv (fun s => R * I s t + L * pd2 I s t) x
      = R * pd1 I x t + L * deriv (fun s => pd2 I s t) x := by
    have hIat : HasDerivAt (fun s => I s t) (deriv (fun s => I s t) x) x :=
      (hs.Ix x t).hasDerivAt
    have h1 : HasDerivAt (fun s => R * I s t) (R * deriv (fun s => I s t) x) x :=
      hIat.const_mul R
    have h2 : HasDerivAt (fun s => L * pd2 I s t) (L * deriv (fun s => pd2 I s t) x) x :=
      (hs.Ixx x t).hasDerivAt.const_mul L
    have hsum : HasDerivAt (fun s => R * I s t + L * pd2 I s t)
        (R * deriv (fun s => I s t) x + L * deriv (fun s => pd2 I s t) x) x :=
      h1.add h2
    simpa [pd1] using hsum.deriv
  -- the substitution facts
  have hpd1I : ∀ s, pd1 I x s = -(S * V x s + K * pd2 V x s) := by
    intro s
    have hs' := hI x s
    linarith
  have hpd1I_at : pd1 I x t = -(S * V x t + K * pd2 V x t) := hpd1I t
  have hcrossSub : deriv (fun s => pd2 I s t) x = -(S * pd2 V x t + K * pd2 (fun x t => pd2 V x t) x t) := by
    rw [hcross x t]
    have hfun : (fun s => pd1 I x s) = (fun s => -(S * V x s + K * pd2 V x s)) := by
      funext s
      exact hpd1I s
    rw [hfun]
    have hVt' : HasDerivAt (fun s => V x s) (deriv (fun s => V x s) t) t :=
      (hs.Vt x t).hasDerivAt
    have h1 : HasDerivAt (fun s => S * V x s) (S * deriv (fun s => V x s) t) t :=
      hVt'.const_mul S
    have h2 : HasDerivAt (fun s => K * pd2 V x s) (K * deriv (fun s => pd2 V x s) t) t :=
      (hs.Vtt x t).hasDerivAt.const_mul K
    have hsum : HasDerivAt (fun s => S * V x s + K * pd2 V x s)
        (S * deriv (fun s => V x s) t + K * deriv (fun s => pd2 V x s) t) t :=
      h1.add h2
    exact hsum.neg.deriv
  -- assemble: -∂²V/∂x² = R·∂I/∂x + L·∂²I/∂x∂t
  have hmain : -deriv (fun s => pd1 V s t) x
      = R * pd1 I x t + L * deriv (fun s => pd2 I s t) x := by
    rw [← hL, ← hR]
    exact hd
  -- substitute and finish
  rw [hpd1I_at, hcrossSub] at hmain
  have hneg := congrArg Neg.neg hmain
  simp at hneg
  convert hneg using 1
  ring

/-- Distortionless condition (R/L = S/K, i.e. RK = LS): the propagation constant factorises,
    m² = (R + Lp)(S + Kp) = (√(RS) + p·√(LK))².  Attenuation √(RS) and speed 1/√(LK) do not
    depend on p — every frequency component propagates at the same speed and attenuation,
    so a composite signal travels without distortion. -/
theorem distortionless_factorisation (R L S K p : ℝ) (hcond : R * K = L * S)
    (hRS : 0 ≤ R * S) (hLK : 0 ≤ L * K) (hRK : 0 ≤ R * K) :
    (Real.sqrt (R * S) + p * Real.sqrt (L * K)) ^ 2 = (R + L * p) * (S + K * p) := by
  have hsqrt : Real.sqrt (R * S) * Real.sqrt (L * K) = R * K := by
    rw [← Real.sqrt_mul hRS (L * K)]
    have hmul : (R * S) * (L * K) = (R * K) * (L * S) := by ring
    rw [hmul, hcond]
    simpa [sq] using Real.sqrt_sq (by simpa [hcond] using hRK)
  calc
    (Real.sqrt (R * S) + p * Real.sqrt (L * K)) ^ 2
        = Real.sqrt (R * S) ^ 2 + 2 * p * (Real.sqrt (R * S) * Real.sqrt (L * K))
            + p ^ 2 * Real.sqrt (L * K) ^ 2 := by
          ring
    _ = R * S + 2 * p * (Real.sqrt (R * S) * Real.sqrt (L * K)) + p ^ 2 * (L * K) := by
          rw [Real.sq_sqrt hRS, Real.sq_sqrt hLK]
    _ = R * S + 2 * p * (R * K) + p ^ 2 * (L * K) := by rw [hsqrt]
    _ = R * S + p * (R * K + L * S) + p ^ 2 * (L * K) := by
          rw [hcond]
          ring
    _ = (R + L * p) * (S + K * p) := by
          ring_nf

/-- The finite speed 1/√(LK) of the distortionless line: positive whenever LK > 0
    (Heaviside's 1887 result — a line with inductance propagates at finite speed). -/
theorem distortionless_finite_speed (L K : ℝ) (hLK : 0 < L * K) :
    0 < (Real.sqrt (L * K))⁻¹ := by
  exact inv_pos.mpr (Real.sqrt_pos.2 hLK)

/-- With the distortionless condition, α = √(RS) and v = 1/√(LK) give a travelling-wave
    solution V(x,t) = e^{−αx}·F(t − x/v) of the second-order equation: the profile F is
    carried undistorted (up to the exponential attenuation) at the finite speed v. -/
theorem distortionless_wave_solution (F : ℝ → ℝ) (R L S K : ℝ)
    (hcond : R * K = L * S) (hRS : 0 ≤ R * S) (hLK : 0 ≤ L * K) (hRK : 0 ≤ R * K)
    (hF : Differentiable ℝ F) (hF' : Differentiable ℝ (deriv F)) :
    let α := Real.sqrt (R * S)
    let v := (Real.sqrt (L * K))⁻¹
    let V := fun x t => Real.exp (-α * x) * F (t - x * v⁻¹)
    ∀ x t, deriv (fun s => pd1 V s t) x
      = L * K * pd2 (fun x t => pd2 V x t) x t + (R * K + L * S) * pd2 V x t + R * S * V x t := by
  intro α v V x t
  -- basic chain-rule blocks
  have hA : ∀ a, HasDerivAt (fun s => Real.exp (-α * s)) (Real.exp (-α * a) * (-α)) a := by
    intro a
    simpa using ((hasDerivAt_id a).const_mul (-α)).exp
  have hArg : ∀ a, HasDerivAt (fun s => t - s * v⁻¹) (-v⁻¹) a := by
    intro a
    have hlin : HasDerivAt (fun s => s * v⁻¹) (v⁻¹) a := by
      simpa using (hasDerivAt_id a).mul_const (v⁻¹)
    exact (hlin.neg.const_add t)
  have hFarg : ∀ a, HasDerivAt (fun s => F (t - s * v⁻¹)) (deriv F (t - a * v⁻¹) * (-v⁻¹)) a := by
    intro a
    exact ((hF (t - a * v⁻¹)).hasDerivAt).comp a (hArg a)
  have hFarg' : ∀ a, HasDerivAt (fun s => deriv F (t - s * v⁻¹))
      (deriv (deriv F) (t - a * v⁻¹) * (-v⁻¹)) a := by
    intro a
    exact ((hF' (t - a * v⁻¹)).hasDerivAt).comp a (hArg a)
  -- first partials
  have hpd1V : pd1 V x t = Real.exp (-α * x) * (-(α * F (t - x * v⁻¹)) - v⁻¹ * deriv F (t - x * v⁻¹)) := by
    unfold pd1
    dsimp [V]
    have hprod : HasDerivAt ((fun s => Real.exp (-α * s)) * fun s => F (t - s * v⁻¹))
        (Real.exp (-α * x) * (-(α * F (t - x * v⁻¹)) - v⁻¹ * deriv F (t - x * v⁻¹))) x := by
      convert ((hA x).mul (hFarg x)) using 1 <;> first | ring | rfl
    exact hprod.deriv
  have hpd2V : pd2 V x t = Real.exp (-α * x) * deriv F (t - x * v⁻¹) := by
    unfold pd2
    dsimp [V]
    have hinner : HasDerivAt (fun s => s - x * v⁻¹) 1 t := by
      exact (hasDerivAt_id t).sub_const (x * v⁻¹)
    have hcomp : HasDerivAt (fun s => Real.exp (-α * x) * F (s - x * v⁻¹))
        (Real.exp (-α * x) * (deriv F (t - x * v⁻¹) * 1)) t := by
      have hinner' : HasDerivAt (fun s => F (s - x * v⁻¹)) (deriv F (t - x * v⁻¹) * 1) t := by
        exact ((hF (t - x * v⁻¹)).hasDerivAt).comp t hinner
      exact hinner'.const_mul (Real.exp (-α * x))
    have hval : Real.exp (-α * x) * (deriv F (t - x * v⁻¹) * 1)
        = Real.exp (-α * x) * deriv F (t - x * v⁻¹) := by
      ring
    simpa [hval] using hcomp.deriv
  -- second t-derivative
  have htt : pd2 (fun x t => pd2 V x t) x t = Real.exp (-α * x) * deriv (deriv F) (t - x * v⁻¹) := by
    have hpd2Vs : ∀ s, pd2 V x s = Real.exp (-α * x) * deriv F (s - x * v⁻¹) := by
      intro s
      unfold pd2
      dsimp [V]
      have hinner : HasDerivAt (fun u => u - x * v⁻¹) 1 s := by
        exact (hasDerivAt_id s).sub_const (x * v⁻¹)
      have hcomp : HasDerivAt (fun u => Real.exp (-α * x) * F (u - x * v⁻¹))
          (Real.exp (-α * x) * (deriv F (s - x * v⁻¹) * 1)) s := by
        have hinner' : HasDerivAt (fun u => F (u - x * v⁻¹)) (deriv F (s - x * v⁻¹) * 1) s := by
          exact ((hF (s - x * v⁻¹)).hasDerivAt).comp s hinner
        exact hinner'.const_mul (Real.exp (-α * x))
      have hval : Real.exp (-α * x) * (deriv F (s - x * v⁻¹) * 1)
          = Real.exp (-α * x) * deriv F (s - x * v⁻¹) := by
        ring
      simpa [hval] using hcomp.deriv
    unfold pd2
    change deriv (fun s => pd2 V x s) t = Real.exp (-α * x) * deriv (deriv F) (t - x * v⁻¹)
    rw [show (fun s => pd2 V x s) = (fun s => Real.exp (-α * x) * deriv F (s - x * v⁻¹)) by
      funext s
      exact hpd2Vs s]
    have hinner : HasDerivAt (fun s => s - x * v⁻¹) 1 t := by
      exact (hasDerivAt_id t).sub_const (x * v⁻¹)
    have hcomp : HasDerivAt (fun s => Real.exp (-α * x) * deriv F (s - x * v⁻¹))
        (Real.exp (-α * x) * (deriv (deriv F) (t - x * v⁻¹) * 1)) t := by
      have hinner' : HasDerivAt (fun s => deriv F (s - x * v⁻¹))
          (deriv (deriv F) (t - x * v⁻¹) * 1) t := by
        exact ((hF' (t - x * v⁻¹)).hasDerivAt).comp t hinner
      exact hinner'.const_mul (Real.exp (-α * x))
    have hval : Real.exp (-α * x) * (deriv (deriv F) (t - x * v⁻¹) * 1)
        = Real.exp (-α * x) * deriv (deriv F) (t - x * v⁻¹) := by
      ring
    simpa [hval] using hcomp.deriv
  -- second x-derivative
  have hxx : deriv (fun s => pd1 V s t) x = Real.exp (-α * x) *
      (α ^ 2 * F (t - x * v⁻¹) + 2 * α * v⁻¹ * deriv F (t - x * v⁻¹)
        + (v⁻¹) ^ 2 * deriv (deriv F) (t - x * v⁻¹)) := by
    have hpd1Vs : ∀ s, pd1 V s t = Real.exp (-α * s) * (-(α * F (t - s * v⁻¹)) - v⁻¹ * deriv F (t - s * v⁻¹)) := by
      intro s
      unfold pd1
      dsimp [V]
      have hprod : HasDerivAt ((fun u => Real.exp (-α * u)) * fun u => F (t - u * v⁻¹))
          (Real.exp (-α * s) * (-(α * F (t - s * v⁻¹)) - v⁻¹ * deriv F (t - s * v⁻¹))) s := by
        convert ((hA s).mul (hFarg s)) using 1 <;> first | ring | rfl
      exact hprod.deriv
    rw [show (fun s => pd1 V s t) = (fun s => Real.exp (-α * s) * (-(α * F (t - s * v⁻¹)) - v⁻¹ * deriv F (t - s * v⁻¹))) by
      funext s
      exact hpd1Vs s]
    have hinner : HasDerivAt (fun s => -(α * F (t - s * v⁻¹)) - v⁻¹ * deriv F (t - s * v⁻¹))
        (α * v⁻¹ * deriv F (t - x * v⁻¹) + (v⁻¹) ^ 2 * deriv (deriv F) (t - x * v⁻¹)) x := by
      have h1 := (hFarg x).const_mul α
      have h2 := (hFarg' x).const_mul (v⁻¹)
      have hneg1 : HasDerivAt (fun s => -(α * F (t - s * v⁻¹)))
          (-(α * (deriv F (t - x * v⁻¹) * (-v⁻¹)))) x := h1.neg
      -- convert's unification writes s * v⁻¹ as v⁻¹ * s inside the lambdas; bridge:
      have hfunc : (fun s => -(α * F (t - s * v⁻¹)) - v⁻¹ * deriv F (t - s * v⁻¹)) =
          (fun s => -(α * F (t - v⁻¹ * s)) - v⁻¹ * deriv F (t - v⁻¹ * s)) := by
        funext s
        have harg1 : t - s * v⁻¹ = t - v⁻¹ * s := by ring
        rw [harg1]
      convert (hneg1.sub h2) using 1
      all_goals try ring
      all_goals try rfl
      all_goals try (exact hfunc.trans rfl)
    have hprod : HasDerivAt ((fun s => Real.exp (-α * s)) * fun s => -(α * F (t - s * v⁻¹)) - v⁻¹ * deriv F (t - s * v⁻¹))
        (Real.exp (-α * x) * (α ^ 2 * F (t - x * v⁻¹) + 2 * α * v⁻¹ * deriv F (t - x * v⁻¹)
          + (v⁻¹) ^ 2 * deriv (deriv F) (t - x * v⁻¹))) x := by
      convert ((hA x).mul hinner) using 1
      all_goals first | ring | rfl
    exact hprod.deriv
  -- the three identities
  have halpha2 : α ^ 2 = R * S := by
    dsimp [α]
    exact Real.sq_sqrt hRS
  have hvinv : v⁻¹ = Real.sqrt (L * K) := by
    simp [v]
  have hvinv2 : (v⁻¹) ^ 2 = L * K := by
    rw [hvinv]
    exact Real.sq_sqrt hLK
  have hαv : α * v⁻¹ = R * K := by
    rw [hvinv]
    dsimp [α]
    rw [← Real.sqrt_mul hRS (L * K)]
    have hmul : (R * S) * (L * K) = (R * K) * (L * S) := by ring
    rw [hmul, hcond]
    simpa [sq] using Real.sqrt_sq (by simpa [hcond] using hRK)
  -- assemble
  calc
    deriv (fun s => pd1 V s t) x = Real.exp (-α * x) *
        (α ^ 2 * F (t - x * v⁻¹) + 2 * α * v⁻¹ * deriv F (t - x * v⁻¹)
          + (v⁻¹) ^ 2 * deriv (deriv F) (t - x * v⁻¹)) := hxx
    _ = L * K * pd2 (fun x t => pd2 V x t) x t + (R * K + L * S) * pd2 V x t + R * S * V x t := by
      rw [htt, hpd2V]
      dsimp [V]
      rw [← halpha2, ← hvinv2]
      rw [show R * K + L * S = 2 * α * v⁻¹ by
        have hRK' : R * K = α * v⁻¹ := hαv.symm
        rw [hRK']
        have hLS' : L * S = α * v⁻¹ := by
          rw [← hcond]
          exact hαv.symm
        rw [hLS']
        ring]
      ring

end HeavisideTelegraph
