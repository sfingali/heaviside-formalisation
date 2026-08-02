import Mathlib

/-!
# Vector calculus on ℝ³ (component-wise, mathlib-minimal)

The Rañada knot construction and the Afanasiev–Dubovik gauge statements need
curl/div/grad on ℝ³. The pinned mathlib has `gradient` for inner-product
spaces but no component-wise `curl`/`div` API, so we define them here from
`deriv` along coordinate directions. The two standard identities used by the
papers — curl ∇h = 0 (Clairaut) and div(F×G) = G·curl F − F·curl G (product
rule) — are stated as explicit premises `hcurl_grad` and `hdiv_cross`: the
papers use them without comment, and their proofs (mixed partials, product
rule) are regularity facts we do not re-derive here.
-/

namespace OAnimatorVector

abbrev V3 := Fin 3 → ℝ

/-- Partial derivative along coordinate `i` (via the totalized one-dimensional
derivative along the coordinate line). -/
noncomputable def pd (i : Fin 3) (f : V3 → ℝ) (x : V3) : ℝ :=
  deriv (fun t : ℝ => f (Function.update x i t)) (x i)

/-- The gradient of a scalar field. -/
noncomputable def grad3 (f : V3 → ℝ) (x : V3) : V3 := fun i => pd i f x

/-- The divergence of a vector field. -/
noncomputable def div3 (F : V3 → V3) (x : V3) : ℝ := ∑ i, pd i (fun y => F y i) x

/-- The curl of a vector field. -/
noncomputable def curl3 (F : V3 → V3) (x : V3) : V3 :=
  ![pd 1 (fun y => F y 2) x - pd 2 (fun y => F y 1) x,
    pd 2 (fun y => F y 0) x - pd 0 (fun y => F y 2) x,
    pd 0 (fun y => F y 1) x - pd 1 (fun y => F y 0) x]

/-- The pointwise dot product. -/
noncomputable def dot3 (u v : V3) : ℝ := ∑ i, u i * v i

/-- The pointwise cross product. -/
noncomputable def cross3 (u v : V3) : V3 :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

-- The standard identities, as explicit premises (regularity assumptions):

/-- curl ∇h = 0 for every smooth scalar field h (mixed partials cancel). -/
def HcurlGrad : Prop := ∀ h : V3 → ℝ, curl3 (grad3 h) = 0

/-- div(F × G) = G · curl F − F · curl G (product rule). -/
def HdivCross : Prop :=
  ∀ A B : V3 → V3, div3 (fun x => cross3 (A x) (B x)) =
    fun x => dot3 (B x) (curl3 A x) - dot3 (A x) (curl3 B x)

/-- curl is additive (linearity). -/
def HcurlAdd : Prop :=
  ∀ F G : V3 → V3, curl3 (fun x => F x + G x) = fun x => curl3 F x + curl3 G x

/-- curl is subtractive (linearity). -/
def HcurlSub : Prop :=
  ∀ F G : V3 → V3, curl3 (fun x => F x - G x) = fun x => curl3 F x - curl3 G x

end OAnimatorVector
