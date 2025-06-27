import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.RepresentationTheory.Basic

-- #check SemidirectProduct.lift

variable {K : Type*} [Field K]
         {L : Type*} [Ring L] [Algebra K L] [Algebra.IsQuadraticExtension K L]

variable {α G : Type*} [Group α] [Group G] {ϕ : G →* MulAut α}
         (f : α →* L) (σ : G →* L ≃ₐ[K] L)
         (h : ∀ (g : G) (a : α), f (ϕ g a) = σ g (f a))
         -- (h : ∀ (g : G), MonoidHom.comp f (ϕ g) = MonoidHom.comp (σ g) f)

/-- Construct representations of semidirect products from automorphisms of algebras.

To be precise, given a `K`-algebra `L`, a group homomorphism `f` from
`α` to `L`, and a group homomorphism `σ` from `G` to the group of
`K`-algebra automorphisms of `L`, we obtain a `K`-linear
representation of a semidirect product `α ⋊ G` on `L`, where the
elements of `α` act as scalar multiplication via `f` and the elements
of `G` act via `σ`. -/
def SemidirectProduct.representationFromAlgebra : Representation K (α ⋊[ϕ] G) L :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := L) |>.comp <|
  SemidirectProduct.lift
    ((DistribMulAction.toModuleAut K L).comp f.toHomUnits)
    ((DistribMulAction.toModuleAut K L).comp σ)
    (by intro g; ext a x
        show f (ϕ g a) * x = σ g (f a * (σ g)⁻¹ x)
        rewrite [h g a, map_mul]; congr 1; rw [AlgEquiv.aut_inv, ←AlgEquiv.symm_apply_eq])
