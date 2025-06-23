
import Mathlib

def Representation (G : Type*) [Monoid G] (R : Type*) [Semiring R] (V : Type*) [AddCommMonoid V] [Module R V] :=
  G →* (V ≃ₗ[R] V)
