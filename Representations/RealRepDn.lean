-- work by Hikari Iwasaki on June 24, 2025 --
import Mathlib
#check DihedralGroup

noncomputable section

-- Goal: construct an explicit real representation of the dihedral group.
-- work still in progress.
-- current state: trying to prove the map is a homomorphism.
-- tasks:
-- 1) theorem rot_l : showing (rotMat n)^l corresponds to rotation by (l 2π /n)
-- 2) theorem rot_id : once rot_l is done, we should be able to prove this easily
-- 3) theorem rot_id_pow : a generalized version, should be easy
-- 4) all of these are used to prove stdmap is multiplicative (std_mul).

variable (n : ℕ)
abbrev V₂ := Fin 2 → ℝ
-- instance : AddCommMonoid V₂ := Pi.addCommMonoid
-- instance : Module ℝ V₂ := inferInstance -- Pi.module _ _ _

open Matrix
open Complex
open scoped Matrix
open DihedralGroup

def A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
def A_lin : V₂ →ₗ[ℝ] V₂ := Matrix.toLin' A

noncomputable def rotMat (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (2 * Real.pi / n),
   -Real.sin (2 * Real.pi / n);
   Real.sin (2 * Real.pi / n),
   Real.cos (2 * Real.pi / n)]

#check Real.cos_add --  cos (x + y) = cos x * cos y - sin x * sin y


theorem rot_l (l : ℕ): (rotMat n)^l  = !![Real.cos (2 * Real.pi * l/ n),
   -Real.sin (2 * Real.pi * l / n);
   Real.sin (2 * Real.pi * l / n),
   Real.cos (2 * Real.pi * l / n)] := by
  induction' l with l ih
  · simp
    rw [← @one_fin_two]
  rw [pow_add, ih]
  unfold rotMat
  ext i j
  match i with
  | 0 =>
    match j with
    | 0 =>
      simp
      rw [← sub_eq_add_neg , ← Real.cos_add]
      ring_nf
    | 1 => sorry
  | 1 => sorry


theorem rot_id : ∀ (l : ℕ),  (rotMat n)^n = 1 := by
  -- intro l
  sorry


theorem rot_id_pow : ∀ (l : ℕ),  (rotMat n)^(l*n) = 1 := by
  -- deduced the theorem to above
  sorry


noncomputable def refMat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 , 0 ; 0,  -1]

def stdmap (n : ℕ) : DihedralGroup n → (V₂ →ₗ[ℝ] V₂) := by
  intro g
  match g with
  | .r k => exact Matrix.toLin' ((rotMat n)^k.val)
  | .sr k => exact Matrix.toLin' (refMat * (rotMat n)^k.val)

theorem stdmap_one : stdmap n 1 = 1 := by
  rw [one_def]
  unfold stdmap
  simp
  rfl

#check LinearMap.toMatrix'_comp
#check Matrix.toLin'_mul


theorem stdmap_mul : ∀ x y , stdmap n (x * y) = stdmap n x ∘ₗ stdmap n y := by
  intro x y
  match x with
  | .r k =>
      match y with
      |.r l =>
        unfold stdmap
        simp
        rw [(Matrix.toLin'_mul (rotMat n ^ k.val) (rotMat n ^ l.val)).symm]
        rw [← pow_add]

        -- now we need to show that power by k.val + l.val and (k+l).val evaluate to the same matrix.
        -- (!) need (rotMat n)^n = 1. doing this above ^

        sorry
      |.sr l => sorry
  | .sr k => sorry




def rep_example (n : ℕ) : Representation  ℂ (DihedralGroup n) V₂ where
  toFun := stdmap -- (DihedralGroup n) → (V₂ →ₗ[ℂ] V₂)
  map_one' := stdmap_one
  map_mul' := stdmap_mul
