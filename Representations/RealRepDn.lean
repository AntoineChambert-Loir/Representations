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

abbrev V₂ := Fin 2 → ℝ
-- instance : AddCommMonoid V₂ := Pi.addCommMonoid
-- instance : Module ℝ V₂ := inferInstance -- Pi.module _ _ _

open Matrix
open Complex
open scoped Matrix
open DihedralGroup

def A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]
def A_lin : V₂ →ₗ[ℝ] V₂ := Matrix.toLin' A

def rotMat (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (2 * Real.pi / n),
   -Real.sin (2 * Real.pi / n);
   Real.sin (2 * Real.pi / n),
   Real.cos (2 * Real.pi / n)]

#check Real.cos_add --  cos (x + y) = cos x * cos y - sin x * sin y


theorem rot_l (n l : ℕ): (rotMat n)^l  = !![Real.cos (2 * Real.pi * l/ n),
   -Real.sin (2 * Real.pi * l / n);
   Real.sin (2 * Real.pi * l / n),
   Real.cos (2 * Real.pi * l / n)] := by
  induction' l with l ih
  · simp
    rw [← @one_fin_two]
  rw [pow_add, ih]
  unfold rotMat
  ext i j
  fin_cases i <;> {
  · fin_cases j <;> {
      simp
      rw [mul_add, add_div]
      try rw [Real.sin_add]
      try rw [Real.cos_add]
      ring_nf
    }
  }


theorem rot_id (n : ℕ) (hn : n ≠ 0): (rotMat n)^n = 1 := by
  rw [rot_l n]
  ext i j
  fin_cases i <;> {
    fin_cases j <;> {
      simp
      rw [mul_div_assoc, div_self, mul_one]
      try rw [Real.cos_two_pi]
      try rw [Real.sin_two_pi]
      exact Nat.cast_ne_zero.mpr hn
    }
  }


theorem rot_id_pow (n : ℕ) (hn : n ≠ 0): ∀ (l : ℕ), (rotMat n)^(n * l) = 1 := by
  intro l
  induction' l with l ih
  · simp
  rw[mul_add, pow_add, ih, one_mul, mul_one]
  exact rot_id n hn




def refMat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 , 0 ; 0,  -1]

theorem ref_rot (n: ℕ)  (hn : n ≠ 0): (rotMat n) * refMat = refMat * (rotMat n)^(n-1) := by
  rw [rot_l]
  unfold rotMat refMat
  ext i j
  fin_cases i <;> {
    fin_cases j <;> {
      simp
      try rw [← Real.cos_two_pi_sub]
      try rw [← Real.sin_two_pi_sub]
      congr 1
      field_simp
      ring
    }
  }

def stdmap (n : ℕ) : DihedralGroup n → (V₂ →ₗ[ℝ] V₂) := by
  intro g
  match g with
  | .r k => exact Matrix.toLin' ((rotMat n)^k.val)
  | .sr k => exact Matrix.toLin' (refMat * (rotMat n)^k.val)

theorem stdmap_one (n : ℕ): stdmap n 1 = 1 := by
  rw [one_def]
  unfold stdmap
  simp
  rfl

#check LinearMap.toMatrix'_comp
#check Matrix.toLin'_mul


theorem stdmap_mul (n: ℕ) (hn : n ≠ 0): ∀ x y , stdmap n (x * y) = stdmap n x ∘ₗ stdmap n y := by
  intro x y
  match y with
  |.r l =>
    match x with
    |.r k =>
      rw[r_mul_r]
      unfold stdmap
      simp
      repeat rw [← Matrix.toLin'_mul]
      congr 1
      rw [← pow_add]
      by_cases h : k.val + l.val < n
      · have : (k + l).val = k.val + l.val :=  ZMod.val_add_of_lt h
        rw [this]
      · push_neg at h
        haveI : NeZero n := ⟨hn⟩
        have : k.val + l.val = (k + l).val + n := ZMod.val_add_val_of_le h
        rw [this, pow_add, rot_id n hn, mul_one]


    |.sr k =>
      rw[sr_mul_r]
      unfold stdmap
      simp
      repeat rw [← Matrix.toLin'_mul]
      congr 1
      rw [mul_assoc]
      congr 1
      rw [← pow_add]
      by_cases h : k.val + l.val < n
      · have : (k + l).val = k.val + l.val :=  ZMod.val_add_of_lt h
        rw [this]
      · push_neg at h
        haveI : NeZero n := ⟨hn⟩
        have : k.val + l.val = (k + l).val + n := ZMod.val_add_val_of_le h
        rw [this, pow_add, rot_id n hn, mul_one]


  |.sr l => sorry


def rep_example (n : ℕ) : Representation  ℂ (DihedralGroup n) V₂ where
  toFun := stdmap -- (DihedralGroup n) → (V₂ →ₗ[ℂ] V₂)
  map_one' := stdmap_one
  map_mul' := stdmap_mul
