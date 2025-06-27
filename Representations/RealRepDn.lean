-- work by Hikari Iwasaki on June 24, 2025 --
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.RepresentationTheory.Basic

-- #check DihedralGroup

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

-- #check Real.cos_add -- cos (x + y) = cos x * cos y - sin x * sin y


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


theorem rot_id (n : ℕ) [NeZero n] : (rotMat n)^n = 1 := by
  rw [rot_l n]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rot_id_pow (n : ℕ) [NeZero n] : ∀ (l : ℕ), (rotMat n)^(n * l) = 1 := by
  intro l
  induction' l with l ih
  · simp
  · rw [mul_add, pow_add, ih, one_mul, mul_one]
    exact rot_id n

def refMat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 , 0 ; 0,  -1]

theorem ref_rot (n : ℕ) [NeZero n] :
    (rotMat n) * refMat = refMat * (rotMat n)^(n-1) := by
  rw [rot_l]
  unfold rotMat refMat
  ext i j
  fin_cases i <;> {
    fin_cases j <;> {
      simp
      try rw [← Real.cos_two_pi_sub]
      try rw [← Real.sin_two_pi_sub]
      congr 1
      have := NeZero.ne n; field_simp; ring
    }
  }


theorem ref_rot' (n: ℕ) [NeZero n] :
    (rotMat n)^(n-1) * refMat = refMat * rotMat n := by
  rw [rot_l]
  unfold rotMat refMat
  ext i j
  fin_cases i <;> {
    fin_cases j <;> {
      simp
      try rw [← Real.cos_two_pi_sub]
      try rw [← Real.sin_two_pi_sub]
      congr 1
      have := NeZero.ne n; field_simp; ring
    }
  }


theorem ref_ref_id : refMat * refMat  = 1:= by
  unfold refMat
  ext i j
  fin_cases i <;> {
    fin_cases j <;>  simp }


-- #check Nat.zero_le
theorem ref_rot_gen (n: ℕ) [NeZero n] :
    ∀ l', (l' < n) → (rotMat n)^l' = refMat * (rotMat n)^(n-l') * refMat  := by
  intro l' hl'
  induction' l' with l' ih
  · rw [pow_zero, tsub_zero, rot_id n, mul_one, ref_ref_id]
  rw [← Nat.sub_sub, ← mul_one (rotMat n ^ (n - l' - 1)), ← rot_id n, ← pow_add]
  have : n - l' - 1 + n = (n - l') + (n - 1) := by
    rw [add_comm]
    rw [← Nat.add_sub_assoc]
    rw [add_comm]
    rw [Nat.add_sub_assoc]
    exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    rw [@Order.one_le_iff_pos]
    exact  Nat.sub_pos_of_lt (Nat.lt_of_succ_lt hl')
  by_cases hl'' : l' < n
  · set ih' := ih hl''
  -- now we need to show rotMat n ^ (l' + 1) = refMat * rotMat n ^ (n - l' - 1 + n) * refMat
    rw [this]
    nth_rw 2 [pow_add]
    rw [← mul_one ((rotMat n) ^ (n - l')), ← ref_ref_id]
    repeat rw [← mul_assoc]
    rw [← ih']
    rw [mul_assoc, mul_assoc]
    nth_rw 2 [ ← mul_assoc]
    rw [pow_add, pow_one]
    congr 1
    rw [← ref_rot n, mul_assoc, ref_ref_id, mul_one]
  -- the other case which is a contradiction
  · have hl''' : l' < n :=  Nat.lt_of_succ_lt hl'
    contradiction


theorem ref_rot_id (n: ℕ) [NeZero n] :
    ∀ (l : ℕ), refMat * (rotMat n)^l * refMat * (rotMat n)^l = 1 := by
  intro l
  induction' l with l ih
  · simp
    exact ref_ref_id
  nth_rw 1 [pow_add, pow_one]
  nth_rw 1 [← mul_assoc]
  nth_rw 2 [mul_assoc]
  rw [ref_rot n]
  repeat rw [mul_assoc]
  rw [← pow_add, add_comm, add_assoc]
  rw [pow_add]
  repeat rw [← mul_assoc]
  rw [ih, one_mul]
  have : 1 + (n - 1) = n := have := NeZero.ne n; by omega
  rw [this, rot_id n]


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

-- #check LinearMap.toMatrix'_comp
-- #check Matrix.toLin'_mul


theorem stdmap_mul (n: ℕ) [NeZero n] :
    ∀ x y , stdmap n (x * y) = stdmap n x ∘ₗ stdmap n y := by
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
        have : k.val + l.val = (k + l).val + n := ZMod.val_add_val_of_le h
        rw [this, pow_add, rot_id n, mul_one]

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
        have : k.val + l.val = (k + l).val + n := ZMod.val_add_val_of_le h
        rw [this, pow_add, rot_id n, mul_one]

  |.sr l =>
    match x with
    |.r k =>
      rw [r_mul_sr]
      unfold stdmap
      simp
      repeat rw [← Matrix.toLin'_mul]
      congr 1

      set m := l-k
      have : l = m+k := by ring
      rw [this]

      by_cases h : m.val + k.val < n
      · have : (m + k).val = m.val + k.val :=  ZMod.val_add_of_lt h
        rw [this, add_comm, pow_add]
        repeat rw [← mul_assoc]
        congr 1
        nth_rw 1 [← one_mul ((rotMat n)^ k.val), ← ref_ref_id, ← mul_one refMat]
        repeat rw  [mul_assoc]
        congr 1
        repeat rw [← mul_assoc]
        rw [ref_rot_id n k.val]

        -- Alternatively,  after the first congr 1,
        -- nth_rw 1 [ref_rot_gen n k.val (ZMod.val_lt k)]
        -- nth_rw 2 [mul_assoc]
        -- rw [ref_ref_id, mul_one, mul_assoc, ← pow_add]
        -- rw [Nat.sub_add_cancel (ZMod.val_le k), rot_id n, mul_one]

      push_neg at h
      have : m.val + k.val = (m + k).val + n := ZMod.val_add_val_of_le h
      rw [← mul_one ((rotMat n) ^ ((m + k).val)), ← rot_id n, ← pow_add, ←this,
          add_comm, pow_add]
      repeat rw [← mul_assoc]
      congr 1
      nth_rw 1 [← one_mul ((rotMat n)^ k.val), ← ref_ref_id, ← mul_one refMat]
      repeat rw  [mul_assoc]
      congr 1
      repeat rw [← mul_assoc]
      rw [ref_rot_id n k.val]

      -- Alternatively,  after the first congr 1,
      -- nth_rw  1[← one_mul (rotMat n ^ k.val), ← ref_ref_id]
      -- nth_rw 1 [← mul_one refMat]
      -- repeat rw [mul_assoc]
      -- congr 1
      -- symm
      -- repeat rw [← mul_assoc]
      -- exact ref_rot_id n k.val

    |.sr k =>
      rw [sr_mul_sr]
      unfold stdmap
      simp
      repeat rw [← Matrix.toLin'_mul]
      congr 1

      set m := l-k
      have : l = m+k := by ring
      rw [this]

      by_cases h : m.val + k.val < n
      · have : (m + k).val = m.val + k.val :=  ZMod.val_add_of_lt h
        rw [this, add_comm, pow_add]
        repeat rw [← mul_assoc]
        rw [ref_rot_id n k.val, one_mul]

      push_neg at h
      have : m.val + k.val = (m + k).val + n := ZMod.val_add_val_of_le h
      rw [← mul_one ((rotMat n) ^ ((m + k).val)), ← rot_id n, ← pow_add, ←this,
          add_comm, pow_add]
      repeat rw [← mul_assoc]
      rw [ref_rot_id n k.val, one_mul]


def rep_example (n : ℕ) [NeZero n] : Representation ℝ (DihedralGroup n) V₂ where
  toFun := stdmap n -- (DihedralGroup n) → (V₂ →ₗ[ℂ] V₂)
  map_one' := stdmap_one n
  map_mul' := stdmap_mul n
