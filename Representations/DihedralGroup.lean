import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Basic

variable {n : ℕ}

namespace DihedralGroup

/-! # Extra lemmas about `DihedralGroup` -/
section MissingLemmas

@[simp]
lemma r_pow_cast (i j : ZMod n) :
    (.r i : DihedralGroup n) ^ (j.cast : ℤ) = .r (i * j) := by
  simp

@[simp]
lemma r_one_pow_cast (i : ZMod n) :
    (.r 1 : DihedralGroup n) ^ (i.cast : ℤ) = .r i := by
  simp

end MissingLemmas

/-!
# Presentation
In this section, we prove that `DihedralGroup n` has the presentation $\langle r, s : r^n = 1, s^2 = 1, rsr = s \rangle$.

## Relations
Here, we prove (or demonstrate that Mathlib has already proved) that the relations hold in the dihedral group and for any homomorphism out of the dihedral group.
-/
example : (DihedralGroup.r 1 : DihedralGroup n) ^ n = 1 :=
  DihedralGroup.r_one_pow_n

example : (DihedralGroup.sr 0 : DihedralGroup n) * DihedralGroup.sr 0 = 1 :=
  DihedralGroup.sr_mul_self 0

lemma sr_conj_r (i j : ZMod n) :
    (DihedralGroup.sr i : DihedralGroup n) *
        DihedralGroup.r j * (DihedralGroup.sr i)⁻¹
    = DihedralGroup.r (-j) :=
  show DihedralGroup.r (i - (i + j)) = DihedralGroup.r (-j) by
  abel_nf

lemma r_mul_sr_mul_r' (i j k : ZMod n) :
    (DihedralGroup.r i : DihedralGroup n) *
        DihedralGroup.sr j * DihedralGroup.r k
    = DihedralGroup.sr (j + (k - i)) :=
  show DihedralGroup.sr (j - i + k) = DihedralGroup.sr (j + (k - i)) by
  abel_nf

lemma r_mul_sr_mul_r (i j : ZMod n) :
    (DihedralGroup.r i : DihedralGroup n) *
        DihedralGroup.sr j * DihedralGroup.r i
    = DihedralGroup.sr j := by
  have := r_mul_sr_mul_r' i j i
  rwa [sub_self i, add_zero j] at this

/-!
## Lifting
Here, we construct the homomorphism out of the dihedral group into another group corresponding to given elements satisfying the relations.

We also show that the two constructions are inverse, defining an equivalence between homomorphisms and elements satisfying the relations.
-/

section UniversalProperty

variable {G : Type*} [Monoid G]

section Relations
variable (f : DihedralGroup n →* G)

lemma hom_relation₁ : f (.r 1) ^ n = 1 := by
  rw [←map_pow, DihedralGroup.r_one_pow_n, map_one]

lemma hom_relation₂ : f (.sr 0) * f (.sr 0) = 1 := by
  rw [←map_mul, DihedralGroup.sr_mul_self 0, map_one]

lemma hom_relation₃ : f (.r 1) * f (.sr 0) * f (.r 1) = f (.sr 0) := by
  repeat rewrite [←map_mul]
  rw [r_mul_sr_mul_r]

/-
lemma hom_relation₃' [Group G] (f : DihedralGroup n →* G) :
    f (.sr 0) * f (.r 1) * (f (.sr 0))⁻¹ = (f (.r 1))⁻¹ := by
  repeat rewrite [←map_mul, ←map_inv]
  rw [sr_conj_r, DihedralGroup.inv_r]
-/

-- These are dangerous as simp lemmas for some reason related to applying it to Gˣˣˣ...
lemma hom_apply_r (i : ZMod n) :
    (f (.r i) : G) = ((f.toHomUnits (.r 1)) ^ (i.cast : ℤ) : Gˣ) := by
  conv => lhs; rw [←f.coe_toHomUnits, ←i.intCast_zmod_cast, ←r_one_zpow, map_zpow]

lemma hom_apply_sr (i : ZMod n) :
    (f (.sr i) : G) = f (.sr 0) * ((f.toHomUnits (.r 1)) ^ (i.cast : ℤ) : Gˣ) := by
  nth_rewrite 1 2 [←f.coe_toHomUnits, ←f.coe_toHomUnits]; norm_cast
  rw [←map_zpow, ←map_mul]; congr 1; simp

end Relations

section Lift
variable {r s : G} (h_r : r ^ n = 1) (h_s : s * s = 1) (h_rs : r * s * r = s)

private def lift.r_ : Gˣ where
  val := r
  inv := s * r * s
  val_inv := by rewrite [←mul_assoc, ←mul_assoc]
                rw [h_rs, h_s]
  inv_val := by rewrite [mul_assoc, mul_assoc]; nth_rewrite 2 [←mul_assoc]
                rw [h_rs, h_s]

private def lift.s_ : Gˣ := ⟨s, s, h_s, h_s⟩

local notation "r_" => lift.r_ h_s h_rs
local notation "s_" => lift.s_ h_s

include h_r in
private lemma lift.lemma_add (i j : ZMod n) :
    r_ ^ ((i+j).cast : ℤ) = r_ ^ (i.cast : ℤ) * r_ ^ (j.cast : ℤ) := by
  conv => rhs; rewrite [←zpow_add, zpow_eq_zpow_emod' _ (Units.ext h_r)]
  rw [ZMod.intCast_cast_add i j]

include h_r in
private lemma lift.lemma_sub (i j : ZMod n) :
    r_ ^ ((i-j).cast : ℤ) = r_ ^ (-j.cast : ℤ) * r_ ^ (i.cast : ℤ) := by
  conv => rhs; rewrite [←zpow_add, neg_add_eq_sub, zpow_eq_zpow_emod' _ (Units.ext h_r)]
  rw [ZMod.intCast_cast_sub i j]

lemma _root_.Int.cases_ofNat_neg_ofNat (motive : ℤ → Prop)
    (ofNat : ∀ n : ℕ, motive n) (neg_ofNat : ∀ n : ℕ, motive (-n)) :
    ∀ n : ℤ, motive n :=
  Int.rec ofNat (neg_ofNat ·.succ)

include h_rs in
private lemma lift.lemma₂ :
    ∀ (n : ℤ), (r_ ^ n : Gˣ) * s = s * (r_ ^ (-n) : Gˣ) := by
  suffices this : ∀ (n : ℕ), r_ ^ n * s_ = s_ * (r_ ^ (-n:ℤ) : Gˣ) by
    apply Int.cases_ofNat_neg_ofNat <;>
       (intro n; specialize this n;
        conv => lhs; arg 2; rewrite [(show s = (s_).val from rfl)]
        conv => rhs; arg 1; rewrite [(show s = (s_).val from rfl)]
        norm_cast)
    case neg_ofNat =>
      apply mul_left_cancel (a := (r_ ^ n : Gˣ))
      apply mul_right_cancel (b := (r_ ^ (-n:ℤ) : Gˣ))
      symm
      group; rewrite [zpow_natCast]; apply this
  have h_ab : r_ * s_ = s_ * r_⁻¹ := by
    apply mul_right_cancel (b := r_)
    group; simpa only [zpow_neg_one] using (Units.ext h_rs)
  intro (n : ℕ); induction n
  case zero => group
  case succ n hᵢ =>
    conv => lhs; rewrite [pow_succ, mul_assoc, h_ab, ←mul_assoc, hᵢ]
    group

def lift : DihedralGroup n →* G where
  toFun := fun
  | .r i  => (r_ ^ (i.cast : ℤ) : Gˣ)
  | .sr i => s * (r_ ^ (i.cast : ℤ) : Gˣ)
  map_one' := by rewrite [DihedralGroup.one_def]; simp
  map_mul' x y := by
    cases x <;> cases y <;> (simp; norm_cast)
    -- Reduce case 3 to case 1...
    case' sr.r => rewrite [mul_assoc]; apply congrArg (s * ·); norm_cast
    -- ... and solve using `lemma_add`.
    case r.r | sr.r => apply lift.lemma_add h_r
    case' r.sr =>
      rewrite [←mul_assoc, lift.lemma₂ h_s h_rs]
      rewrite [mul_assoc]; apply congrArg (s * ·)
    case' sr.sr =>
      rewrite [mul_assoc]; nth_rewrite 2 [←mul_assoc]; rewrite [lift.lemma₂ h_s h_rs]
      rewrite [←mul_assoc, ←mul_assoc]
      rewrite [h_s, one_mul]
    case r.sr | sr.sr => norm_cast; apply lift.lemma_sub h_r

@[simp]
lemma lift_apply_r_of_ne_zero [NeZero n] (i : ZMod n) :
    lift h_r h_s h_rs (.r i) = r ^ i.val := by
  simp only [lift, lift.r_, MonoidHom.coe_mk, OneHom.coe_mk, ←i.natCast_val]
  norm_cast

@[simp]
lemma lift_apply_r_nat (i : ℕ) :
    lift h_r h_s h_rs (.r i) = r ^ i := by
  cases n
  · rfl
  · simp [lift_apply_r_of_ne_zero, pow_eq_pow_mod i h_r]

@[simp]
lemma lift_apply_sr_of_ne_zero [NeZero n] (i : ZMod n) :
    lift h_r h_s h_rs (.sr i) = s * r ^ i.val := by
  simp only [lift, lift.r_, MonoidHom.coe_mk, OneHom.coe_mk, ←i.natCast_val]
  norm_cast

@[simp]
lemma lift_apply_sr_nat (i : ℕ) :
    lift h_r h_s h_rs (.sr i) = s * r ^ i := by
  cases n
  · simp [lift, lift.r_]
  · simp [lift_apply_sr_of_ne_zero, pow_eq_pow_mod i h_r]

end Lift

theorem hom_lift_eq_self (f : DihedralGroup n →* G) :
    lift (hom_relation₁ f) (hom_relation₂ f) (hom_relation₃ f) = f := by
  ext x; /- unfold lift lift.r_ lift.s_; -/
  cases x <;> (
  rename_i i
  conv =>
    rhs
    try rewrite [←zero_add i, ←sr_mul_r 0 i, map_mul]
    repeat rewrite [←f.coe_toHomUnits]
    rw [←r_one_pow_cast, map_zpow]
  have : f (.sr 0) * f (.r 1) * f (.sr 0) = f (.r 1)⁻¹ := by simp [←map_mul f]
  simp [lift, lift.r_]; congr)

variable (n G) in
@[ext]
-- TODO better name!
private structure PresentationData where
  r : G
  s : G
  relation₁ : r ^ n = 1
  relation₂ : s * s = 1
  relation₃ : r * s * r = s

/-- The universal property of `DihedralGroup n`.
The use of the structure `PresentationData` may be very unconventional. -/
def homEquiv : (DihedralGroup n →* G) ≃ PresentationData n G where
  toFun f := ⟨f (.r 1), f (.sr 0), hom_relation₁ f, hom_relation₂ f, hom_relation₃ f⟩
  invFun := fun ⟨_, _, h_r, h_s, h_rs⟩ ↦ lift h_r h_s h_rs
  left_inv := hom_lift_eq_self
  right_inv := by
    intro ⟨r', s, h_r, h_s, h_rs⟩; ext
    · have := lift_apply_r_nat h_r h_s h_rs 1
      rwa [Nat.cast_one, pow_one] at this
    · simp [lift, lift_apply_sr_nat]

end UniversalProperty

/-! # Construction of standard 2-dimensional representations -/
section Real2DRepresentation

-- how to work with points in (Fin 2 → ℝ)
example : Fin 2 → ℝ := ![1, 0]

example : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

example : Fin 2 → ℝ := fun
  | 0 => 1
  | 1 => 0

-- how to work with maps (Fin 2 → ℝ) → (Fin 2 → ℝ)
example : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
  fun v => fun i => 2 * v i

-- noncomputable def matrixToLin (M : GL (Fin 2) ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ where
--   toFun := fun v => fun i => ∑ j, M i j * v j
--   map_add' := sorry
--   map_smul' := sorry

noncomputable example : GL (Fin 2) ℝ →* (Fin 2 → ℝ) ≃ₗ[ℝ] Fin 2 → ℝ := by
  let u := Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ℝ)
  let v := LinearMap.GeneralLinearGroup.generalLinearEquiv (R := ℝ) (Fin 2 → ℝ)
  let w := u.trans v
  exact w.toMonoidHom

noncomputable example : GL (Fin 2) ℝ →* (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ := by
  let e : LinearMap.GeneralLinearGroup ℝ (Fin 2 → ℝ) →* Module.End ℝ (Fin 2 → ℝ) :=
    DistribMulAction.toModuleEnd ℝ (Fin 2 → ℝ)
  let u := Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ℝ)
  exact e.comp u.toMonoidHom

open Real

noncomputable abbrev rotationMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ, -sin θ;
     sin θ,  cos θ]

theorem rotationMatrix_pow (θ : ℝ) (l : ℕ) :
    (rotationMatrix θ) ^ l = rotationMatrix (θ * l) := by
  induction' l with l ih
  · simp [rotationMatrix]; apply Matrix.one_fin_two
  · rw [pow_add, ih]
    unfold rotationMatrix
    ext i j
    fin_cases i <;> fin_cases j <;> (
      simp
      rw [mul_add]
      try rw [Real.sin_add]
      try rw [Real.cos_add]
      ring_nf
    )

theorem rotationMatrix_pow_n (i : ℤ) :
    rotationMatrix (2 * π * i / n) ^ n = 1 := by
  by_cases h:n = 0
  · subst h; rfl
  · haveI : NeZero n := ⟨h⟩
    rw [rotationMatrix_pow]
    have h₁ : cos (2 * π * i) = 1 := by
      convert cos_int_mul_two_pi i using 2; ring
    have h₂ : sin (2 * π * i) = 0 := by
      convert sin_int_mul_pi (2 * i) using 2; push_cast; ring
    ext i j; fin_cases i <;> fin_cases j <;> simpa

abbrev reflectionMatrix /- (θ : ℝ) -/ : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,  0;
     0, -1]

theorem reflectionMatrix_mul_self : reflectionMatrix * reflectionMatrix = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem reflectionMatrix_conj_rotationMatrix (θ : ℝ) :
    reflectionMatrix * rotationMatrix θ * reflectionMatrix⁻¹
    = rotationMatrix (-θ) := by
  rewrite [show reflectionMatrix⁻¹ = reflectionMatrix by unfold Matrix.inv; simp]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem rot_mul_refl_mul_rot_eq_refl (θ : ℝ) :
    rotationMatrix θ * reflectionMatrix * rotationMatrix θ = reflectionMatrix := by
  ext i j; fin_cases i <;> fin_cases j <;> unfold rotationMatrix reflectionMatrix
  case «0».«0» => simp [←pow_two, cos_sq_add_sin_sq θ]
  case «1».«1» => have := congrArg Neg.neg (cos_sq_add_sin_sq θ); simp_all [pow_two]
  case «0».«1» | «1».«0» => simp [mul_comm]

section GLApproach

-- example of obtaining an element of GL given a matrix and proof of invertibility
noncomputable example (t : Matrix (Fin 2) (Fin 2) ℝ) (h : IsUnit t) : GL (Fin 2) ℝ := h.unit

lemma reflectionMatrix_is_unit : IsUnit reflectionMatrix := by
    rw [isUnit_iff_exists]
    use reflectionMatrix
    constructor
    . exact reflectionMatrix_mul_self
    . exact reflectionMatrix_mul_self

noncomputable def reflectionMatrix_unit : GL (Fin 2) ℝ :=
    reflectionMatrix_is_unit.unit

lemma reflectionMatrix_unit_mul_self :
    reflectionMatrix_unit * reflectionMatrix_unit = 1 := by
  dsimp [reflectionMatrix_unit]
  rw [Units.ext_iff]
  exact reflectionMatrix_mul_self

lemma reflectionMatrix_unit_eq_inv_self :
    reflectionMatrix_unit⁻¹ = reflectionMatrix_unit := by
  rw [@inv_eq_iff_mul_eq_one]
  exact reflectionMatrix_unit_mul_self

lemma rotM_isUnit: ∀ (θ : ℝ), IsUnit (rotationMatrix (θ : ℝ)):= by
  intro θ
  let A := rotationMatrix (θ : ℝ)
  have hA1: A.det =  1 := by
    unfold A
    simp
    repeat rw [← pow_two]
    rw [cos_sq_add_sin_sq]
  simp only [Matrix.isUnit_iff_isUnit_det]
  rw [hA1]
  exact isUnit_one

noncomputable def rotationMatrix_unit (θ : ℝ): GL (Fin 2) ℝ := by
  have h : IsUnit (rotationMatrix (θ : ℝ)):= by exact rotM_isUnit θ
  exact h.unit

lemma rotationMatrix_unit_pow (θ : ℝ) (l : ℕ) :
    (rotationMatrix_unit θ) ^ l = rotationMatrix_unit (θ * l) := by
  dsimp [rotationMatrix_unit]
  rw [Units.ext_iff]
  exact rotationMatrix_pow θ l

theorem rotationMatrix_unit_pow_n (i : ℤ) :
    rotationMatrix_unit (2 * π * i / n) ^ n = 1 := by
  dsimp [rotationMatrix_unit]
  rw [Units.ext_iff]
  exact rotationMatrix_pow_n i

lemma conj_relation :
    reflectionMatrix * rotationMatrix (2 * π / ↑n) *
        reflectionMatrix * rotationMatrix (2 * π / ↑n)
    = 1 := by
  ext i j
  simp
  fin_cases i <;> fin_cases j
  case «0».«0» | «1».«1» => simp [←pow_two, cos_sq_add_sin_sq]
  case «0».«1» | «1».«0» => ring_nf; simp

lemma conj_unit_relation :
    reflectionMatrix_unit * rotationMatrix_unit (2 * π / ↑n) *
        reflectionMatrix_unit * rotationMatrix_unit (2 * π / ↑n)
    = 1 := by
  dsimp [reflectionMatrix_unit, rotationMatrix_unit]
  rw [Units.ext_iff]
  exact conj_relation

theorem rot_mul_refl_mul_rot_eq_refl_unit (θ : ℝ) :
    rotationMatrix_unit θ * reflectionMatrix_unit * rotationMatrix_unit θ
    = reflectionMatrix_unit := by
  ext : 1; push_cast; exact rot_mul_refl_mul_rot_eq_refl θ

noncomputable def representation :
    Representation ℝ (DihedralGroup n) (Fin 2 → ℝ) := by
  dsimp [Representation]
  let G := GL (Fin 2) ℝ
  let r : G := rotationMatrix_unit (2 * π / n)
  let s : G := reflectionMatrix_unit
  have h_a : r ^ n = 1 := by
    cases Nat.eq_zero_or_pos n with
      | inl h_zero  => rw [pow_eq_one_iff_modEq, h_zero]

      | inr h_pos =>
        haveI : NeZero n := NeZero.of_pos h_pos

        unfold r
        --have hmodify : rotationMatrix_unit (2 * π / n) ^ n
        --               = rotationMatrix_unit (2 * π * 1 / n) ^ n := by
        --  simp only [mul_one]
        --rw [hmodify]
        have hl2 : rotationMatrix_unit (2 * π * (1 : ℤ)/ ↑n) ^ n
                   = rotationMatrix_unit (2 * π / ↑n) ^ n := by
          have h : 2 * π * (1: ℤ) / n = 2 * π / n := by
            simp only [Int.cast_one, mul_one]
          rw [h]
        rw [← hl2]
        rw [rotationMatrix_unit_pow_n (1 : ℤ)]

  have h_b : s * s = 1 := reflectionMatrix_unit_mul_self
  have h_ab : r * s * r = s := by
    unfold r s
    symm; rewrite [←inv_mul_eq_one, reflectionMatrix_unit_eq_inv_self]
    simp only [←mul_assoc] -- left-associate
    exact conj_unit_relation
  let φ := lift h_a h_b h_ab
  exact ((DistribMulAction.toModuleEnd ℝ (Fin 2 → ℝ)).comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom).comp φ

end GLApproach

end Real2DRepresentation

end DihedralGroup
