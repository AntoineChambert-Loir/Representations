import Mathlib.GroupTheory.SpecificGroups.Dihedral

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

/-! # The Relations
Here, we prove (or demonstrate that Mathlib has already proved) that the relations hold in the dihedral group and for any homomorphism out of the dihedral group.
-/
example : (DihedralGroup.r 1 : DihedralGroup n) ^ n = 1 :=
  DihedralGroup.r_one_pow_n

example : (DihedralGroup.sr 0 : DihedralGroup n) * DihedralGroup.sr 0 = 1 :=
  DihedralGroup.sr_mul_self 0

lemma sr_conj_r (i j : ZMod n) :
    (DihedralGroup.sr i : DihedralGroup n) *
      DihedralGroup.r j * (DihedralGroup.sr i)⁻¹ =
    DihedralGroup.r (-j) :=
  show DihedralGroup.r (i - (i + j)) = DihedralGroup.r (-j) by
  abel_nf

lemma r_mul_sr_mul_r' (i j k : ZMod n) :
    (DihedralGroup.r i : DihedralGroup n) *
      DihedralGroup.sr j * DihedralGroup.r k =
    DihedralGroup.sr (j + (k - i)) :=
  show DihedralGroup.sr (j - i + k) = DihedralGroup.sr (j + (k - i)) by
  abel_nf

lemma r_mul_sr_mul_r (i j : ZMod n) :
    (DihedralGroup.r i : DihedralGroup n) *
      DihedralGroup.sr j * DihedralGroup.r i =
    DihedralGroup.sr j := by
  have := r_mul_sr_mul_r' i j i
  rwa [sub_self i, add_zero j] at this

/-!
# Lifting
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

-- example {G H} [Group G] [Monoid H] (f : G →* H) (x : G) (n : ℤ) : f (x ^ n) = _ := sorry

example {G H} [Group G] [Monoid H] (f : G →* H) : G →* Hˣ := f.toHomUnits

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
  val_inv := by rewrite [←mul_assoc, ←mul_assoc]; rw [h_rs, h_s]
  inv_val := by rewrite [mul_assoc, mul_assoc]; nth_rewrite 2 [←mul_assoc]; rw [h_rs, h_s]

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

end DihedralGroup
