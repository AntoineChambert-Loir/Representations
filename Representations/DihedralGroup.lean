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
    DihedralGroup.r (-j) := by
  simp

variable {G : Type*} [Group G]

section
variable (f : DihedralGroup n →* G)

lemma hom_relation₁ : f (.r 1) ^ n = 1 := by
  rw [←map_pow, DihedralGroup.r_one_pow_n, map_one]

lemma hom_relation₂ : f (.sr 0) * f (.sr 0) = 1 := by
  rw [←map_mul, DihedralGroup.sr_mul_self 0, map_one]

lemma hom_relation₃ : f (.sr 0) * f (.r 1) * (f (.sr 0))⁻¹ = (f (.r 1))⁻¹ := by
  repeat rewrite [←map_mul, ←map_inv]
  rw [sr_conj_r, DihedralGroup.inv_r]

end

/-! # Lifting
Here, we construct the homomorphism out of the dihedral group into another group corresponding to given elements satisfying the relations.

We also show that the two constructions are inverse, defining an equivalence between homomorphisms and elements satisfying the relations. -/
section Lift
variable {r s : G} (h_a : r ^ n = 1) (h_b : s * s = 1) (h_ab : s * r * s⁻¹ = r⁻¹)

include h_a in
private lemma lift.lemma_add (i j : ZMod n) :
    r ^ ((i+j).cast : ℤ) = r ^ (i.cast : ℤ) * r ^ (j.cast : ℤ) := by
  conv => rhs; rewrite [←zpow_add, zpow_eq_zpow_emod' _ h_a]
  rw [ZMod.intCast_cast_add i j]

include h_a in
private lemma lift.lemma_sub (i j : ZMod n) :
    r ^ ((i-j).cast : ℤ) = r ^ (-j.cast : ℤ) * r ^ (i.cast : ℤ) := by
  conv => rhs; rewrite [←zpow_add, neg_add_eq_sub, zpow_eq_zpow_emod' _ h_a]
  rw [ZMod.intCast_cast_sub i j]

lemma _root_.Int.cases_ofNat_neg_ofNat (motive : ℤ → Prop)
    (ofNat : ∀ n : ℕ, motive n) (neg_ofNat : ∀ n : ℕ, motive (-n)) :
    ∀ n : ℤ, motive n :=
  Int.rec ofNat (neg_ofNat ·.succ)

include h_ab in
private lemma lift.lemma₂ : ∀ (n : ℤ), r ^ n * s = s * r ^ (-n) := by
  suffices this : ∀ (n : ℕ), r ^ n * s = s * r ^ (-n:ℤ) by
    apply Int.cases_ofNat_neg_ofNat
    · norm_cast
    · intro n
      apply mul_left_cancel (a := r ^ n) ∘ mul_right_cancel (b := r ^ (-n:ℤ)); symm
      group; rewrite [zpow_natCast]; apply this
  have h_ab : r * s = s * r⁻¹ := by
    apply mul_left_cancel (a := r⁻¹) ∘ mul_right_cancel (b := r * s⁻¹)
    group; simpa only [zpow_neg_one] using h_ab
  intro (n : ℕ); induction n
  case zero => group
  case succ n hᵢ =>
    conv => lhs; rewrite [pow_succ, mul_assoc, h_ab, ←mul_assoc, hᵢ]
    group

def lift : DihedralGroup n →* G where
  toFun := fun
  | .r i  => r ^ (i.cast:ℤ)
  | .sr i => s * r ^ (i.cast:ℤ)
  map_one' := by rewrite [DihedralGroup.one_def]; simp
  map_mul' x y := by
    cases x <;> cases y <;> simp
    case r.r => apply lift.lemma_add h_a
    case sr.r =>
      rewrite [mul_assoc]; apply congrArg (s * ·)
      apply lift.lemma_add h_a
    case r.sr =>
      rewrite [←mul_assoc, lift.lemma₂ h_ab]
      rewrite [mul_assoc]; apply congrArg (s * ·)
      apply lift.lemma_sub h_a
    case sr.sr =>
      rewrite [mul_assoc]; nth_rewrite 2 [←mul_assoc]; rewrite [lift.lemma₂ h_ab]
      rewrite [←mul_assoc, ←mul_assoc]; rewrite [h_b, one_mul]
      apply lift.lemma_sub h_a

@[simp]
lemma lift_apply_r (i : ZMod n) :
    lift h_a h_b h_ab (.r i) = r ^ (i.cast : ℤ) :=
  rfl

@[simp]
lemma lift_apply_r_one : lift h_a h_b h_ab (.r 1) = r := by
  -- This is not quite trivial when `n = 1`.
  dsimp [lift]
  rw [←Int.cast_one,
      ZMod.coe_intCast, ←zpow_eq_zpow_emod' _ (n := n) (zpow_natCast r n ▸ h_a),
      zpow_one]

@[simp]
lemma lift_apply_sr (i : ZMod n) :
    lift h_a h_b h_ab (.sr i) = s * r ^ (i.cast : ℤ) :=
  rfl
  /- by dsimp [lift]
  rw [zpow_eq_zpow_emod' i (n := ↑n) (zpow_natCast r n ▸ h_a), ZMod.coe_intCast] -/

@[simp]
lemma lift_apply_sr_zero :
    lift h_a h_b h_ab (.sr 0) = s := by
  rw [lift_apply_sr, ZMod.cast_zero]; group

end Lift

theorem hom_lift_eq_self (f : DihedralGroup n →* G) :
    lift (hom_relation₁ f) (hom_relation₂ f) (hom_relation₃ f) = f := by
  ext x; unfold lift; cases x <;> dsimp
  case' sr i =>
    conv => rhs; rewrite [←zero_add i]
    rw [←sr_mul_r 0 i, map_mul]
  all_goals (conv => rhs; rw [←r_one_pow_cast]); rw [map_zpow]

variable (n G) in
@[ext]
-- TODO better name!
private structure PresentationData where
  r : G
  s : G
  relation₁ : r ^ n = 1
  relation₂ : s * s = 1
  relation₃ : s * r * s⁻¹ = r⁻¹

/-- The universal property of `DihedralGroup n`.
The use of the structure `PresentationData` may be very unconventional. -/
def homEquiv : (DihedralGroup n →* G) ≃ PresentationData n G where
  toFun f := ⟨f (.r 1), f (.sr 0), hom_relation₁ f, hom_relation₂ f, hom_relation₃ f⟩
  invFun := fun ⟨_, _, h₁, h₂, h₃⟩ ↦ lift h₁ h₂ h₃
  left_inv := hom_lift_eq_self
  right_inv := by
    intro; ext
    · apply lift_apply_r_one
    · apply lift_apply_sr_zero

end DihedralGroup
