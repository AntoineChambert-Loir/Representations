import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic.NoncommRing

variable {n: ℕ} {G: Type*} [Monoid G]

example {G': Type*} [Group G'] {a: G'} {a_pow_n_eq_one: a^n = 1} {k l: ℕ} :
    k ≡ l [ZMOD n] → a^k = a^l := by
  intro h
  refine pow_eq_pow_iff_modEq.mpr ?_
  apply Int.natCast_modEq_iff.mp
  apply orderOf_dvd_of_pow_eq_one at a_pow_n_eq_one
  have ⟨k, kh⟩ := dvd_def.mp a_pow_n_eq_one
  rw [kh] at h
  simpa using Int.ModEq.of_mul_right k h

lemma pow_eq_pow_of_ModEq {a: G} {i j n: ℕ}
    (h₁: a^n = 1) (h₂: i ≡ j [MOD n]) : a^i = a^j := by
  wlog i_le_j: i ≤ j
  · exact (this h₁ h₂.symm $ le_of_not_ge i_le_j).symm
  · let ⟨k, hk⟩ := (Nat.modEq_iff_dvd' i_le_j).mp h₂
    apply Nat.eq_add_of_sub_eq i_le_j at hk
    simp [hk, pow_add, pow_mul, h₁]

/-
lemma rel_two_eq_xa_right {a x: G} {i j: ℕ} (h₁: i ≤ j) (h₂: a * x * a = x):
    a^i * x * a^j = x * a^(j - i) := by
  if i_zero: i = 0 then
    simp [i_zero]
  else
    conv_lhs => rw [<-Nat.succ_pred_eq_of_ne_zero i_zero]
    have i_ge_one: i ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr i_zero
    conv_lhs => rw [<-Nat.add_sub_of_le (le_trans i_ge_one h₁)]
    conv_lhs => calc a^(i - 1 + 1) * x * a^(1 + (j - 1))
      _ = (a^(i - 1) * a) * x * (a * a^(j - 1)) := by simp [pow_add]
      _ = a^(i - 1) * (a * x * a) * a^(j - 1) := by group
      _ = a^(i - 1) * x * a^(j - 1) := by simp [h₂]

    have := rel_two_eq_xa_right (i := i - 1) (j := j - 1) (by exact Nat.sub_le_sub_right h₁ 1) h₂
    rw [Nat.sub_sub_sub_cancel_right i_ge_one] at this
    exact this
-/

lemma rel_two_eq_xa_zpow {G: Type*} [Group G] {a x: G} {i j: ℤ} (h₂: a * x * a = x):
    a^i * x * a^j = x * a^(j - i) := by
  induction i with
    | zero => simp
    | pred k hk =>
      conv_lhs => calc a^(-(k: ℤ) - 1) * x * a^j
        _ = a^(-1: ℤ) * (a^(-k: ℤ) * x * a^j) := by group
        _ = a^(-1: ℤ) * ((a * x * a) * a^(j - -k)) := by rw [hk, h₂]
      group
    | succ k hk =>
      conv_lhs => calc a^((k: ℤ) + 1) * x * a^j
        _ = a * (a^(k: ℤ) * x * a^j) := by group
        _ = a * (x * a^(j - k)) := by rw [hk]
        _ = (a * x * a) * a^(j - (k + 1)) := by group
      rw [h₂]

lemma rel_two_eq_xa {a x: G} [NeZero n] {i j: ZMod n}
    (h₁: a^n = 1) (h₂: a * x * a = x):
    a^i.val * x * a^j.val = x * a^(j - i).val := by
  if n_one: n = 1 then
    subst n_one
    fin_cases i; fin_cases j
    simp
  else if i_val_zero: i.val = 0 then
    simp [i.val_eq_zero.mp i_val_zero]
  else
    have : a^j.val = a^(1 + (j - 1).val) := by
      apply pow_eq_pow_of_ModEq h₁
      simp [pow_eq_pow_of_ModEq h₁, <-ZMod.eq_iff_modEq_nat]
    rw [this]
    conv_lhs => calc a^i.val * x * a^(1 + (j - 1).val)
      _ = a^i.val.pred.succ * x * a^(1 + (j - 1).val) := by rw [Nat.succ_pred i_val_zero]
      _ = (a^i.val.pred * a) * x * (a * a^(j - 1).val) := by simp [pow_add]
      _ = a^i.val.pred * (a * x * a) * a^(j - 1).val := by group
      _ = a^(i.val - 1) * x * a^(j - 1).val := by simp [h₂]
      _ = a^(i.val - ZMod.val 1) * x * a^(j - 1).val := by rw [ZMod.val_one'' n_one]

    have : (i - 1).val = i.val - ZMod.val (1: ZMod n) := by
      apply ZMod.val_sub
      simp [ZMod.val_one'' n_one]
      exact Nat.one_le_iff_ne_zero.mpr i_val_zero
    rw [<-this]

    have : (i - 1).val < i.val := by
      rw [ZMod.val_sub ?_]
      <;> simp [ZMod.val_one'' n_one]
      · exact Nat.zero_lt_of_ne_zero i_val_zero
      · exact Nat.one_le_iff_ne_zero.mpr i_val_zero
    have := rel_two_eq_xa (i := i - 1) (j := j - 1) h₁ h₂
    rw [sub_sub_sub_cancel_right] at this
    exact this
termination_by i.val

namespace QuaternionGroup

def lift [NeZero n] (a x: G)
    (h₁: a^(2 * n) = 1) (h₂: x^2 = a^n) (h₃: a * x * a = x):
    QuaternionGroup n →* G where
  toFun := fun g => match g with
    | .a k => a ^ k.val
    | .xa k => x * a ^ k.val
  map_one' := by rw [one_def]; simp
  map_mul' := by
    intro g₁ g₂
    obtain l | l := g₁
    <;> obtain m | m := g₂
    <;> simp

    case' a.a => rw [<-pow_add]
    case' xa.a => rw [(?_: a^(l + m).val = a^(l.val + m.val)), mul_assoc, <-pow_add]
    case a.a | xa.a => apply pow_eq_pow_of_ModEq h₁; simp [←ZMod.eq_iff_modEq_nat]

    · rw [<-mul_assoc, <-rel_two_eq_xa h₁ h₃]
    · conv_rhs => calc x * a^l.val * (x * a^m.val)
        _ = x * (a^l.val * x * a^m.val) := by noncomm_ring
        _ = x * (x * a^(m - l).val) := by rw [rel_two_eq_xa h₁ h₃]
        _ = x^2 * a^(m - l).val := by noncomm_ring
        _ = a^n * a^(m - l).val := by rw [h₂]
        _ = a^(n + (m - l).val) := by rw [<-pow_add]
      apply pow_eq_pow_of_ModEq h₁
      simp [<-ZMod.eq_iff_modEq_nat]
      ring

def lift_nzero_to_group {G: Type*} [Group G] (a x: G) (h₁: x^2 = 1) (h₂: a * x * a = x):
    QuaternionGroup 0 →* G where
  toFun := fun g => match g with
    | .a (k: ℤ) => a^k
    | .xa (k: ℤ) => x * a^k
  map_one' := by rw [one_def]; simp
  map_mul' := by
    intro g₁ g₂
    obtain (l: ℤ) | (l: ℤ) := g₁
    <;> obtain (m: ℤ) | (m: ℤ) := g₂
    · simp [<-zpow_add]
    · simp [<-mul_assoc, rel_two_eq_xa_zpow h₂]
    · simp [mul_assoc, <-zpow_add]
    · conv_rhs => calc x * a^l * (x * a^m)
        _ = x * (a^l * x * a^m) := by group
        _ = x * (x * a^(m - l)) := by rw [rel_two_eq_xa_zpow h₂]
        _ = x^2 * a^(m - l) := by noncomm_ring
      simp [h₁]

def lift_nzero (a x: G) (h₁: x^2 = 1) (h₂: a * x * a = x):
    QuaternionGroup 0 →* G :=
  let a': Gˣ := Units.mk
    (val := a)
    (inv := x * a * x)
    (val_inv := by 
      rw [(by group: a * (x * a * x) = (a * x * a) * x)]
      rw [h₂, <-pow_two, h₁]
    )
    (inv_val := by
      rw [(by group: (x * a * x) * a = x * (a * x * a))]
      rw [h₂, <-pow_two, h₁]
    )
  let x': Gˣ := Units.mk
    (val := x)
    (inv := x)
    (val_inv := by rw [<-pow_two, h₁])
    (inv_val := by rw [<-pow_two, h₁])
  have h₂': a' * x' * a' = x' := by
    apply Units.ext_iff.mpr
    repeat rw [Units.val_mul]
    exact h₂
  {
    toFun g := match g with
      | .a (k: ℤ) => Units.instGroup.zpow k a'
      | .xa (k: ℤ) => x' * Units.instGroup.zpow k a'
    map_one' := by rw [one_def]; simp
    map_mul' := by
      intro g₁ g₂
      obtain (l: ℤ) | (l: ℤ) := g₁
      <;> obtain (m: ℤ) | (m: ℤ) := g₂
      <;> simp [a_mul_xa, Nat.mul_zero, zpow_eq_pow, <-Units.val_mul]
      <;> apply Units.ext_iff.mp
      · rw [<-zpow_add]
      · rw [<-mul_assoc, rel_two_eq_xa_zpow h₂']
      · rw [mul_assoc, <-zpow_add]
      · rw [(by group: x' * a'^l * (x' * a'^m) = x' * (a'^l * x' * a'^m))]
        rw [rel_two_eq_xa_zpow h₂', <-mul_assoc]
        rw [(Units.val_eq_one.mp x'.inv_val: x' * x' = 1), one_mul]
  }

end QuaternionGroup
