import Representations.Basic

import Mathlib

variable (n: ℕ) (G: Type*) [Monoid G]

example {G': Type*} [Group G'] {a: G'} {a_pow_n_eq_one: a^n = 1} {k l: ℕ} : k ≡ l [ZMOD n] → a^k = a^l := by
  intro h
  refine pow_eq_pow_iff_modEq.mpr ?_
  apply Int.natCast_modEq_iff.mp
  apply orderOf_dvd_of_pow_eq_one at a_pow_n_eq_one
  have ⟨k, kh⟩ := dvd_def.mp a_pow_n_eq_one
  rw [kh] at h
  simpa using Int.ModEq.of_mul_right k h

lemma pow_eq_pow_of_ModEq {G: Type*} [Monoid G] {a: G} {i j n: ℕ} (h₁: a^n = 1) (h₂: i ≡ j [MOD n]) : a^i = a^j := by
  wlog i_le_j: i ≤ j
  · exact (this h₁ h₂.symm $ le_of_not_ge i_le_j).symm
  · let ⟨k, hk⟩ := (Nat.modEq_iff_dvd' i_le_j).mp h₂
    apply Nat.eq_add_of_sub_eq i_le_j at hk
    simp [hk, pow_add, pow_mul, h₁]

lemma rel_two_eq_xa {G: Type*} [Monoid G] {a x: G} {n: ℕ} [NeZero n] {i j: ZMod n} (h₁: a^n = 1) (h₂: a * x * a = x): 
    a^i.val * x * a^j.val = x * a^(j - i).val := by
  if n_one: n = 1 then
    subst n_one
    fin_cases i
    fin_cases j
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
    have := @rel_two_eq_xa G _ _ _ _ _ (i - 1) (j - 1) h₁ h₂
    rw [sub_sub_sub_cancel_right] at this
    exact this

termination_by i.val

def lift [NeZero n] (a x: G) (h₁: a^(2 * n) = 1) (h₂: x^2 = a^n) (h₃: a * x * a = x):
    QuaternionGroup n →* G where
  toFun := fun g => match g with
    | .a k => a ^ k.val
    | .xa k => x * a ^ k.val
  map_one' := by
    rw [(by rfl: (1: QuaternionGroup n) = .a 0)]
    simp
  map_mul' := by
    intro g₁ g₂
    obtain l | l := g₁
    <;> obtain m | m := g₂
    <;> simp

    case' a.a => rw [<-pow_add]
    case' xa.a => rw [(?_: a^(l + m).val = a^(l.val + m.val)), mul_assoc, <-pow_add]
    case a.a | xa.a => exact pow_eq_pow_of_ModEq h₁ (by simp [<-ZMod.eq_iff_modEq_nat])

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

