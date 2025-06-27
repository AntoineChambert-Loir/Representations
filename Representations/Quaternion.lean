import Representations.Basic

import Mathlib

variable (n: ℕ) (G: Type*) [Monoid G]

open QuaternionGroup

variable {n: ℕ}

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

/-
lemma rel_two_eq_xa_right {G: Type*} [Monoid G] {a x: G} {i j: ℕ} (h₁: i ≤ j) (h₂: a * x * a = x): 
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

lemma rel_two_eq_xa {G: Type*} [Monoid G] {a x: G} {n: ℕ} [NeZero n] {i j: ZMod n} (h₁: a^n = 1) (h₂: a * x * a = x):
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

def lift [NeZero n] (a x: G) (h₁: a^(2 * n) = 1) (h₂: x^2 = a^n) (h₃: a * x * a = x):
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

def lift_nzero {G: Type*} [Monoid G] (a x: G) (h₁: x^2 = 1) (h₂: a * x * a = x):
    QuaternionGroup 0 →* G :=
  let f: QuaternionGroup 0 → G := fun g => match g with
    | .a (k: ℤ) => if k ≥ 0 then a^k.natAbs else x * a^k.natAbs * x
    | .xa (k: ℤ) => if k ≥ 0 then x * a^k.natAbs else a^k.natAbs * x
  {
    toFun := f
    map_one' := by unfold f; rw [one_def]; simp
    map_mul' := by
      have a_unit: IsUnit a := isUnit_iff_exists.mpr $ by
        use x * a * x
        split_ands
        · group; rw [h₂, <-pow_two, h₁]
        · rw [(by group: x * a * x * a = x * (a * x * a)), h₂, <-pow_two, h₁]
      have x_unit: IsUnit x := isUnit_iff_exists.mpr $ by
        use x
        split_ands <;> rw [<-pow_two, h₁]
      have factor_through_units: ∀g: QuaternionGroup 0, IsUnit (f g) := by
        intro g
        obtain (k: ℤ) | (k: ℤ) := g
        <;> obtain ge_zero | lt_zero := (by omega: k ≥ 0 ∨ k < 0)
        <;> (dsimp [f]; split_ifs with h)
        · exact a_unit.pow k.natAbs
        · absurd lt_zero; exact not_lt_of_ge h
        · exact (x_unit.mul $ a_unit.pow k.natAbs).mul x_unit
        · exact x_unit.mul (a_unit.pow k.natAbs)
        · exact x_unit.mul (a_unit.pow k.natAbs)
        · exact (a_unit.pow k.natAbs).mul x_unit
      have map_comm: ∀x: QuaternionGroup 0, f x = (factor_through_units x).unit.val := by
        sorry
      intro x y
      rw [map_comm x, map_comm y, map_comm (x * y)]
      rw [<-Units.val_mul]
      apply Units.eq_iff.mpr
      exact @IsUnit.unit_mul G _ (f x) (f y) (factor_through_units x) (factor_through_units y)
      /-
      let ⟨a', ha⟩ := factor_through_units (.a 1)
      let ⟨x', hx⟩ := factor_through_units (.xa 0)
      let f' := lift_nzero_to_group a' x' ?_ ?_
      · sorry
      ·
        rw [x'.val_zpow_eq_zpow_val 2]
        sorry
      · sorry
      -/
  }



/-

abbrev Int.pos_disc (x: ℤ): ℕ := x.sign.toNat
abbrev Int.neg_disc (x: ℤ): ℕ := x.neg.sign.toNat

@[simp]
theorem pos_disc_zero: Int.pos_disc 0 = 0 := by bound
@[simp]
theorem neg_disc_zero: Int.neg_disc 0 = 0 := by bound
@[simp]
theorem pos_disc_zero_neg: (Int.neg 0).pos_disc = 0 := by bound
@[simp]
lemma neg_disc_zero_neg: (Int.neg 0).neg_disc = 0 := by bound
@[simp]
lemma neg_disc_neg_one {l: ℤ} (h: l < 0): l.neg_disc = 1 := by
  unfold Int.neg_disc
  rw [(?_: l.neg.sign = 1)]
  · trivial
  · exact Int.sign_eq_one_iff_pos.mpr (Int.neg_pos.mpr h)
@[simp]
lemma neg_disc_pos_zero {l: ℤ} (h: l > 0): l.neg_disc = 0 := by
  unfold Int.neg_disc
  rw [(?_: l.neg.sign = -1)]
  · trivial
  · exact Int.sign_eq_neg_one_iff_neg.mpr (Int.neg_neg_iff_pos.mpr h)

def lift_n_zero (a x: G) (h₂: x^2 = 1) (h₃: a * x * a = x):
    QuaternionGroup 0 →* G where
  toFun := fun g => match g with
    | .a (k: ℤ) => x^k.neg_disc * a^k.natAbs * x^k.neg_disc
    | .xa (k: ℤ) => x^k.pos_disc * a^k.natAbs * x^k.neg_disc
  map_one' := by
    rw [(by rfl: (1: QuaternionGroup 0) = .a 0)]
    simp!
  map_mul' := by
    intro g₁ g₂
    obtain (l: ℤ) | (l: ℤ) := g₁
    <;> obtain (m: ℤ) | (m: ℤ) := g₂
    <;> simp
    ·
      obtain sl | sl | sl := (by omega: l < 0 ∨ l = 0 ∨ l > 0)
      <;> try simp [sl]
      <;> obtain sm | sm | sm := (by omega: m < 0 ∨ m = 0 ∨ m > 0)
      <;> try simp [sl, sm]
      (case' a.a.inl.inl =>
        conv_rhs => calc x * a^l.natAbs * x * (x * a^m.natAbs * x)
          _ = x * a^l.natAbs * x^2 * a^m.natAbs * x := by noncomm_ring
          _ = x * a^l.natAbs * a^m.natAbs * x := by simp [h₂]
          _ = x * (a^l.natAbs * a^m.natAbs) * x := by noncomm_ring
          _ = x * a^(l.natAbs + m.natAbs) * x := by rw [<-pow_add]
          _ = x * a^(l + m).natAbs * x := by rw [<-Int.natAbs_add_of_nonpos (le_of_lt sl) (le_of_lt sm)]
      );

      (case a.a.inr.inr.inr.inr => 
        have := Int.add_pos_of_pos_of_nonneg sl (le_of_lt sm)
        simp [neg_disc_pos_zero this, <-pow_add]
        rw [<-Int.natAbs_add_of_nonneg (le_of_lt sl) (le_of_lt sm)]
      );

      all_goals obtain ssum | ssum | ssum := (by omega: (l + m) < 0 ∨ (l + m) = 0 ∨ (l + m) > 0)
      <;> try simp [sl, sm, ssum]
      · rw [(by noncomm_ring: x * x = x^2), h₂]
      · omega
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
    ·
      sorry
    ·
      sorry
    · sorry
-/
