import Mathlib
--import Mathlib.GroupTheory.SpecificGroups.Dihedral
-- set_option diagnostics true

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


-- how to work with points in (Fin 2 → ℝ)
def v : Fin 2 → ℝ := ![1, 0]

def u : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

def w : Fin 2 → ℝ := fun
  | 0 => 1
  | 1 => 0


-- how to work with maps (Fin 2 → ℝ) → (Fin 2 → ℝ)
def f : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
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
  let e : LinearMap.GeneralLinearGroup ℝ (Fin 2 → ℝ) →*  ((Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) :=
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

theorem rotationMatrix_pow_n [NeZero n] (i : ℤ) :
    rotationMatrix (2 * π * i / n) ^ n = 1 := by
  rw [rotationMatrix_pow]
  have h₁ : cos (2 * π * i) = 1 := sorry
  have h₂ : sin (2 * π * i) = 0 := sorry
  ext i j; fin_cases i <;> fin_cases j <;> simpa

abbrev reflectionMatrix /- (θ : ℝ) -/ : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,  0;
     0, -1]

theorem reflectionMatrix_mul_self : reflectionMatrix * reflectionMatrix = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem reflectionMatrix_conj_rotationMatrix (θ : ℝ) :
    reflectionMatrix * rotationMatrix θ * reflectionMatrix⁻¹ = (rotationMatrix (-θ)) := by
  rw [(show reflectionMatrix⁻¹ = reflectionMatrix from
         sorry /- DivisionMonoid.inv_eq_of_mul reflectionMatrix_mul_self -/)]
  ext i j; fin_cases i <;> fin_cases j <;> simp

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

lemma reflectionMatrix_unit_mul_self : reflectionMatrix_unit * reflectionMatrix_unit = 1 := by
  dsimp [reflectionMatrix_unit]
  rw [Units.ext_iff]
  exact reflectionMatrix_mul_self

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

lemma rotationMatrix_unit_pow (θ : ℝ) (l : ℕ) : (rotationMatrix_unit θ) ^ l = rotationMatrix_unit (θ * l) := by
  dsimp [rotationMatrix_unit]
  rw [Units.ext_iff]
  exact rotationMatrix_pow θ l

theorem rotationMatrix_unit_pow_n [NeZero n] (i : ℤ) :  rotationMatrix_unit (2 * π * i / n) ^ n = 1 := by
  dsimp [rotationMatrix_unit]
  rw [Units.ext_iff]
  exact rotationMatrix_pow_n i

noncomputable def representation : Representation ℝ (DihedralGroup n) (Fin 2 → ℝ) := by
  dsimp [Representation]
  let G := GL (Fin 2) ℝ
  let r : G := rotationMatrix_unit (2 * π / n)
  let s : G := reflectionMatrix_unit
  let h_a : r ^ n = 1 := by
    cases Nat.eq_zero_or_pos n with
      | inl h_zero  => exact
        pow_eq_one_iff_modEq.mpr (congrFun (congrArg HMod.hMod h_zero) (orderOf r))

      | inr h_pos =>
        have h_nezero: NeZero n := by
          exact NeZero.of_pos h_pos

        unfold r
        --have hmodify : rotationMatrix_unit (2 * π / n) ^ n = rotationMatrix_unit (2 * π * 1 / n) ^ n := by
        --  simp only [mul_one]
        --rw [hmodify]
        have hl2: rotationMatrix_unit (2 * π * (1 : ℤ)/ ↑n) ^ n = rotationMatrix_unit (2 * π / ↑n) ^ n := by
          have h: 2 * π * (1: ℤ) / n = 2 * π / n := by
            simp only [Int.cast_one, mul_one]
          rw [h]
        rw [← hl2]
        rw [rotationMatrix_unit_pow_n (1 : ℤ)]

  let h_b : s * s = 1 := by
    simp [s]
    exact reflectionMatrix_unit_mul_self
  let h_ab : s * r * s⁻¹ = r⁻¹ := sorry
  let φ := lift h_a h_b h_ab
  exact ((DistribMulAction.toModuleEnd ℝ (Fin 2 → ℝ)).comp Matrix.GeneralLinearGroup.toLin.toMonoidHom).comp φ
end DihedralGroup
