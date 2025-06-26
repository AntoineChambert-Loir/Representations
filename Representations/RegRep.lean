import Mathlib

-- Work by Hikari Iwasaki, Wednesday-Thursday June 25-26, 2025
-- Regular representaiton over ℝ. There should be no problem extending this to an arbitrary field k.

noncomputable section

abbrev V_reg (G : Type) := G → ℝ -- vector space of dimension |G|

abbrev std_basis (G : Type) [Fintype G] [DecidableEq G] : Basis G ℝ (V_reg G) := Pi.basisFun ℝ G
-- use: passing (Pi.basisFun ℝ G) g returns a vector, of the form G → ℝ

-- define a linear map such that v_h gets sent to v_gh
def map_basis_elements (G : Type)[Group G] [Fintype G] [DecidableEq G] (g : G): (V_reg G) →ₗ[ℝ] (V_reg G) :=
  Basis.constr (std_basis G) ℝ (fun h ↦ std_basis G (g * h))

-- definition of the regular representation map
def regmap (G : Type)[Group G] [Fintype G] [DecidableEq G]: G → ((V_reg G) →ₗ[ℝ] (V_reg G)) := fun g ↦ map_basis_elements G g

-- check the defining properties
def regmap_one' (G : Type)[Group G] [Fintype G] [DecidableEq G]: regmap G 1 = 1 := by
  unfold regmap  map_basis_elements
  ext g g'
  simp
  by_cases h: g = g'
  · subst h
    rw [Pi.single_eq_same]
    let f := fun (x:G) ↦ (Pi.single g (1 : ℝ) : G → ℝ) x * (Pi.single x (1 : ℝ) : G → ℝ) g
    have : f g = 1 := by
      unfold f
      rw [Pi.single_eq_same]
      norm_num
    change ∑ x, f x  = 1
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ g), this]
    nth_rw 2 [← add_zero 1]
    rw [add_left_cancel_iff]
    have : ∀ x ∈  Finset.univ.erase g, f x = (0:ℝ) := by
      intro x hx
      have hxg : x ≠ g := (Finset.mem_erase.mp hx).1
      simp only [f]
      rw [Pi.single_eq_of_ne hxg]
      norm_num

    exact Finset.sum_eq_zero this

  -- now case g ≠ g'
  push_neg at h
  rw [Pi.single_eq_of_ne h.symm]
  let f := fun (x:G) ↦ (Pi.single g (1 : ℝ) : G → ℝ) x * (Pi.single x (1 : ℝ) : G → ℝ) g'
  have : f g = 0 := by
    unfold f
    rw [Pi.single_eq_same, Pi.single_eq_of_ne h.symm]
    norm_num
  change ∑ x, f x  = 0
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ g), this]
  nth_rw 2 [← add_zero 0]
  rw [add_left_cancel_iff]
  have : ∀ x ∈  Finset.univ.erase g, f x = (0:ℝ) := by
    intro x hx
    simp only [f]
    have hxg : x ≠ g := (Finset.mem_erase.mp hx).1
    rw [Pi.single_eq_of_ne hxg]
    norm_num
  exact Finset.sum_eq_zero this


def regmap_mul'  (G : Type)[Group G] [Fintype G] [DecidableEq G]: ∀ (x y : G), regmap G (x * y) = regmap G x * regmap G y := by
  intro x y
  unfold regmap map_basis_elements
  ext g g'
  simp
  apply Finset.sum_congr rfl
  intro x₁
  simp only [Finset.mem_univ, mul_eq_mul_left_iff, forall_const]
  by_cases hgx₁ : g = x₁
  · left
    subst hgx₁
    let f := fun (x₂:G) ↦  (Pi.single (y * g) (1 : ℝ) : G → ℝ) x₂ * (Pi.single (x * x₂) (1 : ℝ) : G → ℝ) g'
    by_cases hxygg' : x * y * g = g'
    · subst g'
      rw  [Pi.single_eq_same]
      have : f (y * g) = 1 := by
        unfold f
        rw [mul_assoc, Pi.single_eq_same, Pi.single_eq_same]
        norm_num
      change 1 = ∑ x₂, f x₂
      rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ (y * g)), this]
      nth_rw 1 [← add_zero 1]
      rw [add_left_cancel_iff]
      have : ∀ x ∈  Finset.univ.erase (y * g), f x = (0:ℝ) := by
        intro x hx
        simp only [f]
        have hxg : x ≠ y * g := (Finset.mem_erase.mp hx).1
        rw [Pi.single_eq_of_ne hxg]
        norm_num
      exact (Finset.sum_eq_zero this).symm

    -- case x * y * g ≠ g'
    push_neg at hxygg'
    rw  [Pi.single_eq_of_ne (hxygg'.symm)]
    have : f (y * g) = 0 := by
      unfold f
      rw [← mul_assoc, Pi.single_eq_of_ne hxygg'.symm]
      norm_num
    change 0 = ∑ x₂, f x₂
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ (y * g)), this]
    nth_rw 1 [← add_zero 0]
    rw [add_left_cancel_iff]
    have : ∀ x ∈  Finset.univ.erase (y * g), f x = (0:ℝ) := by
      intro x hx
      simp only [f]
      have hxg : x ≠ y * g := (Finset.mem_erase.mp hx).1
      rw [Pi.single_eq_of_ne hxg]
      norm_num
    exact (Finset.sum_eq_zero this).symm

  -- finally case g ≠ x₁
  push_neg at hgx₁
  right; rw [Pi.single_eq_of_ne (hgx₁.symm)]

-- Put together, these define the regular representation of a finite group G.
def RegRep (G : Type)[Group G] [Fintype G] [DecidableEq G]: Representation  ℝ  G (V_reg G)  where
  toFun := regmap G
  map_one' := regmap_one' G
  map_mul' := regmap_mul' G
