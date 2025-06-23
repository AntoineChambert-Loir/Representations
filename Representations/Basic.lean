
import Mathlib

#print Representation

#check DihedralGroup

-- Let's get the trivial representation
example (n : ℕ) : Representation ℂ (DihedralGroup n) ℂ :=
  Representation.trivial _ _ _

-- Let's get the trivial representation over the integers
example (n : ℕ) : Representation ℤ (DihedralGroup n) ℤ :=
  Representation.trivial _ _ _

-- Let's get the left regular representation
noncomputable
example (n : ℕ) : Representation ℤ (DihedralGroup n) (DihedralGroup n →₀ ℤ) :=
  Representation.leftRegular _ _

#check Equiv.Perm

#check Matrix.GeneralLinearGroup
#check Matrix.SpecialLinearGroup

#check PresentedGroup

#check QuaternionGroup

#check RegularWreathProduct

#check SemidirectProduct
#check Matrix.symplecticGroup
#check pinGroup
#check spinGroup


