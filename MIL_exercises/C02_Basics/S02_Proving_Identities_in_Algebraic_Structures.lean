import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

-- An example.
example (a b c : R) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
example (a b c : R) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : R) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- An example.
example (a b c : R) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : R) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : R) : a * (b * c) = b * (a * c) := by
  rw [mul_comm]
  rw [mul_assoc]
  rw [mul_comm c]

-- Using facts from the local context.
example (a b c d e f : R) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : R) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]

example (a b c d : R) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

example (a b c d e f : R) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

variable (a b c d e f : R)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b : R)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc (a + b) * (a + b)
    _ = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : R)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [add_mul, mul_add, mul_add]
  rw [← add_assoc]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc (a + b) * (c + d)
    _ = a * c + a * d + (b * c + b * d) := by
      rw [add_mul, mul_add, mul_add]
    _ = a * c + a * d + b * c + b * d := by
      rw [← add_assoc]

example (a b : R) : (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
  calc (a + b) * (a - b)
    _ = a * a + b * a - (a * b + b * b) := by
      rw [mul_sub, add_mul, add_mul]
    _ = a * a + (b * a - a * b) - b * b := by
      rw [← sub_sub, add_sub]
    _ = a * a - b * b := by
      rw [mul_comm b, sub_self, add_zero]
    _ = a ^ 2 - b ^ 2 := by
      rw [← pow_two, ← pow_two]

end

-- Examples.

section
variable (a b c d : R)

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_neg_cancel, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 + 0 * a := by
    rw [← add_mul, zero_add, zero_add]
  rw [add_right_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b :=
  calc  -a
    _ = -a + (a + b) := by
      rw [h, add_zero]
    _ = b := by
      rw [neg_add_cancel_left]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b :=
  calc  a
    _ = a + b + -b := by
      rw [add_neg_cancel_right]
    _ = -b := by
      rw [h, zero_add]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [neg_add_cancel]

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem sub_self (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem sub_self_real (a : ℝ) : a - a = 0 := by
  apply add_neg_cancel

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 :=
  calc  a * a⁻¹
    _ = a⁻¹⁻¹ * a⁻¹ * a * a⁻¹ := by
      rw [mul_assoc, inv_mul_cancel, one_mul]
    _ = a⁻¹⁻¹ * a⁻¹ := by
      rw [mul_assoc a⁻¹⁻¹, inv_mul_cancel, mul_assoc, one_mul]
    _ = 1 := by
      rw [inv_mul_cancel]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]

theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

theorem mul_left_cancel {a b c : G} (h : a * b = a * c) : b = c := by
  rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left]

theorem mul_right_cancel {a b c : G} (h : a * b = c * b) : a = c := by
  rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right]

theorem inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b :=
  calc  a⁻¹
    _ = a⁻¹ * (a * b) := by
      rw [h, mul_one]
    _ = b := by
      rw [inv_mul_cancel_left]

theorem eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ :=
  calc  a
    _ = a * b * b⁻¹ := by
      rw [mul_inv_cancel_right]
    _ = b⁻¹ := by
      rw [h, one_mul]

theorem inv_one : (1⁻¹ : G) = 1 := by
  apply inv_eq_of_mul_eq_one
  rw [mul_one]

theorem inv_inv (a : G) : a⁻¹⁻¹ = a := by
  apply inv_eq_of_mul_eq_one
  rw [inv_mul_cancel]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply inv_eq_of_mul_eq_one
  calc  a * b * (b⁻¹ * a⁻¹)
    _ = a * (b * b⁻¹) * a⁻¹ := by
      rw [← mul_assoc, mul_assoc a b]
    _ = a * a⁻¹ := by
      rw [mul_inv_cancel, mul_one]
    _ = 1 := by
      rw [mul_inv_cancel]

end MyGroup

end
