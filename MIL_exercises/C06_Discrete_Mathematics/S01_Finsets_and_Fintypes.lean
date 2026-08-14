import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.BigOperators

section
variable {α : Type*} [DecidableEq α] (a : α) (s t : Finset α)

#check a ∈ s
#check s ∩ t

end

open Finset

variable (a b c : Finset ℕ)
variable (n : ℕ)

#check a ∩ b
#check a ∪ b
#check a \ b
#check (∅ : Finset ℕ)

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by
  ext x; simp only [mem_inter, mem_union]; tauto

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by rw [inter_union_distrib_left]

example : a ∩ (b ∪ c) = a ∩ b ∪ a ∩ c := inter_union_distrib_left ..

section
variable {α β : Type*} [DecidableEq α] (s t u : Finset α)

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x
  rw [mem_inter, mem_inter]
  rintro ⟨xs, xu⟩
  exact ⟨h xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_iff, mem_inter]
  rintro x ⟨xs, xu⟩
  exact ⟨h xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  simp only [mem_inter] at *
  exact ⟨h xsu.1, xsu.2⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  simp only [mem_inter] at hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  simp only [mem_union] at *
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    simp only [mem_inter]
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    simp only [mem_inter]
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  simp only [subset_iff, mem_inter, mem_union]
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x
  simp only [mem_inter, mem_union]
  rintro (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · exact ⟨xs, Or.inl xt⟩
  · exact ⟨xs, Or.inr xu⟩

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  simp only [mem_sdiff] at *
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  simp only [mem_union]
  intro xtu
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  simp only [subset_iff, mem_sdiff, mem_union]
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  simp only [subset_iff, mem_sdiff, mem_union]
  rintro x ⟨xs, xntu⟩
  refine ⟨⟨xs, ?xnt⟩, ?xnu⟩
  · intro xt; exact xntu <| Or.inl xt
  · intro xu; exact xntu <| Or.inr xu

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm <;> simp only [subset_iff, mem_inter]
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Subset.antisymm
    (fun _x xst ↦ mem_inter.mpr ⟨(mem_inter.mp xst).2, (mem_inter.mp xst).1⟩)
    (fun _x xts ↦ mem_inter.mpr ⟨(mem_inter.mp xts).2, (mem_inter.mp xts).1⟩)

example : s ∩ (s ∪ t) = s := by
  ext x
  simp only [mem_inter, mem_union]
  tauto

example : s ∩ (s ∪ t) = s := by simp

example : s ∪ s ∩ t = s := by
  ext x
  simp only [mem_inter, mem_union]
  tauto

example : s ∪ s ∩ t = s := by simp

example : s \ t ∪ t = s ∪ t := by
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · rintro (⟨xs, _⟩ | xt)
    · left; exact xs
    · right; exact xt
  · rintro (xs | xt)
    · by_cases xt : x ∈ t
      · right; exact xt
      · left; exact ⟨xs, xt⟩
    · right; exact xt

example : s \ t ∪ t = s ∪ t := by
  ext x
  simp only [mem_sdiff, mem_union]
  tauto

example : s \ t ∪ t = s ∪ t := by simp

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  simp only [mem_sdiff, mem_inter, mem_union]
  constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · use Or.inl xs
      rintro ⟨xs, xt⟩
      contradiction
    · use Or.inr xt
      rintro ⟨xs, xt⟩
      contradiction
  · rintro ⟨xs | xt, xnst⟩
    · left
      use xs
      intro xt
      exact xnst ⟨xs, xt⟩
    · right
      use xt
      intro xs
      exact xnst ⟨xs, xt⟩

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; simp; tauto

end

#check ({0, 2, 5} : Finset Nat)

def example1 : Finset ℕ := {0, 1, 2}

example : ({0, 1, 2} : Finset ℕ) = {1, 2, 0} := by decide

example : ({0, 1, 2} : Finset ℕ) = {0, 1, 1, 2} := by decide

example : ({0, 1} : Finset ℕ) = {1, 0} := by rw [Finset.pair_comm]

example (x : Nat) : ({x, x} : Finset ℕ) = {x} := by simp

example (x y z : Nat) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  ext i; simp [or_comm, or_left_comm]

example (x y z : Nat) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  ext i; simp; tauto

example (s : Finset ℕ) (a : ℕ) (h : a ∉ s) : (insert a s |>.erase a) = s :=
  Finset.erase_insert h

example (s : Finset ℕ) (a : ℕ) (h : a ∈ s) : insert a (s.erase a) = s :=
  Finset.insert_erase h

set_option pp.notation false in
#check ({0, 1, 2} : Finset ℕ)

example : {m ∈ range n | Even m} = (range n).filter Even := rfl
example : {m ∈ range n | Even m ∧ m ≠ 3} = (range n).filter (fun m ↦ Even m ∧ m ≠ 3) := rfl

example : {m ∈ range 10 | Even m} = {0, 2, 4, 6, 8} := by decide

#check (range 5).image (fun x ↦ x * 2)

example : (range 5).image (fun x ↦ x * 2) = {x ∈ range 10 | Even x} := by decide

section
variable (s t : Finset Nat)
#check s ×ˢ t
#check s.powerset

end

namespace finsets_and_fintypes
#check Finset.fold

def f (n : ℕ) : Int := (↑n)^2

#check (range 5).fold (fun x y : Int ↦ x + y) 0 f
#eval (range 5).fold (fun x y : Int ↦ x + y) 0 f

#check ∑ i ∈ range 5, i^2
#check ∏ i ∈ range 5, i + 1

variable (g : Nat → Finset Int)

#check (range 5).biUnion g

end finsets_and_fintypes

#check Finset.induction

example {α : Type*} [DecidableEq α] (f : α → ℕ)  (s : Finset α) (h : ∀ x ∈ s, f x ≠ 0) :
    ∏ x ∈ s, f x ≠ 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s anins ih =>
    rw [prod_insert anins]
    apply mul_ne_zero
    · apply h; apply mem_insert_self
    apply ih
    intros x xs
    exact h x (mem_insert_of_mem xs)

noncomputable example (s : Finset ℕ) (h : s.Nonempty) : ℕ := Classical.choose h

example (s : Finset ℕ) (h : s.Nonempty) : Classical.choose h ∈ s := Classical.choose_spec h

noncomputable example (s : Finset ℕ) : List ℕ := s.toList

example (s : Finset ℕ) (a : ℕ) : a ∈ s.toList ↔ a ∈ s := mem_toList

#check Finset.min
#check Finset.min'
#check Finset.max
#check Finset.max'
#check Finset.inf
#check Finset.inf'
#check Finset.sup
#check Finset.sup'

example : Finset.Nonempty {2, 6, 7} := ⟨6, by trivial⟩
example : Finset.min' {2, 6, 7} ⟨6, by trivial⟩ = 2 := by trivial

#check Finset.card

#eval (range 5).card

example (s : Finset ℕ) : s.card = #s := by rfl

example (s : Finset ℕ) : s.card = ∑ _i ∈ s, 1 := by rw [card_eq_sum_ones]

example (s : Finset ℕ) : s.card = ∑ _i ∈ s, 1 := by simp

section
variable {α : Type*} [Fintype α]

example : ∀ x : α, x ∈ Finset.univ := by
  intro x; exact mem_univ x

example : Fintype.card α = (Finset.univ : Finset α).card := rfl
end

example : Fintype.card (Fin 5) = 5 := by simp
example : Fintype.card ((Fin 5) × (Fin 3)) = 15 := by simp

section
variable (s : Finset ℕ)

example : (↑s : Type) = {x : ℕ // x ∈ s} := rfl
example : Fintype.card ↑s = s.card := by simp
end

