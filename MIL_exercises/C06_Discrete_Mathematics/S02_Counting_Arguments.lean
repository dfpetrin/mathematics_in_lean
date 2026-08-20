import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (s t : Finset α) (f : α → β)

example : #(s ×ˢ t) = #s * #t := by rw [card_product]
example : #(s ×ˢ t) = #s * #t := by simp

example : #(s ∪ t) = #s + #t - #(s ∩ t) := by rw [card_union]

example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by rw [card_union_of_disjoint h]
example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by simp [h]

example (h : Function.Injective f) : #(s.image f) = #s := by rw [card_image_of_injective _ h]

example (h : Set.InjOn f s) : #(s.image f) = #s := by rw [card_image_of_injOn h]

section
open Fintype

variable {α β : Type*} [Fintype α] [Fintype β]

example : card (α × β) = card α * card β := by simp

example : card (α ⊕ β) = card α + card β := by simp

example (n : ℕ) : card (Fin n → α) = (card α)^n := by simp

variable {n : ℕ} {γ : Fin n → Type*} [∀ i, Fintype (γ i)]

example : card ((i : Fin n) → γ i) = ∏ i, card (γ i) := by simp

example : card (Σ i, γ i) = ∑ i, card (γ i) := by simp

end

#check Disjoint

example (m n : ℕ) (h : m ≥ n) :
    #(range n ∪ (range n).image fun i ↦ m + i) = 2 * n := by
  rw [card_union_of_disjoint, card_image_of_injective, card_range]; omega
  · apply add_right_injective
  · simp [disjoint_iff_ne]; omega

def triangle (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range (n+1) ×ˢ range (n+1) | p.1 < p.2}

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n = (range (n+1)).biUnion fun j ↦ (range j).image (·, j) := by
    ext p
    simp only [triangle, mem_filter, mem_product, mem_range, mem_biUnion, mem_image]
    constructor
    · rintro ⟨⟨-, hp2⟩, _⟩
      use p.2, hp2, p.1
    · rintro ⟨p2, hp2, p1, hp12, rfl⟩
      omega
  rw [this, card_biUnion]; swap
  · -- take care of disjointness first
    intro x _ y _ xney
    simp [disjoint_iff_ne, xney]
  -- continue the calculation
  trans ∑ i ∈ range (n + 1), i
  · congr; ext i
    rw [card_image_of_injective, card_range]
    intro i1 i2; simp
  rw [sum_range_id]; rfl

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n ≃ Σ i : Fin (n + 1), Fin i :=
    { toFun := by
        rintro ⟨⟨i, j⟩, hp⟩
        have : (i ≤ n ∧ j ≤ n) ∧ i < j := by simpa [triangle] using hp
        exact ⟨⟨j, by omega⟩, ⟨i, this.2⟩⟩
      invFun := by
        rintro ⟨j, i⟩
        use ⟨i, j⟩
        suffices i ≤ n ∧ j ≤ n by simpa [triangle]
        omega }
  rw [←Fintype.card_coe]
  trans; apply Fintype.card_congr this
  rw [Fintype.card_sigma, sum_fin_eq_sum_range]
  convert Finset.sum_range_id (n + 1)
  simp_all

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  apply Nat.eq_div_of_mul_eq_right (by norm_num)
  let turn (p : ℕ × ℕ) : ℕ × ℕ := (n - 1 - p.1, n - p.2)
  calc  2 * #(triangle n)
      = #(triangle n) + #(triangle n) := by ring
    _ = #(triangle n) + #(triangle n |>.image turn) := by
          rw [card_image_of_injOn]
          simp [Set.InjOn, triangle, turn]
          omega
    _ = #(range n ×ˢ range (n + 1)) := by
          rw [← card_union_of_disjoint]; swap
          · simp [disjoint_iff_ne, triangle, turn]; omega
          congr; ext ⟨p1, p2⟩
          simp [triangle, turn]
          constructor
          · rintro (_ | _) <;> omega
          · by_cases hp12 : p1 < p2
            · omega
            intro
            right
            use n - 1 - p1, n - p2
            omega
    _ = (n + 1) * n := by simp [mul_comm]

def triangle' (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range n ×ˢ range n | p.1 ≤ p.2}

example (n : ℕ) : #(triangle' n) = #(triangle n) := by
  let raise (p : ℕ × ℕ) : ℕ × ℕ := (p.1, p.2 + 1)
  have : (triangle' n |>.image raise) = triangle n := by
    ext ⟨p1, p2⟩
    simp [triangle, triangle', raise]
    constructor
    · omega
    intro
    use p2 -1
    omega
  rw [← this, card_image_of_injective]
  intro (p1, p2) (q1, q2); simp [raise]

section
open scoped Classical

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ #{b ∈ t | r a b})
    (h_right : ∀ b ∈ t, #{a ∈ s | r a b} ≤ 1) :
    3 * #s ≤ #t := by
  calc  3 * #s
      = ∑ a ∈ s, 3                               := by simp [mul_comm]
    _ ≤ ∑ a ∈ s, #{b ∈ t | r a b}                := sum_le_sum h_left
    _ = ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by simp
    _ = ∑ b ∈ t, ∑ a ∈ s, if r a b then 1 else 0 := sum_comm
    _ = ∑ b ∈ t, #{a ∈ s | r a b}                := by simp
    _ ≤ ∑ b ∈ t, 1                               := sum_le_sum h_right
    _ = #t                                       := by simp

example (m k : ℕ) (h : m ≠ k) (h' : m / 2 = k / 2) : m = k + 1 ∨ k = m + 1 := by omega

example {n : ℕ} (A : Finset ℕ)
    (hA : #A = n + 1)
    (hA' : A ⊆ range (2 * n)) :
    ∃ m ∈ A, ∃ k ∈ A, Nat.Coprime m k := by
  have : ∃ t ∈ range n, 1 < #{u ∈ A | u / 2 = t} := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · intro u uA
      specialize hA' uA
      simp at *
      exact Nat.div_lt_of_lt_mul hA'
    · simp [hA]
  rcases this with ⟨t, ht, ht'⟩
  simp only [one_lt_card, mem_filter] at ht'
  rcases ht' with ⟨m, ⟨mA, hm⟩, k, ⟨kA, hk⟩, mnek⟩
  use m, mA, k, kA
  obtain rfl | rfl : m = k + 1 ∨ k = m + 1 := by omega
  all_goals simp

end
