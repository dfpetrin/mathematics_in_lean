import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    apply h
    use x, xs
  intro h y ys
  rcases ys with ⟨x, xs, rfl⟩
  apply h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨x', x's, heq⟩
  rwa [← h heq]

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, fxu, rfl⟩
  exact fxu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, fxy⟩
  rw [← fxy] at yu
  use x, yu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, _⟩
  use x, h xs

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x; apply h

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x; rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor <;> use x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, x₁s, rfl⟩, ⟨x₂, x₂t, hx₂⟩⟩
  use x₁
  constructor
  · use x₁s
    rwa [← h hx₂]
  rfl

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, xs, rfl⟩, ht⟩
  use x
  constructor
  · constructor
    · exact xs
    intro xt
    apply ht
    use x, xt
  rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x; exact id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  rintro ⟨x, ⟨xs, fxv⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, fxv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, fxu⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · left; use x, xs
  right; exact fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp; constructor
  · rintro ⟨x, ⟨i, xAi⟩, rfl⟩
    use i, x
  · rintro ⟨i, x, xAi, rfl⟩
    use x, ⟨i, xAi⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y; simp
  intro x xAi fxy i
  use x, xAi i

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y; simp
  intro yInIntersection
  rcases yInIntersection i with ⟨xᵢ, xᵢinAᵢ, rfl⟩
  use xᵢ; constructor
  · intro i'
    rcases yInIntersection i' with ⟨xᵢ', xᵢ'inAᵢ', heq⟩
    rwa [← injf heq]
  rfl

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x; simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x; simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos e
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x₁ x₁nonneg x₂ x₂nonneg sqrtEqSqrt
  calc  x₁
    _ = √x₁ ^ 2 := by rw [sq_sqrt x₁nonneg]
    _ = √x₂ ^ 2 := by rw [sqrtEqSqrt]
    _ = x₂ := by rw [sq_sqrt x₂nonneg]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x₁ x₁nonneg x₂ x₂nonneg; dsimp
  intro sqEqSq
  calc  x₁
    _ = √(x₁ ^ 2) := by rw [sqrt_sq x₁nonneg]
    _ = √(x₂ ^ 2) := by rw [sqEqSq]
    _ = x₂ := by rw [sqrt_sq x₂nonneg]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, x_nonneg, rfl⟩
    apply sqrt_nonneg
  intro y_nonneg
  exact ⟨y ^ 2, sq_nonneg y, sqrt_sq y_nonneg⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩; dsimp
    apply sq_nonneg
  intro y_nonneg
  use √y
  simp [sq_sqrt y_nonneg]

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro injective_f x
    apply injective_f
    apply inverse_spec
    use x
  · intro left_inverse x₁ x₂ fx₁_eq_fx₂
    rw [← left_inverse x₁, ← left_inverse x₂, fx₁_eq_fx₂]

example : Injective f ↔ LeftInverse (inverse f) f := ⟨
  fun injective_f x => injective_f (inverse_spec _ ⟨x, rfl⟩),
  fun left_inverse x₁ x₂ fx₁_eq_fx₂ => left_inverse x₁ ▸ left_inverse x₂ ▸ fx₁_eq_fx₂ ▸ rfl,
⟩

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro surjective_f y
    apply inverse_spec
    apply surjective_f
  · intro right_inverse y
    use inverse f y
    apply right_inverse

example : Surjective f ↔ RightInverse (inverse f) f := ⟨
  fun surjective_f y => inverse_spec y (surjective_f _),
  fun right_inverse y => ⟨inverse f y, right_inverse _⟩,
⟩

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [← h]
  contradiction

-- COMMENTS: TODO: improve this
end
