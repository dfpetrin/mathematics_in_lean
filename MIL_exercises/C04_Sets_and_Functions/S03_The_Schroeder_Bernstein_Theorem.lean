import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import MIL.Common

open Set
open Function

noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]

section
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n

def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
    exact ⟨mem_univ _, hx⟩
  have : ∃ y, g y = x := by
    simp at this
    assumption
  exact invFun_eq this

theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂ (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      exact this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      have x₂eq : x₂ = g (f x₁) := by
        rw [hxeq, sb_right_inv _ _ x₂nA]
      rw [A_def, sbSet, mem_iUnion] at x₁A
      rcases x₁A with ⟨n, x₁Sₙ⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, x₁Sₙ, x₂eq.symm⟩
    rw [if_pos x₁A, if_pos x₂A] at hxeq
    exact hf hxeq
  push Not at xA
  rw [if_neg xA.left, if_neg xA.right] at hxeq
  rw [← sb_right_inv _ _ xA.left, hxeq, sb_right_inv _ _ xA.right]

theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, gySₙ⟩
    rcases n with _ | m
    · simp [sbAux] at gySₙ
    simp [sbAux] at gySₙ
    rcases gySₙ with ⟨x, xSₘ, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨m, xSₘ⟩
    rw [h_def, sbFun, if_pos this]
    apply hg hx

  use g y
  rw [h_def, sbFun, if_neg gyA]
  apply leftInverse_invFun hg

end

theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩

-- Auxiliary information
section
variable (g : β → α) (x : α)

#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

end
