import Mathlib.Tactic

namespace MyListSpace

inductive List (α : Type*) where
  | nil  : List α
  | cons : α → List α → List α

end MyListSpace

namespace MyListSpace2

def append {α : Type*} : List α → List α → List α
  | [],      bs => bs
  | a :: as, bs => a :: append as bs

def map {α β : Type*} (f : α → β) : List α → List β
  | []      => []
  | a :: as => f a :: map f as

#eval append [1, 2, 3] [4, 5, 6]
#eval map (·^2) [1, 2, 3, 4, 5]

theorem nil_append {α : Type*} (as : List α) : append [] as = as := rfl

theorem cons_append {α : Type*} (a : α) (as bs : List α) :
    append (a :: as) bs = a :: append as bs := rfl

theorem map_nil {α β : Type*} (f : α → β) : map f [] = [] := rfl

theorem map_cons {α β : Type*} (f : α → β) (a : α) (as : List α) :
    map f (a :: as) = f a :: map f as := rfl

end MyListSpace2

namespace MyListSpace3

variable {α β γ : Type*}
variable (as : List α)

open List

theorem append_nil : ∀ as : List α, as ++ [] = as
  | [] => rfl
  | a :: as => by rw [cons_append, append_nil]

theorem map_map (f : α → β) (g : β → γ) :
    ∀ as : List α, map g (map f as) = map (g ∘ f) as
  | [] => rfl
  | a :: as => by rw [map_cons, map_cons, map_cons, map_map]; rfl

theorem append_nil' : as ++ [] = as := by
  induction' as with a as' ih
  · rfl
  · rw [cons_append, ih]

theorem map_map' (f : α → β) (g : β → γ) (as : List α) :
    map g (map f as) = map (g ∘ f) as := by
  induction' as with a as' ih
  · rfl
  · simp [map, ih]

def reverse : List α → List α
  | []      => []
  | a :: as => reverse as ++ [a]

#eval reverse [1, 2, 3, 4, 5]

theorem reverse_append (as bs : List α) : reverse (as ++ bs) = reverse bs ++ reverse as := by
  induction' as with a as' ih
  · rw [nil_append, reverse, append_nil]
  · rw [cons_append, reverse, reverse, ih, append_assoc]

theorem reverse_reverse (as : List α) : reverse (reverse as) = as := by
  induction' as with a as' ih
  · rfl
  ·  simp only [reverse, reverse_append, nil_append, cons_append, ih]

end MyListSpace3

inductive BinTree where
  | empty : BinTree
  | node  : BinTree → BinTree → BinTree

namespace BinTree

def size : BinTree → ℕ
  | empty    => 0
  | node l r => size l + size r + 1

def depth : BinTree → ℕ
  | empty    => 0
  | node l r => max (depth l) (depth r) + 1

theorem size_le : ∀ t : BinTree, size t ≤ 2^depth t - 1
  | empty    => Nat.le_refl _
  | node l r => by
    dsimp [depth, size]
    calc  l.size + r.size + 1
        ≤ (2^l.depth - 1) + (2^r.depth - 1) + 1 := by
            gcongr <;> apply size_le
      _ ≤ (2 ^ max l.depth r.depth - 1) + (2 ^ max l.depth r.depth - 1) + 1 := by
            gcongr <;> simp
      _ = 2 ^ (max l.depth r.depth + 1) - 1 := by
          have : 0 < 2 ^ max l.depth r.depth := by simp
          omega

theorem depth_le_size : ∀ t : BinTree, depth t ≤ size t
  | empty    => Nat.le_refl _
  | node l r => by
    dsimp [depth, size]
    gcongr
    have := depth_le_size l
    have := depth_le_size r
    omega

def flip : BinTree → BinTree
  | empty    => empty
  | node l r => node (flip r) (flip l)

example : flip (node (node empty (node empty empty)) (node empty empty)) =
    node (node empty empty) (node (node empty empty) empty) := rfl

theorem size_flip : ∀ t, size (flip t) = size t
  | empty => rfl
  | node l r => by
    dsimp [flip, size]
    simp [size_flip, add_comm]

end BinTree

inductive PropForm
  | var (n : ℕ)
  | fls
  | conj (A B : PropForm)
  | disj (A B : PropForm)
  | impl (A B : PropForm)

namespace PropForm

def eval : PropForm → (ℕ → Bool) → Bool
  | var n,    v => v n
  | fls,      _ => false
  | conj A B, v => A.eval v && B.eval v
  | disj A B, v => A.eval v || B.eval v
  | impl A B, v => ! A.eval v || B.eval v

def vars : PropForm → Finset ℕ
  | var n    => {n}
  | fls      => ∅
  | conj A B => A.vars ∪ B.vars
  | disj A B => A.vars ∪ B.vars
  | impl A B => A.vars ∪ B.vars

theorem eval_eq_eval : ∀ (A : PropForm) (v1 v2 : ℕ → Bool),
    (∀ n ∈ A.vars, v1 n = v2 n) → A.eval v1 = A.eval v2
  | var n,    v1, v2, h => by simp_all [eval, vars]
  | fls,      v1, v2, h => rfl
  | conj A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]
  | disj A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]
  | impl A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]

theorem eval_eq_eval' (A : PropForm) (v1 v2 : ℕ → Bool) (h : ∀ n ∈ A.vars, v1 n = v2 n) :
    A.eval v1 = A.eval v2 := by
  cases A <;> simp_all [eval, vars, (eval_eq_eval' · v1 v2)]

def subst : PropForm → ℕ → PropForm → PropForm
  | var n,    m, C => if n = m then C else var n
  | fls,      _, _ => fls
  | conj A B, m, C => conj (A.subst m C) (B.subst m C)
  | disj A B, m, C => disj (A.subst m C) (B.subst m C)
  | impl A B, m, C => impl (A.subst m C) (B.subst m C)

theorem subst_eq_of_not_mem_vars :
    ∀ (A : PropForm) (m : ℕ) (C : PropForm), m ∉ A.vars → A.subst m C = A
  | var n,    m, C, h => by simp_all [subst, vars]; tauto
  | fls,      _, _, _ => rfl
  | conj A B, m, C, h => by simp_all [subst, vars, subst_eq_of_not_mem_vars]
  | disj A B, m, C, h => by simp_all [subst, vars, subst_eq_of_not_mem_vars]
  | impl A B, m, C, h => by simp_all [subst, vars, subst_eq_of_not_mem_vars]

theorem subst_eq_of_not_mem_vars' (A : PropForm) (m : ℕ) (C : PropForm) :
    m ∉ A.vars → A.subst m C = A := by
  cases A <;> simp_all [vars, subst, subst_eq_of_not_mem_vars']; tauto

theorem subst_eval_eq : ∀ (A : PropForm) (m : ℕ) (C : PropForm) (v : ℕ → Bool),
    (A.subst m C).eval v = A.eval (fun n => if n = m then C.eval v else v n)
  | var n,    m, C, v => by
      simp [subst, eval]
      split <;> rfl
  | fls,      _, _, _ => rfl
  | conj A B, m, C, v => by simp [subst, eval, subst_eval_eq]
  | disj A B, m, C, v => by simp [subst, eval, subst_eval_eq]
  | impl A B, m, C, v => by simp [subst, eval, subst_eval_eq]

theorem subst_eval_eq' (A : PropForm) (m : ℕ) (C : PropForm) (v : ℕ → Bool) :
    (A.subst m C).eval v = A.eval (fun n => if n = m then C.eval v else v n) := by
  cases A <;> simp [subst, eval, subst_eval_eq']
  split <;> rfl

end PropForm
