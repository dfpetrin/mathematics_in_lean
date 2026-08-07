import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_iff_left₀ _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have ngeNs : n ≥ Ns := le_of_max_le_left nge
  have ngeNt : n ≥ Nt := le_of_max_le_right nge
  calc  |s n + t n - (a + b)|
    _ = |(s n - a) + (t n - b)| := by congr; abel
    _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs n ngeNs) (ht n ngeNt)
    _ = ε := by norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      group
    rw [h]
    group
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := div_pos εpos acpos
  rcases cs _ εcpos with ⟨Ns, hs⟩
  use Ns
  intro n nge
  calc  |c * s n - c * a|
    _ = |c| * |s n - a| := by rw [← mul_sub, abs_mul]
    _ < |c| * (ε / |c|) := mul_lt_mul_of_pos_left (hs n nge) acpos
    _ = ε := by field_simp

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nge
  calc  |s n|
    _ = |s n - a + a| := by congr; abel
    _ ≤ |s n - a| + |a| := abs_add_le _ _
    _ < |a| + 1 := by linarith [h n nge]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨Ns, B, hs⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (hs Ns (le_refl _))
  have εBpos : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ εBpos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have ngeNs : n ≥ Ns := le_of_max_le_left nge
  have ngeNt : n ≥ Nt := le_of_max_le_right nge
  calc  |s n * t n - 0|
    _ = |s n| * |t n - 0| := by rw [sub_zero, sub_zero, abs_mul]
    _ < B * (ε / B) := mul_lt_mul'' (hs n ngeNs) (ht n ngeNt) (abs_nonneg _) (abs_nonneg _)
    _ = ε := by field_simp

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    abel
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have hpos : |a - b| > 0 := abs_sub_pos.mpr abne
  have sba : ConvergesTo (fun n ↦ s n - s n) (b - a) := by
    convert convergesTo_add sb (convergesTo_mul_const (-1) sa) using 1
    · ext; ring
    ring
  rcases sba _ hpos with ⟨N, h⟩
  have : |a - b| < |a - b|
  calc
    _ = |s N - s N - (b - a)| := by congr 1; abel
    _ < |a - b| := h N (le_refl _)
  linarith

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_const' [Inhabited α] (a : ℝ) : ConvergesTo' (fun _ : α ↦ a) a := by
  intro ε εpos
  use default
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add' {s t : α → ℝ} {a b : ℝ}
      (cs : ConvergesTo' s a) (ct : ConvergesTo' t b) :
    ConvergesTo' (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have ngeNs : n ≥ Ns := le_of_max_le_left nge
  have ngeNt : n ≥ Nt := le_of_max_le_right nge
  calc  |s n + t n - (a + b)|
    _ = |(s n - a) + (t n - b)| := by congr; abel
    _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs n ngeNs) (ht n ngeNt)
    _ = ε := by norm_num

theorem convergesTo_mul_const' [Inhabited α] {s : α → ℝ} {a : ℝ}
    (c : ℝ) (cs : ConvergesTo' s a) : ConvergesTo' (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const' 0
    · rw [h]
      group
    rw [h]
    group
    assumption
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := div_pos εpos acpos
  rcases cs _ εcpos with ⟨Ns, hs⟩
  use Ns
  intro n nge
  calc  |c * s n - c * a|
    _ = |c| * |s n - a| := by rw [← mul_sub, abs_mul]
    _ < |c| * (ε / |c|) := mul_lt_mul_of_pos_left (hs n nge) acpos
    _ = ε := by field_simp

theorem exists_abs_le_of_convergesTo' {s : α → ℝ} {a : ℝ} (cs : ConvergesTo' s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nge
  calc  |s n|
    _ = |s n - a + a| := by congr; abel
    _ ≤ |s n - a| + |a| := abs_add_le _ _
    _ < |a| + 1 := by linarith [h n nge]

theorem aux' {s t : α → ℝ} {a : ℝ} (cs : ConvergesTo' s a) (ct : ConvergesTo' t 0) :
    ConvergesTo' (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo' cs with ⟨Ns, B, hs⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (hs Ns (le_refl _))
  have εBpos : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ εBpos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have ngeNs : n ≥ Ns := le_of_max_le_left nge
  have ngeNt : n ≥ Nt := le_of_max_le_right nge
  calc  |s n * t n - 0|
    _ = |s n| * |t n - 0| := by rw [sub_zero, sub_zero, abs_mul]
    _ < B * (ε / B) := mul_lt_mul'' (hs n ngeNs) (ht n ngeNt) (abs_nonneg _) (abs_nonneg _)
    _ = ε := by field_simp

theorem convergesTo_mul' [Inhabited α] {s t : α → ℝ} {a b : ℝ}
      (cs : ConvergesTo' s a) (ct : ConvergesTo' t b) :
    ConvergesTo' (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo' (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux' cs
    convert convergesTo_add' ct (convergesTo_const' (-b))
    group
  have := convergesTo_add' h₁ (convergesTo_mul_const' b cs)
  convert convergesTo_add' h₁ (convergesTo_mul_const' b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique' [Inhabited α] {s : α → ℝ} {a b : ℝ}
      (sa : ConvergesTo' s a) (sb : ConvergesTo' s b) :
    a = b := by
  by_contra abne
  have hpos : |a - b| > 0 := abs_sub_pos.mpr abne
  have sba : ConvergesTo' (fun n ↦ s n - s n) (b - a) := by
    convert convergesTo_add' sb (convergesTo_mul_const' (-1) sa) using 1
    · ext; ring
    ring
  rcases sba _ hpos with ⟨N, h⟩
  have : |a - b| < |a - b|
  calc
    _ = |s N - s N - (b - a)| := by congr 1; abel
    _ < |a - b| := h N (le_refl _)
  linarith

end
