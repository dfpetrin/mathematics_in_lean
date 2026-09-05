import MIL.Common

@[ext]
structure GaussInt where
  re : ℤ
  im : ℤ

namespace GaussInt

instance : Zero GaussInt :=
  ⟨0, 0⟩

instance : One GaussInt :=
  ⟨1, 0⟩

instance : Add GaussInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg GaussInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Mul GaussInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

theorem zero_def : (0 : GaussInt) = ⟨0, 0⟩ :=
  rfl

theorem one_def : (1 : GaussInt) = ⟨1, 0⟩ :=
  rfl

theorem add_def (x y : GaussInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
  rfl

theorem neg_def (x : GaussInt) : -x = ⟨-x.re, -x.im⟩ :=
  rfl

theorem mul_def (x y : GaussInt) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
  rfl

@[simp]
theorem zero_re : (0 : GaussInt).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem one_re : (1 : GaussInt).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem add_re (x y : GaussInt) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : GaussInt) : (x + y).im = x.im + y.im :=
  rfl

@[simp]
theorem neg_re (x : GaussInt) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : GaussInt) : (-x).im = -x.im :=
  rfl

@[simp]
theorem mul_re (x y : GaussInt) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : GaussInt) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl

instance : CommRing GaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg := (-·)
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intros
    ext <;> simp [add_assoc]
  zero_add := by
    intro
    ext <;> simp
  add_zero := by
    intro
    ext <;> simp
  neg_add_cancel := by
    intro
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp [add_comm]
  mul_assoc := by
    intros
    ext <;> simp <;> ring
  one_mul := by
    intro
    ext <;> simp
  mul_one := by
    intro
    ext <;> simp
  left_distrib := by
    intros
    ext <;> simp <;> ring
  right_distrib := by
    intros
    ext <;> simp <;> ring
  mul_comm := by
    intros
    ext <;> simp <;> ring
  zero_mul := by
    intro
    ext <;> simp
  mul_zero := by
    intro
    ext <;> simp

@[simp]
theorem sub_re (x y : GaussInt) : (x - y).re = x.re - y.re :=
  rfl

@[simp]
theorem sub_im (x y : GaussInt) : (x - y).im = x.im - y.im :=
  rfl

instance : Nontrivial GaussInt := by
  use 0, 1
  simp [GaussInt.ext_iff]

end GaussInt

example (a b : ℤ) : a = b * (a / b) + a % b :=
  Int.mul_ediv_add_emod a b |>.symm

example (a b : ℤ) : b ≠ 0 → 0 ≤ a % b :=
  Int.emod_nonneg a

example (a b : ℤ) : b ≠ 0 → a % b < |b| :=
  Int.emod_lt_abs a

namespace Int

def div' (a b : ℤ) :=
  (a + b / 2) / b

def mod' (a b : ℤ) :=
  (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * a.div' b + a.mod' b = a := by
  rw [div', mod']
  have := Int.mul_ediv_add_emod (a + b / 2) b
  omega

theorem abs_mod'_le (a b : ℤ) (h : 0 < b) : |a.mod' b| ≤ b / 2 := by
  rw [mod', abs_le]
  constructor
  · have := Int.emod_nonneg (a + b / 2) h.ne'
    omega
  · have := Int.emod_lt_of_pos (a + b / 2) h
    omega

theorem mod'_eq (a b : ℤ) : a.mod' b = a - b * a.div' b := by linarith [div'_add_mod' a b]

end Int

theorem sq_add_sq_eq_zero {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (x y : α) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro heq
    obtain ⟨hx, hy⟩ : x ^ 2 = 0 ∧ y ^ 2 = 0 := by
      rwa [← add_eq_zero_iff_of_nonneg] <;> apply sq_nonneg
    constructor <;> apply eq_zero_of_pow_eq_zero <;> assumption
  · rintro ⟨rfl, rfl⟩
    simp

namespace GaussInt

def norm (x : GaussInt) :=
  x.re ^ 2 + x.im ^ 2

@[simp]
theorem norm_nonneg (x : GaussInt) : 0 ≤ norm x := by
  apply add_nonneg <;> apply sq_nonneg

theorem norm_eq_zero (x : GaussInt) : norm x = 0 ↔ x = 0 := by
  rw [norm, sq_add_sq_eq_zero, GaussInt.ext_iff]
  rfl

theorem norm_pos (x : GaussInt) : 0 < norm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, ne_comm]
  simp [norm_eq_zero]

theorem norm_mul (x y : GaussInt) : norm (x * y) = norm x * norm y := by
  simp [norm]
  ring

def conj (x : GaussInt) : GaussInt :=
  ⟨x.re, -x.im⟩

@[simp]
theorem conj_re (x : GaussInt) : (conj x).re = x.re := rfl

@[simp]
theorem conj_im (x : GaussInt) : (conj x).im = -x.im := rfl

theorem norm_conj (x : GaussInt) : norm (conj x) = norm x := by simp [norm]

instance : Div GaussInt :=
  ⟨fun x y ↦ ⟨(x * conj y).re.div' (norm y), (x * conj y).im.div' (norm y)⟩⟩

instance : Mod GaussInt :=
  ⟨fun x y ↦ x - y * (x / y)⟩

theorem div_def (x y : GaussInt) :
    x / y = ⟨(x * conj y).re.div' (norm y), (x * conj y).im.div' (norm y)⟩ :=
  rfl

theorem mod_def (x y : GaussInt) : x % y = x - y * (x / y) :=
  rfl

theorem norm_mod_lt (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    norm (x % y) < norm y := by
  have norm_y_pos : 0 < norm y := by rwa [norm_pos]
  have mod_mul_conj : x % y * conj y = ⟨(x * conj y).re.mod' (norm y), (x * conj y).im.mod' (norm y)⟩
  · ext <;> simp [mod_def, div_def, Int.mod'_eq, norm] <;> ring
  have : norm (x % y) * norm y ≤ norm y / 2 * norm y
  · calc  norm (x % y) * norm y
        = norm (x % y * conj y) := by simp only [norm_mul, norm_conj]
      _ = |(x * conj y).re.mod' (norm y)| ^ 2 + |(x * conj y).im.mod' (norm y)| ^ 2 := by
            simp [mod_mul_conj, norm]
      _ ≤ (norm y / 2) ^ 2 + (norm y / 2) ^ 2 := by gcongr <;> apply Int.abs_mod'_le _ _ norm_y_pos
      _ = norm y / 2 * (norm y / 2 * 2) := by ring
      _ ≤ norm y / 2 * norm y := by gcongr; apply Int.ediv_mul_le; simp
  calc  norm (x % y)
      ≤ norm y / 2 := le_of_mul_le_mul_right this norm_y_pos
    _ < norm y := by apply Int.ediv_lt_of_lt_mul <;> omega

theorem coe_natAbs_norm (x : GaussInt) : ((norm x).natAbs : ℤ) = norm x :=
  Int.natAbs_of_nonneg (norm_nonneg _)

theorem natAbs_norm_mod_lt (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    (norm (x % y)).natAbs < (norm y).natAbs := by
  rw [← Int.ofNat_lt]
  simp [abs_of_nonneg]
  exact norm_mod_lt x hy

theorem not_norm_mul_left_lt_norm (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    ¬(norm (x * y)).natAbs < (norm x).natAbs := by
  apply not_lt_of_ge
  rw [norm_mul, Int.natAbs_mul]
  apply le_mul_of_one_le_right (Nat.zero_le _)
  rw [← Int.ofNat_le, coe_natAbs_norm]
  exact Int.add_one_le_of_lt (by rwa [norm_pos])

instance : EuclideanDomain GaussInt :=
  { quotient := (· / ·)
    quotient_zero x := by simp [div_def]; rfl
    remainder := (· % ·)
    quotient_mul_add_remainder_eq x y := by rw [mod_def]; ring
    r := (measure (Int.natAbs ∘ norm)).rel
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := not_norm_mul_left_lt_norm }

example (x : GaussInt) : Irreducible x ↔ Prime x :=
  irreducible_iff_prime

end GaussInt
