import MIL.Common

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective _ _ := Submonoid₁.ext



example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem


@[ext]
structure Subgroup₁ (G : Type) [Group G] extends Submonoid₁ G where
  /-- The inverse of an element of a subgroup belongs to the subgroup. -/
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier

/-- Subgroups in `G` can be seen as sets in `G`. -/
instance [Group G] : SetLike (Subgroup₁ G) G where
  coe := (·.carrier)
  coe_injective _ _ := Subgroup₁.ext

instance [Group G] : SubmonoidClass₁ (Subgroup₁ G) G where
  mul_mem := (·.mul_mem)
  one_mem := (·.one_mem)

instance Subgroup₁Group [Group G] (H : Subgroup₁ G) : Group H :=
{ SubMonoid₁Monoid H.toSubmonoid₁ with
  inv := fun ⟨x, hx⟩ ↦ ⟨x⁻¹, H.inv_mem hx⟩
  inv_mul_cancel := fun ⟨x, _⟩ ↦ SetCoe.ext (inv_mul_cancel x) }

class SubgroupClass₁ (S : Type) (G : Type) [Group G] [SetLike S G] : Prop
    extends SubmonoidClass₁ S G where
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance [Group G] : SubgroupClass₁ (Subgroup₁ G) G :=
  { (inferInstance : SubmonoidClass₁ (Subgroup₁ G) G) with
    inv_mem := Subgroup₁.inv_mem }


instance [Monoid M] : Min (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro x y z ⟨v, hv, w, hw, h⟩ ⟨v', hv', w', hw', h'⟩
      use v * v', N.mul_mem hv hv'
      use w * w', N.mul_mem hw hw'
      calc  x * (v * v')
          = x * v * v' := by rw [mul_assoc]
        _ = y * w * v' := by rw [h]
        _ = w * (y * v') := by rw [mul_comm y, mul_assoc]
        _ = w * (z * w') := by rw [h']
        _ = z * (w * w') := by rw [← mul_assoc, mul_comm w, mul_assoc]
}

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  Quotient := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂ (· * ·) (by
      intro a₁ a₂ ⟨w, hw, z, hz, h⟩ b₁ b₂ ⟨w', hw', z', hz', h'⟩
      use w * w', N.mul_mem hw hw'
      use z * z', N.mul_mem hz hz'
      calc  (a₁ * b₁) * (w  * w')
          = (a₁ * w ) * (b₁ * w') := by rw [mul_assoc, ← mul_assoc b₁, mul_comm b₁, mul_assoc, ← mul_assoc]
        _ = (a₂ * z ) * (b₂ * z') := by rw [h, h']
        _ = (a₂ * b₂) * (z  * z') := by rw [mul_assoc, ← mul_assoc z, mul_comm z, mul_assoc, ← mul_assoc]
    )
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    dsimp only
    rw [mul_assoc]
  one := QuotientMonoid.mk N 1
  one_mul := by rintro ⟨a⟩; apply Quotient.sound; dsimp only; rw [one_mul]
  mul_one := by rintro ⟨a⟩; apply Quotient.sound; dsimp only; rw [mul_one]
