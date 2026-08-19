` how to define boundaries and fillers of dimension n by induction on natural numbers

def ℕ : Type ≔ data [ zero. : ℕ | suc. : ℕ → ℕ ]
def 𝟙 : Type ≔ sig ()

{`
think about a boundary at n as two points (as in the boundary at
dimension 1):

b₀ is two points, b₁ is other two points, b₂ is two lines between b₀ and b₁:

b₀ = .            .
     |            |
b₂ = |            |
     |            |
b₁ = .            .
  
finally, f₀ is a filler for b₀, f₁ is a filler for b₁:

           f₀
b₀ = .------------.
     |            |
b₂ = |            |
     |            |
b₁ = .------------.
           f₁

so we built a one higher dimensional boundary from a lower dimensional one
`}
def ∂ : ℕ → Type ≔ [
| zero. ↦ 𝟙
| suc. n ↦ sig (
    b₀ : ∂ n, ` b for boundary
    b₁ : ∂ n,
    b₂ : Br (∂ n) b₀ b₁,
    f₀ : F n b₀, ` f for filler
    f₁ : F n b₁ )]

and F : (n : ℕ) → ∂ n → Type ≔ [
| zero. ↦ _ ↦ Type
| suc. n ↦ y ↦ Br (F n) (y .b₂) (y .f₀) (y .f₁)]

section dim0 ≔
  def b : ∂ 0 ≔ ()

  axiom A : Type

  def f : F 0 b ≔ A
end

section 1 ≔ 
  axiom A₀ : Type
  axiom A₁ : Type
  def b : ∂ 1 ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₀, f₁ ≔ A₁)

  axiom A₂ : Br Type A₀ A₁
  def f : F 1 b ≔ A₂
end

section dim2 ≔ 
  axiom A₀₀ : Type
  axiom A₀₁ : Type
  axiom A₀₂ : Type⁽ᵖ⁾ A₀₀ A₀₁
  axiom A₁₀ : Type
  axiom A₁₁ : Type
  axiom A₁₂ : Type⁽ᵖ⁾ A₁₀ A₁₁
  axiom A₂₀ : Type⁽ᵖ⁾ A₀₀ A₁₀
  axiom A₂₁ : Type⁽ᵖ⁾ A₀₁ A₁₁
  def b : ∂ 2 ≔ (
    b₀ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₀₀, f₁ ≔ A₀₁),
    b₁ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₁₀, f₁ ≔ A₁₁),
    b₂ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₂₀, f₁ ≔ A₂₁),
    f₀ ≔ A₀₂,
    f₁ ≔ A₁₂)

  axiom A₂₂ : Type⁽ᵖᵖ⁾ A₀₂ A₁₂ A₂₀ A₂₁
  def f : F 2 b ≔ sym A₂₂
end

section dim3 ≔ 
  axiom A₀₀₀ : Type
  axiom A₀₀₁ : Type
  axiom A₀₀₂ : Type⁽ᵖ⁾ A₀₀₀ A₀₀₁
  axiom A₀₁₀ : Type
  axiom A₀₁₁ : Type
  axiom A₀₁₂ : Type⁽ᵖ⁾ A₀₁₀ A₀₁₁
  axiom A₀₂₀ : Type⁽ᵖ⁾ A₀₀₀ A₀₁₀
  axiom A₀₂₁ : Type⁽ᵖ⁾ A₀₀₁ A₀₁₁
  axiom A₀₂₂ : Type⁽ᵖᵖ⁾ A₀₀₂ A₀₁₂ A₀₂₀ A₀₂₁
  axiom A₁₀₀ : Type
  axiom A₁₀₁ : Type
  axiom A₁₀₂ : Type⁽ᵖ⁾ A₁₀₀ A₁₀₁
  axiom A₁₁₀ : Type
  axiom A₁₁₁ : Type
  axiom A₁₁₂ : Type⁽ᵖ⁾ A₁₁₀ A₁₁₁
  axiom A₁₂₀ : Type⁽ᵖ⁾ A₁₀₀ A₁₁₀
  axiom A₁₂₁ : Type⁽ᵖ⁾ A₁₀₁ A₁₁₁
  axiom A₁₂₂ : Type⁽ᵖᵖ⁾ A₁₀₂ A₁₁₂ A₁₂₀ A₁₂₁
  axiom A₂₀₀ : Type⁽ᵖ⁾ A₀₀₀ A₁₀₀
  axiom A₂₀₁ : Type⁽ᵖ⁾ A₀₀₁ A₁₀₁
  axiom A₂₀₂ : Type⁽ᵖᵖ⁾ A₀₀₂ A₁₀₂ A₂₀₀ A₂₀₁
  axiom A₂₁₀ : Type⁽ᵖ⁾ A₀₁₀ A₁₁₀
  axiom A₂₁₁ : Type⁽ᵖ⁾ A₀₁₁ A₁₁₁
  axiom A₂₁₂ : Type⁽ᵖᵖ⁾ A₀₁₂ A₁₁₂ A₂₁₀ A₂₁₁
  axiom A₂₂₀ : Type⁽ᵖᵖ⁾ A₀₂₀ A₁₂₀ A₂₀₀ A₂₁₀
  axiom A₂₂₁ : Type⁽ᵖᵖ⁾ A₀₂₁ A₁₂₁ A₂₀₁ A₂₁₁
  def b : ∂ 3 ≔ (
    b₀ ≔ (
      b₀ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₀₀₀, f₁ ≔ A₀₀₁),
      b₁ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₀₁₀, f₁ ≔ A₀₁₁),
      b₂ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₀₂₀, f₁ ≔ A₀₂₁),
      f₀ ≔ A₀₀₂,
      f₁ ≔ A₀₁₂),
    b₁ ≔ (
      b₀ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₁₀₀, f₁ ≔ A₁₀₁),
      b₁ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₁₁₀, f₁ ≔ A₁₁₁),
      b₂ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₁₂₀, f₁ ≔ A₁₂₁),
      f₀ ≔ A₁₀₂,
      f₁ ≔ A₁₁₂),
    b₂ ≔ (
      b₀ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₂₀₀, f₁ ≔ A₂₀₁),
      b₁ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ A₂₁₀, f₁ ≔ A₂₁₁),
      b₂ ≔ (b₀ ≔ (), b₁ ≔ (), b₂ ≔ (), f₀ ≔ sym A₂₂₀, f₁ ≔ sym A₂₂₁),
      f₀ ≔ sym A₂₀₂,
      f₁ ≔ sym A₂₁₂),
    f₀ ≔ sym A₀₂₂,
    f₁ ≔ sym A₁₂₂)

  axiom A₂₂₂ : Type⁽ᵖᵖᵖ⁾ A₀₂₂ A₁₂₂ A₂₀₂ A₂₁₂ A₂₂₀ A₂₂₁
  def f : F 3 b ≔ A₂₂₂⁽³²¹⁾
end

section inductive ≔
  def ∂ : Type ≔ data [
  | z. : ∂
  | s. : (n₀ n₁ : ∂) → Br ∂ n₀ n₁ → F n₀ → F n₁ → ∂ ]

  and F : ∂ → Type ≔ data [
  | z. : Type → F z.
  | s.
    : (n₀ n₁ : ∂) (n₂ : Br ∂ n₀ n₁) (x₀ : F n₀) (x₁ : F n₁) → Br F n₂ x₀ x₁
      → F (s. n₀ n₁ n₂ x₀ x₁) ]

  ` it is much more difficult to use this inductive definition
end
