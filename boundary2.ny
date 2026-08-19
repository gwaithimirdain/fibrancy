{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "fibrant_types"

def ∂ : Type ≔ data [
| zero. : ∂
| suc. : (y₀ y₁ : ∂) → Br ∂ y₀ y₁ → T y₀ → T y₁ → ∂ ]

and T (y : ∂) : Type ≔ match y [
| zero. ↦ Type
| suc. y₀ y₁ y₂ x₀ x₁ ↦ Br T y₂ x₀ x₁]

def El∂ (y : ∂) : Type ≔ match y [
| zero. ↦ sig ()
| suc. y₀ y₁ y₂ x₀ x₁ ↦ sig (
    z₀ : El∂ y₀,
    z₁ : El∂ y₁,
    z₂ : Br El∂ y₂ z₀ z₁,
    w₀ : ElT y₀ x₀ z₀,
    w₁ : ElT y₁ x₁ z₁ )]

and ElT (y : ∂) (x : T y) (z : El∂ y) : Type ≔ match y [
| zero. ↦ x
| suc. y₀ y₁ y₂ x₀ x₁ ↦ Br ElT y₂ x (z .z₂) (z .w₀) (z .w₁)]

def BrElT (y₀ y₁ : ∂) (y₂ : Br ∂ y₀ y₁) (x₀ : T y₀) (x₁ : T y₁)
  (x₂ : Br T y₂ x₀ x₁) (z₀ : El∂ y₀) (z₁ : El∂ y₁) (z₂ : Br El∂ y₂ z₀ z₁)
  : Br Type (ElT y₀ x₀ z₀) (ElT y₁ x₁ z₁)
  ≔ rel ElT y₂ x₂ z₂

def f∂ (y : ∂) : Type ≔ match y [
| zero. ↦ sig ()
| suc. y₀ y₁ y₂ A₀ A₁ ↦ sig (
    f₀ : f∂ y₀,
    f₁ : f∂ y₁,
    f₂ : Br f∂ y₂ f₀ f₁,
    g₀ : fT y₀ A₀ f₀,
    g₁ : fT y₁ A₁ f₁ )]

and fT (y : ∂) (A : T y) (f : f∂ y) : Type ≔ match y [
| zero. ↦ isFibrant A
| suc. y₀ y₁ y₂ A₀ A₁ ↦ Br fT y₂ A (f .f₂) (f .g₀) (f .g₁)]

def fBrElT
  ` cube of types
  (y₀ y₁ : ∂) (y₂ : Br ∂ y₀ y₁) (x₀ : T y₀) (x₁ : T y₁)
  (x₂ : Br T y₂ x₀ x₁)
  ` cube of elements
  (z₀ : El∂ y₀) (z₁ : El∂ y₁) (z₂ : Br El∂ y₂ z₀ z₁) (w₀ : ElT y₀ x₀ z₀)
  (w₁ : ElT y₁ x₁ z₁)
  ` the cube is fibrant
  (f₀ : f∂ y₀) (f₁ : f∂ y₁) (f₂ : Br f∂ y₂ f₀ f₁) (g₀ : fT y₀ x₀ f₀)
  (g₁ : fT y₁ x₁ f₁) (g₂ : Br fT y₂ x₂ f₂ g₀ g₁)
  : isFibrant (BrElT y₀ y₁ y₂ x₀ x₁ x₂ z₀ z₁ z₂ w₀ w₁)
  ≔ match y₂ [
| zero. ⤇ g₂ .id w₀ w₁
| suc. y₀′ y₁′ y₂′ x₀′ x₁′ ⤇
    rel fBrElT y₀′.2 y₁′.2 y₂′.2 x₀′.2 x₁′.2 x₂ (z₂ .z₀) (z₂ .z₁) (z₂ .z₂)
        (z₂ .w₀) (z₂ .w₁) (f₂ .f₀) (f₂ .f₁) (f₂ .f₂) (f₂ .g₀) (f₂ .g₁) g₂
      .id w₀ w₁]

def fT_l (y₀ y₁ : ∂) (y₂ : Br ∂ y₀ y₁) (A₀ : T y₀) (A₁ : T y₁)
  (A₂ : Br T y₂ A₀ A₁) (f₀ : f∂ y₀) (f₁ : f∂ y₁) (f₂ : Br f∂ y₂ f₀ f₁)
  (g₀ : fT y₀ A₀ f₀) (g : fT y₀ A₀ f₀) (g₁ : fT y₁ A₁ f₁)
  (g₂ : Br fT y₂ A₂ f₂ g₀ g₁)
  : Br fT y₂ A₂ f₂ g g₁
  ≔ match y₂ [ zero. ⤇ ¿ʔ | suc. y₀′ y₁′ 𝑥 𝑦 𝑧 ⤇ ¿fT_lʔ ]

{`
def f∂ : ∂ → Type ≔ data [
| zero. : f∂ zero.
| suc. (y₀ y₁ : ∂) (y₂ : Br ∂ y₀ y₁) (A₀ : T y₀) (A₁ : T y₁) (f₀ : f∂ y₀)
    (f₁ : f∂ y₁) (f₂ : Br f∂ y₂ f₀ f₁) (g₀ : fT y₀ A₀ f₀) (g₁ : fT y₁ A₁ f₁)
  : f∂ (suc. y₀ y₁ y₂ A₀ A₁) ]

and fT (y : ∂) (A : T y) (f : f∂ y) : Type ≔ match f [
| zero. ↦ isfTibrant A
| suc. y₀ y₁ y₂ A₀ A₁ f₀ f₁ f₂ g₀ g₁ ↦ Br fT y₂ A f₂ g₀ g₁]

def fT_l (y₀ y₁ : ∂) (y₂ : Br ∂ y₀ y₁) (A₀ : T y₀) (A₁ : T y₁)
  (A₂ : Br T y₂ A₀ A₁) (f₀ : f∂ y₀) (f₁ : f∂ y₁) (f₂ : Br f∂ y₂ f₀ f₁)
  (g₀ : fT y₀ A₀ f₀) (g : fT y₀ A₀ f₀) (g₁ : fT y₁ A₁ f₁)
  (g₂ : Br fT y₂ A₂ f₂ g₀ g₁)
  : Br fT y₂ A₂ f₂ g g₁
  ≔ ¿ʔ
 `}
