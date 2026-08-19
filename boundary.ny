{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "fibrant_types"

def ∂ : Type ≔ data [
| zero. : ∂
| suc. : (y₀ y₁ : ∂) → Br ∂ y₀ y₁ → T y₀ → T y₁ → ∂ ]

and T (y : ∂) : Type ≔ match y [
| zero. ↦ Fib
| suc. y₀ y₁ y₂ x₀ x₁ ↦ Br T y₂ x₀ x₁]

def El∂ (y : ∂) : Fib ≔ match y [
| zero. ↦ ⊤𝕗
| suc. y₀ y₁ y₂ x₀ x₁ ↦
    Σ𝕗 (El∂ y₀)
      (z₀ ↦
       Σ𝕗 (El∂ y₁)
         (z₁ ↦
          Σ𝕗 (Idd𝕗 (El∂ y₀) (El∂ y₁) (Br El∂ y₂) z₀ z₁)
            (z₂ ↦ ElT y₀ x₀ z₀ ×𝕗 ElT y₁ x₁ z₁)))]

and ElT (y : ∂) (x : T y) (z : El∂ y .t) : Fib ≔ match y [
| zero. ↦ x
| suc. y₀ y₁ y₂ x₀ x₁ ↦
    let y₀̅ ≔ z .fst in
    let y₁̅ ≔ z .snd .fst in
    let y₂̅ ≔ z .snd .snd .fst in
    let x₀̅ ≔ z .snd .snd .snd .fst in
    let x₁̅ ≔ z .snd .snd .snd .snd in
    Idd𝕗 (ElT y₀ x₀ y₀̅) (ElT y₁ x₁ y₁̅) (Br ElT y₂ x y₂̅) x₀̅ x₁̅]

def line∂ (A₀ : Fib) (A₁ : Fib) : ∂ ≔ suc. zero. zero. zero. A₀ A₁

def lineT (A₀ : Fib) (A₁ : Fib) (A₂ : Br Fib A₀ A₁) : T (line∂ A₀ A₁) ≔ A₂

def square∂ (A00 A01 : Fib) (A02 : Br Fib A00 A01) (A10 A11 : Fib)
  (A12 : Br Fib A10 A11) (A20 : Br Fib A00 A10) (A21 : Br Fib A01 A11)
  : ∂
  ≔ suc. (line∂ A00 A10) (line∂ A01 A11) (rel line∂ A02 A12)
      (lineT A00 A10 A20) (lineT A01 A11 A21)

def squareT (A00 A01 : Fib) (A02 : Br Fib A00 A01) (A10 A11 : Fib)
  (A12 : Br Fib A10 A11) (A20 : Br Fib A00 A10) (A21 : Br Fib A01 A11)
  (A22 : Br (Br Fib) A02 A12 A20 A21)
  : T (square∂ A00 A01 A02 A10 A11 A12 A20 A21)
  ≔ rel lineT A02 A12 A22

def 𝕗T (y : ∂) : isFibrant (T y) ≔ [
| .trr.p ↦ match y.2 [
  | zero. ⤇ A ↦ A
  | suc. y0 y1 y2 x0 x1 ⤇ 𝕗T⁽ᵖᵖ⁾ y2.2 .id.1 x0.2 x1.2 .trr]
| .trl.p ↦ match y.2 [
  | zero. ⤇ A ↦ A
  | suc. y0 y1 y2 x0 x1 ⤇ 𝕗T⁽ᵖᵖ⁾ y2.2 .id.1 x0.2 x1.2 .trl]
| .liftr.p ↦ match y.2 [
  | zero. ⤇ A ↦ rel A
  | suc. y0 y1 y2 x0 x1 ⤇ 𝕗T⁽ᵖᵖ⁾ y2.2 .id.1 x0.2 x1.2 .liftr]
| .liftl.p ↦ match y.2 [
  | zero. ⤇ A ↦ rel A
  | suc. y0 y1 y2 x0 x1 ⤇ 𝕗T⁽ᵖᵖ⁾ y2.2 .id.1 x0.2 x1.2 .liftl]
| .id.p ↦ x0 x1 ↦ 𝕗T (suc. y.0 y.1 y.2 x0 x1)]

def 𝕗Fib : isFibrant Fib ≔ 𝕗T zero.

axiom A00 : Fib
axiom A01 : Fib
axiom A02 : Br Fib A00 A01
axiom A10 : Fib
axiom A11 : Fib
axiom A12 : Br Fib A10 A11
axiom A20 : Br Fib A00 A10

` Spins forever
` echo rel (rel 𝕗Fib) .id.1 A02 A12 .trr
