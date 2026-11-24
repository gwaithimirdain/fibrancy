{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-discrete-coreflector") -*- `}

import "bookhott"
import "isfibrant"
import "hott_bookhott"
import "fibrant_types"

def condFib (A : Type) : Type ≔ A → isFibrant A

def cfprod (A B : Type) (𝕗A : condFib A) (𝕗B : condFib B) : condFib (A × B)
  ≔ u ↦ 𝕗prod A B (𝕗A (u .fst)) (𝕗B (u .snd))

def cfΣ (A : Type) (B : A → Type) (𝕗A : condFib A)
  (𝕗B : (x : A) → isFibrant (B x))
  : condFib (Σ A B)
  ≔ u ↦ 𝕗Σ A B (𝕗A (u .fst)) 𝕗B

def cfTotBr (A : Type) (𝕗A : condFib A)
  : condFib (Σ (A × A) (u ↦ Br A (u .0) (u .1)))
  ≔ u ↦
    𝕗Σ (A × A) (u ↦ Br A (u .0) (u .1))
      (𝕗prod A A (𝕗A (u .0 .0)) (𝕗A (u .0 .1)))
      (x ↦ rel (𝕗A (x .0)) .id (x .0) (x .1))

def lconn (A : Type) (fA : condFib A) (x y : A) (p : Br A x y)
  : A⁽ᵖᵖ⁾ (rel x) p (rel x) p
  ≔ coconn (A, fA x) x y p

def rconn (A : Type) (fA : condFib A) (x y : A) (p : Br A x y)
  : A⁽ᵖᵖ⁾ p (rel y) p (rel y)
  ≔ conn (A, fA x) x y p

def condfib_eqv (A B : Type) (e : A ≅ B) (fA : condFib A) : condFib B
  ≔ b ↦ 𝕗eqv A B e (fA (e .fro b))

