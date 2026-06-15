{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"
import "univalence"

def hasConn (A : Type) : Type ≔ codata [
| x .lconn
  : (a₀ a₁ : A) → (a₂ : Br A a₀ a₁) → Br (Br A) (rel a₀) a₂ (rel a₀) a₂
| x .rconn
  : (a₀ a₁ : A) → (a₂ : Br A a₀ a₁) → Br (Br A) a₂ (rel a₁) a₂ (rel a₁)
| x .id.p
  : (a₀ : A.0) → (a₁ : A.1) → (a₂ : A.2 a₀ a₁) → hasConn (A.2 a₀ a₁) ] 

def fibHasConn (A : Type) (f : isFibrant A) : hasConn A ≔ [
| .lconn ↦ ¿ʔ
| .rconn ↦ ¿ʔ
| .id.p ↦ ¿ʔ]

def fiblemma (A : Type) (f : isFibrant A) : isFibrant (isFibrant A) ≔ ¿ʔ

def fiblemma2 (A₀ : Type) (f₀ : isFibrant A₀) (A₁ : Type)
  (f₁ : isFibrant A₁) (A₂ : Br Type A₀ A₁) (f₂ : Br isFibrant A₂ f₀ f₁)
  : isFibrant (Br isFibrant A₂ f₀ f₁)
  ≔ ¿ʔ

def isFibHasConn (A : Type) : hasConn (isFibrant A) ≔ [
| .lconn ↦ f₀ f₁ f₂ ↦
    let l : hasConn (isFibrant A)
      ≔ fibHasConn (isFibrant A) (fiblemma A f₀) in
    l .lconn f₀ f₁ f₂
| .rconn ↦ f₀ f₁ f₂ ↦
    let l : hasConn (isFibrant A)
      ≔ fibHasConn (isFibrant A) (fiblemma A f₀) in
    l .rconn f₀ f₁ f₂
| .id.p ↦ f₀ f₁ f₂ ↦
    fibHasConn (isFibrant⁽ᵖ⁾ A.2 f₀ f₁) (fiblemma2 A.0 f₀ A.1 f₁ A.2 f₂)]


