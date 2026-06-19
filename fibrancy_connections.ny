{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"
import "univalence"

def fiblemma (A : Type) (f : isFibrant A) : isFibrant (isFibrant A) ≔ [
| .trr.p ↦ x ↦ f.1
| .trl.p ↦ x ↦ f.0
| .liftr.p ↦ f₀ ↦ ¿ʔ
| .liftl.p ↦ ¿ʔ
| .id.p ↦ ¿ʔ]

def fibProp (A : Type) (f₀ f₁ : isFibrant A) : Br (isFibrant A) f₀ f₁ ≔ [
| .trr.p ⤇ x ⤇ ¿ʔ
| .trr.1 ⤇ ¿ʔ
| .trl.p ⤇ ¿ʔ
| .trl.1 ⤇ ¿ʔ
| .liftr.p ⤇ ¿ʔ
| .liftr.1 ⤇ ¿ʔ
| .liftl.p ⤇ ¿ʔ
| .liftl.1 ⤇ ¿ʔ
| .id.p ⤇ ¿ʔ
| .id.1 ⤇ ¿ʔ]

def fiblemma2 (A₀ : Type) (f₀ : isFibrant A₀) (A₁ : Type)
  (f₁ : isFibrant A₁) (A₂ : Br Type A₀ A₁) (f₂ : Br isFibrant A₂ f₀ f₁)
  : isFibrant (Br isFibrant A₂ f₀ f₁)
  ≔ ¿ʔ

def hasConn (A : Type) : Type ≔ codata [
| x .lconn
  : (a₀ a₁ : A) → (a₂ : Br A a₀ a₁) → Br (Br A) (rel a₀) a₂ (rel a₀) a₂
| x .rconn
  : (a₀ a₁ : A) → (a₂ : Br A a₀ a₁) → Br (Br A) a₂ (rel a₁) a₂ (rel a₁)
| x .id.p
  : (a₀ : A.0) → (a₁ : A.1) → (a₂ : A.2 a₀ a₁) → hasConn (A.2 a₀ a₁) ] 

def fibHasConn (A : Type) (f : isFibrant A) : hasConn A ≔ [
| .lconn ↦ a₀ a₁ a₂ ↦
    let P : A → Fib ≔ a ↦ (Br A a₀ a, rel f .id a₀ a) in
    ¿rel P a₂ʔ
| .rconn ↦ ¿ʔ
| .id.p ↦ ¿ʔ]


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



def BrisFib_fib (A₀ A₁:Type) (A₂:Br Type A₀ A₁) (f₀:isFibrant A₀) (f₁:isFibrant A₁) : isFibrant (Br isFibrant A₂ f₀ f₁)

section parametrized ≔

  {` We can also consider higher destructors whose types depend on the parameters, but they have to depend on a degenerated version of the parameters.  In this case, however, it seems that we require the *parameter* to have connections. `}
  axiom Γ : Type
  axiom 𝕔Γ : hasConn Γ
  axiom A (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) : Type
  axiom 𝕗A (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) : isFibrant (A x₀ x₁ x₂)

  {` For simplicity, we leave off any lower destructors. `}
  def √A (x : Γ) : Type ≔ codata [ a .root.p : A x.0 x.1 x.2 ]

  def 𝕗√A (x : Γ) : isFibrant (√A x) ≔ [
  | .trr.p ↦ a₀ ↦ [
    | .root.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .trr (a₀.2 .root)]
  | .trl.p ↦ a₁ ↦ [
    | .root.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .trl (a₁.2 .root)]
  | .liftr.p ↦ a₀ ↦ [
    | .root.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .liftr (a₀.2 .root)
    | .root.1 ↦
        rel 𝕗A (rel x.0) x.2 (𝕔Γ .lconn x.0 x.1 x.2) .trr (rel a₀ .root)
    {` Here we need a connection structure on Γ, to get a connection square. `}
    ]
  | .liftl.p ↦ a₁ ↦ [
    | .root.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .liftl (a₁.2 .root)
    | .root.1 ↦
        rel 𝕗A x.2 (rel x.1) (𝕔Γ .rconn x.0 x.1 x.2) .trl (rel a₁ .root)
    ]
  {` Again, we can't do the recursive case. `}
  | .id.p ↦ a₀ a₁ ↦ ¿ʔ]

end
