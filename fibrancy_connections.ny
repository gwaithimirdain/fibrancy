{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"
import "univalence"

def Br_hPropᵈ (A : Type) (P : A → Type) : Type ≔ codata [
| x .relate_l.p
  : (a₀ : A.0) → (a₁ : A.1) → (p₀ p : P.0 a₀) → (p₁ : P.1 a₁)
    (a₂ : A.2 a₀ a₁) → (p₂ : P.2 a₂ p₀ p₁)
    → P.2 a₂ p p₁
| x .relate_r.p
  : (a₀ : A.0) → (a₁ : A.1) → (p₀ : P.0 a₀) → (p p₁ : P.1 a₁)
    (a₂ : A.2 a₀ a₁) → (p₂ : P.2 a₂ p₀ p₁)
    → P.2 a₂ p₀ p
| x .id.p
  : (a₀ : A.0) → (a₁ : A.1) → (p₀ : P.0 a₀) → (p₁ : P.1 a₁)
    → Br_hPropᵈ (A.2 a₀ a₁) (a₂ ↦ P.2 a₂ p₀ p₁) ]

def Br_hPropᵈ_lemma (A : Type) (P : A → Type) (bP : Br_hPropᵈ A P) (a : A)
  (p : P a)
  : isFibrant (P a)
  ≔ [
| .trr.p ↦ _ ↦ p.1
| .trl.p ↦ _ ↦ p.0
| .liftr.p ↦ p0 ↦ bP.2 .relate_l a.0 a.1 p.0 p0 p.1 a.2 p.2
| .liftl.p ↦ p1 ↦ bP.2 .relate_r a.0 a.1 p.0 p1 p.1 a.2 p.2
| .id.p ↦ p0 p1 ↦
    Br_hPropᵈ_lemma (A.2 a.0 a.1) (a2 ↦ P.2 a2 p0 p1)
      (bP.2 .id a.0 a.1 p0 p1) a.2
      (bP.2 .relate_r a.0 a.1 p0 p1 p.1 a.2
         (bP.2 .relate_l a.0 a.1 p.0 p0 p.1 a.2 p.2))]


def fibProp_l (A₀ A₁ : Type) (A₂ : Br Type A₀ A₁) (f₀ f : isFibrant A₀)
  (f₁ : isFibrant A₁) (f₂ : Br (isFibrant) A₂ f₀ f₁)
  : Br (isFibrant) A₂ f f₁
  ≔ [
| .trr.p ⤇ a ⤇ f₂.2 .id.1 (f.2 .liftr a.0) (f₁.2 .liftr a.1) .trr a.2

| .trr.1 ⤇ f₂ .trr
| .trl.p ⤇ a ⤇ f₂.2 .id.1 (f.2 .liftl a.0) (f₁.2 .liftl a.1) .trl a.2

| .trl.1 ⤇ f₂ .trl
| .liftr.p ⤇ a ⤇
    sym (f₂.2 .id.1 (f.2 .liftr a.0) (f₁.2 .liftr a.1) .liftr a.2)
| .liftr.1 ⤇ f₂ .liftr
| .liftl.p ⤇ a ⤇
    sym (f₂.2 .id.1 (f.2 .liftl a.0) (f₁.2 .liftl a.1) .liftl a.2)
| .liftl.1 ⤇ f₂ .liftl
| .id.p ⤇ a₀ a₁ ⤇
    fibProp_l (A₀.2 a₀.0 a₁.0) (A₁.2 a₀.1 a₁.1) (sym A₂.2 a₀.2 a₁.2)
      (f₀.2 .id a₀.0 a₁.0) (f.2 .id a₀.0 a₁.0) (f₁.2 .id a₀.1 a₁.1)
      ((f₂.2) .id.2 a₀.2 a₁.2)
| .id.1 ⤇ f₂ .id]

`Alternate (Mike's) construction of trr.p for fibProp_l
{`rel (f₂.1 .id) {f.2 .trr a.0} {f₀.2 .trr a.0}
(rel f₀.2 .id.2 (f.2 .liftr a.0) (f₀.2 .liftr a.0) .trr (rel a.0))
(rel (f₁.2 .trr a.1))
.trl (f₂.2 .trr.2 a.2)`}

`Alternate (Mike's) construction of trl.p for fibProp_l
{`rel (f₂.0 .id) {f.2 .trl a.0} {f₀.2 .trl a.0}
(rel f₀.2 .id.2 (f.2 .liftl a.0) (f₀.2 .liftl a.0) .trl (rel a.0))
(rel (f₁.2 .trl a.1))
.trl (f₂.2 .trl.2 a.2)`}


def fibProp_r (A₀ A₁ : Type) (A₂ : Br Type A₀ A₁) (f₀ : isFibrant A₀)
  (f f₁ : isFibrant A₁) (f₂ : Br (isFibrant) A₂ f₀ f₁)
  : Br (isFibrant) A₂ f₀ f
  ≔ [
| .trr.p ⤇ a ⤇ f₂.2 .id.1 (f₀.2 .liftr a.0) (f.2 .liftr a.1) .trr a.2
| .trr.1 ⤇ f₂ .trr
| .trl.p ⤇ a ⤇ f₂.2 .id.1 (f₀.2 .liftl a.0) (f.2 .liftl a.1) .trl a.2
| .trl.1 ⤇ f₂ .trl
| .liftr.p ⤇ a ⤇
    sym (f₂.2 .id.1 (f₀.2 .liftr a.0) (f.2 .liftr a.1) .liftr a.2)
| .liftr.1 ⤇ f₂ .liftr
| .liftl.p ⤇ a ⤇
    sym (f₂.2 .id.1 (f₀.2 .liftl a.0) (f.2 .liftl a.1) .liftl a.2)
| .liftl.1 ⤇ f₂ .liftl
| .id.p ⤇ a a' ⤇
    fibProp_r (A₀.2 a.0 a'.0) (A₁.2 a.1 a'.1) (sym A₂.2 a.2 a'.2)
      (f₀.2 .id a.0 a'.0) (f.2 .id a.1 a'.1) (f₁.2 .id a.1 a'.1)
      (f₂.2 .id.2 a.2 a'.2)
| .id.1 ⤇ f₂ .id]

`An application of fibProp_l: two proofs of isFibrant(A) are always related 
def fibProp_rel (A : Type) (f f₀ : isFibrant A)
  : Br (isFibrant) (rel A) f f₀
  ≔ fibProp_l A A (rel A) f₀ f f₀ (rel f₀)



def fib_hProp_lemma : Br_hPropᵈ Type isFibrant ≔ [
| .relate_l.p ↦ A₀ A₁ f₀ f f₁ A₂ f₂ ↦ fibProp_l A₀ A₁ A₂ f₀ f f₁ f₂
| .relate_r.p ↦ A₀ A₁ f₀ f f₁ A₂ f₂ ↦ fibProp_r A₀ A₁ A₂ f₀ f f₁ f₂
| .id.p ↦ A₀ A₁ f₀ f₁ ↦ [
  | .relate_l.p ↦ A₂₀ A₂₁ f₂₀ f f₂₁ A₂₂ f₂₂ ↦ ¿ʔ
  | .relate_r.p ↦ ¿ʔ
  | .id.p ↦ ¿ʔ]]


def fibProp_ll (A₀₀ A₀₁ : Type) (A₀₂ : Type⁽ᵖ⁾ A₀₀ A₀₁) (A₁₀ A₁₁ : Type)
  (A₁₂ : Type⁽ᵖ⁾ A₁₀ A₁₁) (f₀₀ : isFibrant A₀₀) (f₀₁ : isFibrant A₀₁)
  (f₀₂ : isFibrant⁽ᵖ⁾ A₀₂ f₀₀ f₀₁) (f₁₀ : isFibrant A₁₀)
  (f₁₁ : isFibrant A₁₁) (f₁₂ : isFibrant⁽ᵖ⁾ A₁₂ f₁₀ f₁₁)
  (A₂₀ : Type⁽ᵖ⁾ A₀₀ A₁₀) (A₂₁ : Type⁽ᵖ⁾ A₀₁ A₁₁)
  (f₂₀ : isFibrant⁽ᵖ⁾ A₂₀ f₀₀ f₁₀) (f : isFibrant⁽ᵖ⁾ A₂₀ f₀₀ f₁₀)
  (f₂₁ : isFibrant⁽ᵖ⁾ A₂₁ f₀₁ f₁₁) (A₂₂ : Type⁽ᵖᵖ⁾ A₀₂ A₁₂ A₂₀ A₂₁)
  (f₂₂ : isFibrant⁽ᵖᵖ⁾ A₂₂ f₀₂ f₁₂ f₂₀ f₂₁)
  : isFibrant⁽ᵖᵖ⁾ A₂₂ f₀₂ f₁₂ f f₂₁
  ≔ [
| .trr.p ⤇ a ⤇ ¿f₂₂.2 .id.1ʔ
| .trr.1 ⤇ ¿f₂₂ .trr.1ʔ
| .trr.2 ⤇ f₂₂ .trr.2
| .trl.p ⤇ ¿ʔ
| .trl.1 ⤇ ¿ʔ
| .trl.2 ⤇ ¿ʔ
| .liftr.p ⤇ ¿ʔ
| .liftr.1 ⤇ ¿ʔ
| .liftr.2 ⤇ ¿ʔ
| .liftl.p ⤇ ¿ʔ
| .liftl.1 ⤇ ¿ʔ
| .liftl.2 ⤇ ¿ʔ
| .id.p ⤇ ¿ʔ
| .id.1 ⤇ ¿ʔ
| .id.2 ⤇ ¿ʔ]
{`[
| .relate_l.p ↦ A₂₀ A₂₁ f₂₀ f₂ f₂₁ A₂₂ f₂₂ ↦ ¿ʔ
| .relate_r.p ↦ ¿ʔ
| .id.p ↦ ¿ʔ]`}




def Br_hPropᵈ_fib : Br_hPropᵈ Type isFibrant ≔ [
| .relate_l.p ↦ A₀ A₁ f₀ f f₁ A₂ f₂ ↦ fibProp_l A₀ A₁ A₂ f₀ f f₁ f₂
| .relate_r.p ↦ A₀ A₁ f₀ f f₁ A₂ f₂ ↦ fibProp_r A₀ A₁ A₂ f₀ f f₁ f₂
| .id.p ↦ A₀ A₁ f₀ f₁ ↦ ¿ʔ]

def fiblemma (A : Type) (f : isFibrant A) : isFibrant (isFibrant A)
  ≔ Br_hPropᵈ_lemma Type isFibrant Br_hPropᵈ_fib A f

def fiblemma2 (A₀ : Type) (f₀ : isFibrant A₀) (A₁ : Type)
  (f₁ : isFibrant A₁) (A₂ : Br Type A₀ A₁)
  (f₂ : (x₀ : A₀) → (x₁ : A₁) → isFibrant (A₂ x₀ x₁))
  : isFibrant (Br isFibrant A₂ f₀ f₁)
  ≔ [
| .trr.p ↦ ¿ʔ
| .trl.p ↦ ¿ʔ
| .liftr.p ↦ ¿ʔ
| .liftl.p ↦ ¿ʔ
| .id.p ↦ ¿ʔ]





def fibProp (A : Type) (f₀ f₁ : isFibrant A) : Br (isFibrant A) f₀ f₁ ≔ [
| .trr.p ⤇ x ⤇ ¿rel f₀.0ʔ
| .trr.1 ⤇ rel f₀ .trr
| .trl.p ⤇ ¿ʔ
| .trl.1 ⤇ rel f₀ .trl
| .liftr.p ⤇ ¿ʔ
| .liftr.1 ⤇ ¿ʔ
| .liftl.p ⤇ ¿ʔ
| .liftl.1 ⤇ ¿ʔ
| .id.p ⤇ ¿ʔ
| .id.1 ⤇ ¿ʔ]


def hasConn (A : Type) : Type ≔ codata [
| x .lconn
  : (a₀ a₁ : A) → (a₂ : Br A a₀ a₁) → Br (Br A) (rel a₀) a₂ (rel a₀) a₂
| x .rconn
  : (a₀ a₁ : A) → (a₂ : Br A a₀ a₁) → Br (Br A) a₂ (rel a₁) a₂ (rel a₁)
| x .id.p
  : (a₀ : A.0) → (a₁ : A.1) → (a₂ : A.2 a₀ a₁) → hasConn (A.2 a₀ a₁) ] 

def hasConnType : hasConn Type ≔ [
| .lconn ↦ A₀ A₁ A₂ ↦ sig (
    x .d : Br A₀ x.01 x.10,
    x .sq0 : Br (Br A₀) (rel x.00) (x .d) (x.02) (x.20),
    x .sq1 : Br A₂ (x .d) (rel x.11) x.21 x.12 )
| .rconn ↦ A₀ A₁ A₂ ↦ sig (
    x .d : Br A₁ x.01 x.10,
    x .sq0 : Br (Br A₁) (x .d) (rel x.11) (x.21) (x.12),
    x .sq1 : Br A₂ (rel x.00) (x .d) x.02 x.20 )
| .id.p ↦ ¿ʔ
{` Warning: using (rel hasConnType .id) to fill this is non-productive `}
]

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
