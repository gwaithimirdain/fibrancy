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
| .trr.p ⤇ a ⤇
    f₂₂.2
      .id.1 (sym (f₀₂.2 .liftr.2 a.02)) (sym (f₁₂.2 .liftr.2 a.12))
      .id.1 (sym (f.2 .liftr.2 a.20)) (sym (f₂₁.2 .liftr.2 a.21))
      .trr a.22
| .trr.1 ⤇ a ⤇ f₂₂ .id.2 (f .liftr a.0) (f₂₁ .liftr a.1) .trr a.2
| .trr.2 ⤇ f₂₂ .trr.2
| .trl.p ⤇ a ⤇
    f₂₂.2
      .id.1 (sym (f₀₂.2 .liftl.2 a.02)) (sym (f₁₂.2 .liftl.2 a.12))
      .id.1 (sym (f.2 .liftl.2 a.20)) (sym (f₂₁.2 .liftl.2 a.21))
      .trl a.22
| .trl.1 ⤇ a ⤇ f₂₂ .id.2 (f .liftl a.0) (f₂₁ .liftl a.1) .trl a.2
| .trl.2 ⤇ f₂₂ .trl.2
| .liftr.p ⤇ a ⤇
    (f₂₂.2
     .id.1 (sym (f₀₂.2 .liftr.2 a.02)) (sym (f₁₂.2 .liftr.2 a.12))
     .id.1 (sym (f.2 .liftr.2 a.20)) (sym (f₂₁.2 .liftr.2 a.21))
     .liftr a.22)⁽³¹²⁾
| .liftr.1 ⤇ a ⤇ sym (f₂₂ .id.2 (f .liftr a.0) (f₂₁ .liftr a.1) .liftr a.2)
| .liftr.2 ⤇ f₂₂ .liftr.2
| .liftl.p ⤇ a ⤇
    (f₂₂.2
     .id.1 (sym (f₀₂.2 .liftl.2 a.02)) (sym (f₁₂.2 .liftl.2 a.12))
     .id.1 (sym (f.2 .liftl.2 a.20)) (sym (f₂₁.2 .liftl.2 a.21))
     .liftl a.22)⁽³¹²⁾
| .liftl.1 ⤇ a ⤇ sym (f₂₂ .id.2 (f .liftl a.0) (f₂₁ .liftl a.1) .liftl a.2)
| .liftl.2 ⤇ f₂₂ .liftl.2
| .id.p ⤇ a₀ a₁ ⤇
    fibProp_ll (A₀₀.2 a₀.00 a₁.00) (A₀₁.2 a₀.01 a₁.01)
      (sym A₀₂.2 a₀.02 a₁.02) (A₁₀.2 a₀.10 a₁.10) (A₁₁.2 a₀.11 a₁.11)
      (sym A₁₂.2 a₀.12 a₁.12) (f₀₀.2 .id a₀.00 a₁.00)
      (f₀₁.2 .id a₀.01 a₁.01) (sym f₀₂.2 .id.1 a₀.02 a₁.02)
      (f₁₀.2 .id a₀.10 a₁.10) (f₁₁.2 .id a₀.11 a₁.11)
      (sym f₁₂.2 .id.1 a₀.12 a₁.12) (sym A₂₀.2 a₀.20 a₁.20)
      (sym A₂₁.2 a₀.21 a₁.21) (sym f₂₀.2 .id.1 a₀.20 a₁.20)
      (sym f.2 .id.1 a₀.20 a₁.20) (sym f₂₁.2 .id.1 a₀.21 a₁.21)
      (A₂₂.2⁽³¹²⁾ a₀.22 a₁.22) (f₂₂.2⁽³¹²⁾ .id.1 a₀.22 a₁.22)
| .id.1 ⤇ a₀ a₁ ⤇
    fibProp_l (A₂₀ a₀.0 a₁.0) (A₂₁ a₀.1 a₁.1) (A₂₂ a₀.2 a₁.2)
      (f₂₀ .id a₀.0 a₁.0) (f .id a₀.0 a₁.0) (f₂₁ .id a₀.1 a₁.1)
      (f₂₂ .id.1 a₀.2 a₁.2)
| .id.2 ⤇ f₂₂ .id.2]

def fibProp_rr (A₀₀ A₀₁ : Type) (A₀₂ : Type⁽ᵖ⁾ A₀₀ A₀₁) (A₁₀ A₁₁ : Type)
  (A₁₂ : Type⁽ᵖ⁾ A₁₀ A₁₁) (f₀₀ : isFibrant A₀₀) (f₀₁ : isFibrant A₀₁)
  (f₀₂ : isFibrant⁽ᵖ⁾ A₀₂ f₀₀ f₀₁) (f₁₀ : isFibrant A₁₀)
  (f₁₁ : isFibrant A₁₁) (f₁₂ : isFibrant⁽ᵖ⁾ A₁₂ f₁₀ f₁₁)
  (A₂₀ : Type⁽ᵖ⁾ A₀₀ A₁₀) (A₂₁ : Type⁽ᵖ⁾ A₀₁ A₁₁)
  (f₂₀ : isFibrant⁽ᵖ⁾ A₂₀ f₀₀ f₁₀) (f f₂₁ : isFibrant⁽ᵖ⁾ A₂₁ f₀₁ f₁₁)
  (A₂₂ : Type⁽ᵖᵖ⁾ A₀₂ A₁₂ A₂₀ A₂₁)
  (f₂₂ : isFibrant⁽ᵖᵖ⁾ A₂₂ f₀₂ f₁₂ f₂₀ f₂₁)
  : isFibrant⁽ᵖᵖ⁾ A₂₂ f₀₂ f₁₂ f₂₀ f
  ≔ [
| .trr.p ⤇ a ⤇
    f₂₂.2
      .id.1 (sym (f₀₂.2 .liftr.2 a.02)) (sym (f₁₂.2 .liftr.2 a.12))
      .id.1 (sym (f₂₀.2 .liftr.2 a.20)) (sym (f.2 .liftr.2 a.21))
      .trr a.22
| .trr.1 ⤇ a ⤇ f₂₂ .id.2 (f₂₀ .liftr a.0) (f .liftr a.1) .trr a.2
| .trr.2 ⤇ f₂₂ .trr.2
| .trl.p ⤇ a ⤇
    f₂₂.2
      .id.1 (sym (f₀₂.2 .liftl.2 a.02)) (sym (f₁₂.2 .liftl.2 a.12))
      .id.1 (sym (f₂₀.2 .liftl.2 a.20)) (sym (f.2 .liftl.2 a.21))
      .trl a.22
| .trl.1 ⤇ a ⤇ f₂₂ .id.2 (f₂₀ .liftl a.0) (f .liftl a.1) .trl a.2
| .trl.2 ⤇ f₂₂ .trl.2
| .liftr.p ⤇ a ⤇
    (f₂₂.2
     .id.1 (sym (f₀₂.2 .liftr.2 a.02)) (sym (f₁₂.2 .liftr.2 a.12))
     .id.1 (sym (f₂₀.2 .liftr.2 a.20)) (sym (f.2 .liftr.2 a.21))
     .liftr a.22)⁽³¹²⁾
| .liftr.1 ⤇ a ⤇ sym (f₂₂ .id.2 (f₂₀ .liftr a.0) (f .liftr a.1) .liftr a.2)
| .liftr.2 ⤇ f₂₂ .liftr.2
| .liftl.p ⤇ a ⤇
    (f₂₂.2
     .id.1 (sym (f₀₂.2 .liftl.2 a.02)) (sym (f₁₂.2 .liftl.2 a.12))
     .id.1 (sym (f₂₀.2 .liftl.2 a.20)) (sym (f.2 .liftl.2 a.21))
     .liftl a.22)⁽³¹²⁾
| .liftl.1 ⤇ a ⤇ sym (f₂₂ .id.2 (f₂₀ .liftl a.0) (f .liftl a.1) .liftl a.2)
| .liftl.2 ⤇ f₂₂ .liftl.2
| .id.p ⤇ a₀ a₁ ⤇
    fibProp_rr (A₀₀.2 a₀.00 a₁.00) (A₀₁.2 a₀.01 a₁.01)
      (sym A₀₂.2 a₀.02 a₁.02) (A₁₀.2 a₀.10 a₁.10) (A₁₁.2 a₀.11 a₁.11)
      (sym A₁₂.2 a₀.12 a₁.12) (f₀₀.2 .id a₀.00 a₁.00)
      (f₀₁.2 .id a₀.01 a₁.01) (sym f₀₂.2 .id.1 a₀.02 a₁.02)
      (f₁₀.2 .id a₀.10 a₁.10) (f₁₁.2 .id a₀.11 a₁.11)
      (sym f₁₂.2 .id.1 a₀.12 a₁.12) (sym A₂₀.2 a₀.20 a₁.20)
      (sym A₂₁.2 a₀.21 a₁.21) (sym f₂₀.2 .id.1 a₀.20 a₁.20)
      (sym f.2 .id.1 a₀.21 a₁.21) (sym f₂₁.2 .id.1 a₀.21 a₁.21)
      (A₂₂.2⁽³¹²⁾ a₀.22 a₁.22) (f₂₂.2⁽³¹²⁾ .id.1 a₀.22 a₁.22)
| .id.1 ⤇ a₀ a₁ ⤇
    fibProp_r (A₂₀ a₀.0 a₁.0) (A₂₁ a₀.1 a₁.1) (A₂₂ a₀.2 a₁.2)
      (f₂₀ .id a₀.0 a₁.0) (f .id a₀.1 a₁.1) (f₂₁ .id a₀.1 a₁.1)
      (f₂₂ .id.1 a₀.2 a₁.2)
| .id.2 ⤇ f₂₂ .id.2]

` Asked Claude to do _lll (and _rrr) below
`-------------------
def fibProp_lll (A₀₀₀ A₀₀₁ A₀₁₀ A₀₁₁ A₁₀₀ A₁₀₁ A₁₁₀ A₁₁₁ : Type)
  (f₀₀₀ : isFibrant A₀₀₀) (f₀₀₁ : isFibrant A₀₀₁) (f₀₁₀ : isFibrant A₀₁₀)
  (f₀₁₁ : isFibrant A₀₁₁) (f₁₀₀ : isFibrant A₁₀₀) (f₁₀₁ : isFibrant A₁₀₁)
  (f₁₁₀ : isFibrant A₁₁₀) (f₁₁₁ : isFibrant A₁₁₁)
  (A₀₀₂ : Type⁽ᵖ⁾ A₀₀₀ A₀₀₁) (A₀₁₂ : Type⁽ᵖ⁾ A₀₁₀ A₀₁₁)
  (A₀₂₀ : Type⁽ᵖ⁾ A₀₀₀ A₀₁₀) (A₀₂₁ : Type⁽ᵖ⁾ A₀₀₁ A₀₁₁)
  (A₁₀₂ : Type⁽ᵖ⁾ A₁₀₀ A₁₀₁) (A₁₁₂ : Type⁽ᵖ⁾ A₁₁₀ A₁₁₁)
  (A₁₂₀ : Type⁽ᵖ⁾ A₁₀₀ A₁₁₀) (A₁₂₁ : Type⁽ᵖ⁾ A₁₀₁ A₁₁₁)
  (A₂₀₀ : Type⁽ᵖ⁾ A₀₀₀ A₁₀₀) (A₂₀₁ : Type⁽ᵖ⁾ A₀₀₁ A₁₀₁)
  (A₂₁₀ : Type⁽ᵖ⁾ A₀₁₀ A₁₁₀) (A₂₁₁ : Type⁽ᵖ⁾ A₀₁₁ A₁₁₁)
  (f₀₀₂ : isFibrant⁽ᵖ⁾ A₀₀₂ f₀₀₀ f₀₀₁) (f₀₁₂ : isFibrant⁽ᵖ⁾ A₀₁₂ f₀₁₀ f₀₁₁)
  (f₀₂₀ : isFibrant⁽ᵖ⁾ A₀₂₀ f₀₀₀ f₀₁₀) (f₀₂₁ : isFibrant⁽ᵖ⁾ A₀₂₁ f₀₀₁ f₀₁₁)
  (f₁₀₂ : isFibrant⁽ᵖ⁾ A₁₀₂ f₁₀₀ f₁₀₁) (f₁₁₂ : isFibrant⁽ᵖ⁾ A₁₁₂ f₁₁₀ f₁₁₁)
  (f₁₂₀ : isFibrant⁽ᵖ⁾ A₁₂₀ f₁₀₀ f₁₁₀) (f₁₂₁ : isFibrant⁽ᵖ⁾ A₁₂₁ f₁₀₁ f₁₁₁)
  (f₂₀₀ : isFibrant⁽ᵖ⁾ A₂₀₀ f₀₀₀ f₁₀₀) (f₂₀₁ : isFibrant⁽ᵖ⁾ A₂₀₁ f₀₀₁ f₁₀₁)
  (f₂₁₀ : isFibrant⁽ᵖ⁾ A₂₁₀ f₀₁₀ f₁₁₀) (f₂₁₁ : isFibrant⁽ᵖ⁾ A₂₁₁ f₀₁₁ f₁₁₁)
  (A₀₂₂ : Type⁽ᵖᵖ⁾ A₀₀₂ A₀₁₂ A₀₂₀ A₀₂₁)
  (A₁₂₂ : Type⁽ᵖᵖ⁾ A₁₀₂ A₁₁₂ A₁₂₀ A₁₂₁)
  (A₂₀₂ : Type⁽ᵖᵖ⁾ A₀₀₂ A₁₀₂ A₂₀₀ A₂₀₁)
  (A₂₁₂ : Type⁽ᵖᵖ⁾ A₀₁₂ A₁₁₂ A₂₁₀ A₂₁₁)
  (A₂₂₀ : Type⁽ᵖᵖ⁾ A₀₂₀ A₁₂₀ A₂₀₀ A₂₁₀)
  (A₂₂₁ : Type⁽ᵖᵖ⁾ A₀₂₁ A₁₂₁ A₂₀₁ A₂₁₁)
  (f₀₂₂ : isFibrant⁽ᵖᵖ⁾ A₀₂₂ f₀₀₂ f₀₁₂ f₀₂₀ f₀₂₁)
  (f₁₂₂ : isFibrant⁽ᵖᵖ⁾ A₁₂₂ f₁₀₂ f₁₁₂ f₁₂₀ f₁₂₁)
  (f₂₀₂ : isFibrant⁽ᵖᵖ⁾ A₂₀₂ f₀₀₂ f₁₀₂ f₂₀₀ f₂₀₁)
  (f₂₁₂ : isFibrant⁽ᵖᵖ⁾ A₂₁₂ f₀₁₂ f₁₁₂ f₂₁₀ f₂₁₁)
  (f₂₂₀ f : isFibrant⁽ᵖᵖ⁾ A₂₂₀ f₀₂₀ f₁₂₀ f₂₀₀ f₂₁₀)
  (f₂₂₁ : isFibrant⁽ᵖᵖ⁾ A₂₂₁ f₀₂₁ f₁₂₁ f₂₀₁ f₂₁₁)
  (A₂₂₂ : Type⁽ᵖᵖᵖ⁾ A₀₂₂ A₁₂₂ A₂₀₂ A₂₁₂ A₂₂₀ A₂₂₁)
  (f₂₂₂ : isFibrant⁽ᵖᵖᵖ⁾ A₂₂₂ f₀₂₂ f₁₂₂ f₂₀₂ f₂₁₂ f₂₂₀ f₂₂₁)
  : isFibrant⁽ᵖᵖᵖ⁾ A₂₂₂ f₀₂₂ f₁₂₂ f₂₀₂ f₂₁₂ f f₂₂₁
  ≔ [
| .trr.p ⤇ a ⤇
    f₂₂₂.2
      .id.1 ((f₀₂₂.2 .liftr.3 a.022)⁽²³¹⁾) ((f₁₂₂.2 .liftr.3 a.122)⁽²³¹⁾)
      .id.1 ((f₂₀₂.2 .liftr.3 a.202)⁽²³¹⁾) ((f₂₁₂.2 .liftr.3 a.212)⁽²³¹⁾)
      .id.1 ((f.2 .liftr.3 a.220)⁽²³¹⁾) ((f₂₂₁.2 .liftr.3 a.221)⁽²³¹⁾)
      .trr a.222
| .trr.1 ⤇ a ⤇
    f₂₂₂
      .id.2 (f₂₀₂ .liftr.1 a.02) (f₂₁₂ .liftr.1 a.12)
      .id.2 (sym (f .liftr.1 a.20)) (sym (f₂₂₁ .liftr.1 a.21))
      .trr a.22
| .trr.2 ⤇ a ⤇
    f₂₂₂
      .id.1 (f₀₂₂ .liftr.1 a.02) (f₁₂₂ .liftr.1 a.12)
      .id.2 (sym (f .liftr.2 a.20)) (sym (f₂₂₁ .liftr.2 a.21))
      .trr a.22
| .trr.3 ⤇ f₂₂₂ .trr.3
| .trl.p ⤇ a ⤇
    f₂₂₂.2
      .id.1 ((f₀₂₂.2 .liftl.3 a.022)⁽²³¹⁾) ((f₁₂₂.2 .liftl.3 a.122)⁽²³¹⁾)
      .id.1 ((f₂₀₂.2 .liftl.3 a.202)⁽²³¹⁾) ((f₂₁₂.2 .liftl.3 a.212)⁽²³¹⁾)
      .id.1 ((f.2 .liftl.3 a.220)⁽²³¹⁾) ((f₂₂₁.2 .liftl.3 a.221)⁽²³¹⁾)
      .trl a.222
| .trl.1 ⤇ a ⤇
    f₂₂₂
      .id.2 (f₂₀₂ .liftl.1 a.02) (f₂₁₂ .liftl.1 a.12)
      .id.2 (sym (f .liftl.1 a.20)) (sym (f₂₂₁ .liftl.1 a.21))
      .trl a.22
| .trl.2 ⤇ a ⤇
    f₂₂₂
      .id.1 (f₀₂₂ .liftl.1 a.02) (f₁₂₂ .liftl.1 a.12)
      .id.2 (sym (f .liftl.2 a.20)) (sym (f₂₂₁ .liftl.2 a.21))
      .trl a.22
| .trl.3 ⤇ f₂₂₂ .trl.3
| .liftr.p ⤇ a ⤇
    (f₂₂₂.2
     .id.1 ((f₀₂₂.2 .liftr.3 a.022)⁽²³¹⁾) ((f₁₂₂.2 .liftr.3 a.122)⁽²³¹⁾)
     .id.1 ((f₂₀₂.2 .liftr.3 a.202)⁽²³¹⁾) ((f₂₁₂.2 .liftr.3 a.212)⁽²³¹⁾)
     .id.1 ((f.2 .liftr.3 a.220)⁽²³¹⁾) ((f₂₂₁.2 .liftr.3 a.221)⁽²³¹⁾)
     .liftr a.222)⁽⁴¹²³⁾
| .liftr.1 ⤇ a ⤇
    (f₂₂₂
     .id.2 (f₂₀₂ .liftr.1 a.02) (f₂₁₂ .liftr.1 a.12)
     .id.2 (sym (f .liftr.1 a.20)) (sym (f₂₂₁ .liftr.1 a.21))
     .liftr a.22)⁽³¹²⁾
| .liftr.2 ⤇ a ⤇
    (f₂₂₂
     .id.1 (f₀₂₂ .liftr.1 a.02) (f₁₂₂ .liftr.1 a.12)
     .id.2 (sym (f .liftr.2 a.20)) (sym (f₂₂₁ .liftr.2 a.21))
     .liftr a.22)⁽³¹²⁾
| .liftr.3 ⤇ f₂₂₂ .liftr.3
| .liftl.p ⤇ a ⤇
    (f₂₂₂.2
     .id.1 ((f₀₂₂.2 .liftl.3 a.022)⁽²³¹⁾) ((f₁₂₂.2 .liftl.3 a.122)⁽²³¹⁾)
     .id.1 ((f₂₀₂.2 .liftl.3 a.202)⁽²³¹⁾) ((f₂₁₂.2 .liftl.3 a.212)⁽²³¹⁾)
     .id.1 ((f.2 .liftl.3 a.220)⁽²³¹⁾) ((f₂₂₁.2 .liftl.3 a.221)⁽²³¹⁾)
     .liftl a.222)⁽⁴¹²³⁾
| .liftl.1 ⤇ a ⤇
    (f₂₂₂
     .id.2 (f₂₀₂ .liftl.1 a.02) (f₂₁₂ .liftl.1 a.12)
     .id.2 (sym (f .liftl.1 a.20)) (sym (f₂₂₁ .liftl.1 a.21))
     .liftl a.22)⁽³¹²⁾
| .liftl.2 ⤇ a ⤇
    (f₂₂₂
     .id.1 (f₀₂₂ .liftl.1 a.02) (f₁₂₂ .liftl.1 a.12)
     .id.2 (sym (f .liftl.2 a.20)) (sym (f₂₂₁ .liftl.2 a.21))
     .liftl a.22)⁽³¹²⁾
| .liftl.3 ⤇ f₂₂₂ .liftl.3
| .id.p ⤇ a₀ a₁ ⤇
    fibProp_lll (A₀₀₀.2 a₀.000 a₁.000) (A₀₀₁.2 a₀.001 a₁.001)
      (A₀₁₀.2 a₀.010 a₁.010) (A₀₁₁.2 a₀.011 a₁.011) (A₁₀₀.2 a₀.100 a₁.100)
      (A₁₀₁.2 a₀.101 a₁.101) (A₁₁₀.2 a₀.110 a₁.110) (A₁₁₁.2 a₀.111 a₁.111)
      (f₀₀₀.2 .id a₀.000 a₁.000) (f₀₀₁.2 .id a₀.001 a₁.001)
      (f₀₁₀.2 .id a₀.010 a₁.010) (f₀₁₁.2 .id a₀.011 a₁.011)
      (f₁₀₀.2 .id a₀.100 a₁.100) (f₁₀₁.2 .id a₀.101 a₁.101)
      (f₁₁₀.2 .id a₀.110 a₁.110) (f₁₁₁.2 .id a₀.111 a₁.111)
      (sym A₀₀₂.2 a₀.002 a₁.002) (sym A₀₁₂.2 a₀.012 a₁.012)
      (sym A₀₂₀.2 a₀.020 a₁.020) (sym A₀₂₁.2 a₀.021 a₁.021)
      (sym A₁₀₂.2 a₀.102 a₁.102) (sym A₁₁₂.2 a₀.112 a₁.112)
      (sym A₁₂₀.2 a₀.120 a₁.120) (sym A₁₂₁.2 a₀.121 a₁.121)
      (sym A₂₀₀.2 a₀.200 a₁.200) (sym A₂₀₁.2 a₀.201 a₁.201)
      (sym A₂₁₀.2 a₀.210 a₁.210) (sym A₂₁₁.2 a₀.211 a₁.211)
      (sym f₀₀₂.2 .id.1 a₀.002 a₁.002) (sym f₀₁₂.2 .id.1 a₀.012 a₁.012)
      (sym f₀₂₀.2 .id.1 a₀.020 a₁.020) (sym f₀₂₁.2 .id.1 a₀.021 a₁.021)
      (sym f₁₀₂.2 .id.1 a₀.102 a₁.102) (sym f₁₁₂.2 .id.1 a₀.112 a₁.112)
      (sym f₁₂₀.2 .id.1 a₀.120 a₁.120) (sym f₁₂₁.2 .id.1 a₀.121 a₁.121)
      (sym f₂₀₀.2 .id.1 a₀.200 a₁.200) (sym f₂₀₁.2 .id.1 a₀.201 a₁.201)
      (sym f₂₁₀.2 .id.1 a₀.210 a₁.210) (sym f₂₁₁.2 .id.1 a₀.211 a₁.211)
      (A₀₂₂.2⁽³¹²⁾ a₀.022 a₁.022) (A₁₂₂.2⁽³¹²⁾ a₀.122 a₁.122)
      (A₂₀₂.2⁽³¹²⁾ a₀.202 a₁.202) (A₂₁₂.2⁽³¹²⁾ a₀.212 a₁.212)
      (A₂₂₀.2⁽³¹²⁾ a₀.220 a₁.220) (A₂₂₁.2⁽³¹²⁾ a₀.221 a₁.221)
      (f₀₂₂.2⁽³¹²⁾ .id.1 a₀.022 a₁.022) (f₁₂₂.2⁽³¹²⁾ .id.1 a₀.122 a₁.122)
      (f₂₀₂.2⁽³¹²⁾ .id.1 a₀.202 a₁.202) (f₂₁₂.2⁽³¹²⁾ .id.1 a₀.212 a₁.212)
      (f₂₂₀.2⁽³¹²⁾ .id.1 a₀.220 a₁.220) (f.2⁽³¹²⁾ .id.1 a₀.220 a₁.220)
      (f₂₂₁.2⁽³¹²⁾ .id.1 a₀.221 a₁.221) (A₂₂₂.2⁽⁴¹²³⁾ a₀.222 a₁.222)
      (f₂₂₂.2⁽⁴¹²³⁾ .id.1 a₀.222 a₁.222)
| .id.1 ⤇ a₀ a₁ ⤇
    fibProp_ll (A₂₀₀ a₀.00 a₁.00) (A₂₀₁ a₀.01 a₁.01) (A₂₀₂ a₀.02 a₁.02)
      (A₂₁₀ a₀.10 a₁.10) (A₂₁₁ a₀.11 a₁.11) (A₂₁₂ a₀.12 a₁.12)
      (f₂₀₀ .id a₀.00 a₁.00) (f₂₀₁ .id a₀.01 a₁.01)
      (f₂₀₂ .id.1 a₀.02 a₁.02) (f₂₁₀ .id a₀.10 a₁.10)
      (f₂₁₁ .id a₀.11 a₁.11) (f₂₁₂ .id.1 a₀.12 a₁.12) (A₂₂₀ a₀.20 a₁.20)
      (A₂₂₁ a₀.21 a₁.21) (f₂₂₀ .id.1 a₀.20 a₁.20) (f .id.1 a₀.20 a₁.20)
      (f₂₂₁ .id.1 a₀.21 a₁.21) (A₂₂₂ a₀.22 a₁.22) (f₂₂₂ .id.1 a₀.22 a₁.22)
| .id.2 ⤇ a₀ a₁ ⤇
    fibProp_ll (A₀₂₀ a₀.00 a₁.00) (A₀₂₁ a₀.01 a₁.01) (A₀₂₂ a₀.02 a₁.02)
      (A₁₂₀ a₀.10 a₁.10) (A₁₂₁ a₀.11 a₁.11) (A₁₂₂ a₀.12 a₁.12)
      (f₀₂₀ .id a₀.00 a₁.00) (f₀₂₁ .id a₀.01 a₁.01)
      (f₀₂₂ .id.1 a₀.02 a₁.02) (f₁₂₀ .id a₀.10 a₁.10)
      (f₁₂₁ .id a₀.11 a₁.11) (f₁₂₂ .id.1 a₀.12 a₁.12)
      (sym A₂₂₀ a₀.20 a₁.20) (sym A₂₂₁ a₀.21 a₁.21)
      (sym f₂₂₀ .id.1 a₀.20 a₁.20) (sym f .id.1 a₀.20 a₁.20)
      (sym f₂₂₁ .id.1 a₀.21 a₁.21) (A₂₂₂⁽²¹³⁾ a₀.22 a₁.22)
      (f₂₂₂⁽²¹³⁾ .id.1 a₀.22 a₁.22)
| .id.3 ⤇ f₂₂₂ .id.3]

def fibProp_rrr (A₀₀₀ A₀₀₁ A₀₁₀ A₀₁₁ A₁₀₀ A₁₀₁ A₁₁₀ A₁₁₁ : Type)
  (f₀₀₀ : isFibrant A₀₀₀) (f₀₀₁ : isFibrant A₀₀₁) (f₀₁₀ : isFibrant A₀₁₀)
  (f₀₁₁ : isFibrant A₀₁₁) (f₁₀₀ : isFibrant A₁₀₀) (f₁₀₁ : isFibrant A₁₀₁)
  (f₁₁₀ : isFibrant A₁₁₀) (f₁₁₁ : isFibrant A₁₁₁)
  (A₀₀₂ : Type⁽ᵖ⁾ A₀₀₀ A₀₀₁) (A₀₁₂ : Type⁽ᵖ⁾ A₀₁₀ A₀₁₁)
  (A₀₂₀ : Type⁽ᵖ⁾ A₀₀₀ A₀₁₀) (A₀₂₁ : Type⁽ᵖ⁾ A₀₀₁ A₀₁₁)
  (A₁₀₂ : Type⁽ᵖ⁾ A₁₀₀ A₁₀₁) (A₁₁₂ : Type⁽ᵖ⁾ A₁₁₀ A₁₁₁)
  (A₁₂₀ : Type⁽ᵖ⁾ A₁₀₀ A₁₁₀) (A₁₂₁ : Type⁽ᵖ⁾ A₁₀₁ A₁₁₁)
  (A₂₀₀ : Type⁽ᵖ⁾ A₀₀₀ A₁₀₀) (A₂₀₁ : Type⁽ᵖ⁾ A₀₀₁ A₁₀₁)
  (A₂₁₀ : Type⁽ᵖ⁾ A₀₁₀ A₁₁₀) (A₂₁₁ : Type⁽ᵖ⁾ A₀₁₁ A₁₁₁)
  (f₀₀₂ : isFibrant⁽ᵖ⁾ A₀₀₂ f₀₀₀ f₀₀₁) (f₀₁₂ : isFibrant⁽ᵖ⁾ A₀₁₂ f₀₁₀ f₀₁₁)
  (f₀₂₀ : isFibrant⁽ᵖ⁾ A₀₂₀ f₀₀₀ f₀₁₀) (f₀₂₁ : isFibrant⁽ᵖ⁾ A₀₂₁ f₀₀₁ f₀₁₁)
  (f₁₀₂ : isFibrant⁽ᵖ⁾ A₁₀₂ f₁₀₀ f₁₀₁) (f₁₁₂ : isFibrant⁽ᵖ⁾ A₁₁₂ f₁₁₀ f₁₁₁)
  (f₁₂₀ : isFibrant⁽ᵖ⁾ A₁₂₀ f₁₀₀ f₁₁₀) (f₁₂₁ : isFibrant⁽ᵖ⁾ A₁₂₁ f₁₀₁ f₁₁₁)
  (f₂₀₀ : isFibrant⁽ᵖ⁾ A₂₀₀ f₀₀₀ f₁₀₀) (f₂₀₁ : isFibrant⁽ᵖ⁾ A₂₀₁ f₀₀₁ f₁₀₁)
  (f₂₁₀ : isFibrant⁽ᵖ⁾ A₂₁₀ f₀₁₀ f₁₁₀) (f₂₁₁ : isFibrant⁽ᵖ⁾ A₂₁₁ f₀₁₁ f₁₁₁)
  (A₀₂₂ : Type⁽ᵖᵖ⁾ A₀₀₂ A₀₁₂ A₀₂₀ A₀₂₁)
  (A₁₂₂ : Type⁽ᵖᵖ⁾ A₁₀₂ A₁₁₂ A₁₂₀ A₁₂₁)
  (A₂₀₂ : Type⁽ᵖᵖ⁾ A₀₀₂ A₁₀₂ A₂₀₀ A₂₀₁)
  (A₂₁₂ : Type⁽ᵖᵖ⁾ A₀₁₂ A₁₁₂ A₂₁₀ A₂₁₁)
  (A₂₂₀ : Type⁽ᵖᵖ⁾ A₀₂₀ A₁₂₀ A₂₀₀ A₂₁₀)
  (A₂₂₁ : Type⁽ᵖᵖ⁾ A₀₂₁ A₁₂₁ A₂₀₁ A₂₁₁)
  (f₀₂₂ : isFibrant⁽ᵖᵖ⁾ A₀₂₂ f₀₀₂ f₀₁₂ f₀₂₀ f₀₂₁)
  (f₁₂₂ : isFibrant⁽ᵖᵖ⁾ A₁₂₂ f₁₀₂ f₁₁₂ f₁₂₀ f₁₂₁)
  (f₂₀₂ : isFibrant⁽ᵖᵖ⁾ A₂₀₂ f₀₀₂ f₁₀₂ f₂₀₀ f₂₀₁)
  (f₂₁₂ : isFibrant⁽ᵖᵖ⁾ A₂₁₂ f₀₁₂ f₁₁₂ f₂₁₀ f₂₁₁)
  (f₂₂₀ : isFibrant⁽ᵖᵖ⁾ A₂₂₀ f₀₂₀ f₁₂₀ f₂₀₀ f₂₁₀)
  (f f₂₂₁ : isFibrant⁽ᵖᵖ⁾ A₂₂₁ f₀₂₁ f₁₂₁ f₂₀₁ f₂₁₁)
  (A₂₂₂ : Type⁽ᵖᵖᵖ⁾ A₀₂₂ A₁₂₂ A₂₀₂ A₂₁₂ A₂₂₀ A₂₂₁)
  (f₂₂₂ : isFibrant⁽ᵖᵖᵖ⁾ A₂₂₂ f₀₂₂ f₁₂₂ f₂₀₂ f₂₁₂ f₂₂₀ f₂₂₁)
  : isFibrant⁽ᵖᵖᵖ⁾ A₂₂₂ f₀₂₂ f₁₂₂ f₂₀₂ f₂₁₂ f₂₂₀ f
  ≔ [
| .trr.p ⤇ a ⤇
    f₂₂₂.2
      .id.1 ((f₀₂₂.2 .liftr.3 a.022)⁽²³¹⁾) ((f₁₂₂.2 .liftr.3 a.122)⁽²³¹⁾)
      .id.1 ((f₂₀₂.2 .liftr.3 a.202)⁽²³¹⁾) ((f₂₁₂.2 .liftr.3 a.212)⁽²³¹⁾)
      .id.1 ((f₂₂₀.2 .liftr.3 a.220)⁽²³¹⁾) ((f.2 .liftr.3 a.221)⁽²³¹⁾)
      .trr a.222
| .trr.1 ⤇ a ⤇
    f₂₂₂
      .id.2 (f₂₀₂ .liftr.1 a.02) (f₂₁₂ .liftr.1 a.12)
      .id.2 (sym (f₂₂₀ .liftr.1 a.20)) (sym (f .liftr.1 a.21))
      .trr a.22
| .trr.2 ⤇ a ⤇
    f₂₂₂
      .id.1 (f₀₂₂ .liftr.1 a.02) (f₁₂₂ .liftr.1 a.12)
      .id.2 (sym (f₂₂₀ .liftr.2 a.20)) (sym (f .liftr.2 a.21))
      .trr a.22
| .trr.3 ⤇ f₂₂₂ .trr.3
| .trl.p ⤇ a ⤇
    f₂₂₂.2
      .id.1 ((f₀₂₂.2 .liftl.3 a.022)⁽²³¹⁾) ((f₁₂₂.2 .liftl.3 a.122)⁽²³¹⁾)
      .id.1 ((f₂₀₂.2 .liftl.3 a.202)⁽²³¹⁾) ((f₂₁₂.2 .liftl.3 a.212)⁽²³¹⁾)
      .id.1 ((f₂₂₀.2 .liftl.3 a.220)⁽²³¹⁾) ((f.2 .liftl.3 a.221)⁽²³¹⁾)
      .trl a.222
| .trl.1 ⤇ a ⤇
    f₂₂₂
      .id.2 (f₂₀₂ .liftl.1 a.02) (f₂₁₂ .liftl.1 a.12)
      .id.2 (sym (f₂₂₀ .liftl.1 a.20)) (sym (f .liftl.1 a.21))
      .trl a.22
| .trl.2 ⤇ a ⤇
    f₂₂₂
      .id.1 (f₀₂₂ .liftl.1 a.02) (f₁₂₂ .liftl.1 a.12)
      .id.2 (sym (f₂₂₀ .liftl.2 a.20)) (sym (f .liftl.2 a.21))
      .trl a.22
| .trl.3 ⤇ f₂₂₂ .trl.3
| .liftr.p ⤇ a ⤇
    (f₂₂₂.2
     .id.1 ((f₀₂₂.2 .liftr.3 a.022)⁽²³¹⁾) ((f₁₂₂.2 .liftr.3 a.122)⁽²³¹⁾)
     .id.1 ((f₂₀₂.2 .liftr.3 a.202)⁽²³¹⁾) ((f₂₁₂.2 .liftr.3 a.212)⁽²³¹⁾)
     .id.1 ((f₂₂₀.2 .liftr.3 a.220)⁽²³¹⁾) ((f.2 .liftr.3 a.221)⁽²³¹⁾)
     .liftr a.222)⁽⁴¹²³⁾
| .liftr.1 ⤇ a ⤇
    (f₂₂₂
     .id.2 (f₂₀₂ .liftr.1 a.02) (f₂₁₂ .liftr.1 a.12)
     .id.2 (sym (f₂₂₀ .liftr.1 a.20)) (sym (f .liftr.1 a.21))
     .liftr a.22)⁽³¹²⁾
| .liftr.2 ⤇ a ⤇
    (f₂₂₂
     .id.1 (f₀₂₂ .liftr.1 a.02) (f₁₂₂ .liftr.1 a.12)
     .id.2 (sym (f₂₂₀ .liftr.2 a.20)) (sym (f .liftr.2 a.21))
     .liftr a.22)⁽³¹²⁾
| .liftr.3 ⤇ f₂₂₂ .liftr.3
| .liftl.p ⤇ a ⤇
    (f₂₂₂.2
     .id.1 ((f₀₂₂.2 .liftl.3 a.022)⁽²³¹⁾) ((f₁₂₂.2 .liftl.3 a.122)⁽²³¹⁾)
     .id.1 ((f₂₀₂.2 .liftl.3 a.202)⁽²³¹⁾) ((f₂₁₂.2 .liftl.3 a.212)⁽²³¹⁾)
     .id.1 ((f₂₂₀.2 .liftl.3 a.220)⁽²³¹⁾) ((f.2 .liftl.3 a.221)⁽²³¹⁾)
     .liftl a.222)⁽⁴¹²³⁾
| .liftl.1 ⤇ a ⤇
    (f₂₂₂
     .id.2 (f₂₀₂ .liftl.1 a.02) (f₂₁₂ .liftl.1 a.12)
     .id.2 (sym (f₂₂₀ .liftl.1 a.20)) (sym (f .liftl.1 a.21))
     .liftl a.22)⁽³¹²⁾
| .liftl.2 ⤇ a ⤇
    (f₂₂₂
     .id.1 (f₀₂₂ .liftl.1 a.02) (f₁₂₂ .liftl.1 a.12)
     .id.2 (sym (f₂₂₀ .liftl.2 a.20)) (sym (f .liftl.2 a.21))
     .liftl a.22)⁽³¹²⁾
| .liftl.3 ⤇ f₂₂₂ .liftl.3
| .id.p ⤇ a₀ a₁ ⤇
    fibProp_rrr (A₀₀₀.2 a₀.000 a₁.000) (A₀₀₁.2 a₀.001 a₁.001)
      (A₀₁₀.2 a₀.010 a₁.010) (A₀₁₁.2 a₀.011 a₁.011) (A₁₀₀.2 a₀.100 a₁.100)
      (A₁₀₁.2 a₀.101 a₁.101) (A₁₁₀.2 a₀.110 a₁.110) (A₁₁₁.2 a₀.111 a₁.111)
      (f₀₀₀.2 .id a₀.000 a₁.000) (f₀₀₁.2 .id a₀.001 a₁.001)
      (f₀₁₀.2 .id a₀.010 a₁.010) (f₀₁₁.2 .id a₀.011 a₁.011)
      (f₁₀₀.2 .id a₀.100 a₁.100) (f₁₀₁.2 .id a₀.101 a₁.101)
      (f₁₁₀.2 .id a₀.110 a₁.110) (f₁₁₁.2 .id a₀.111 a₁.111)
      (sym A₀₀₂.2 a₀.002 a₁.002) (sym A₀₁₂.2 a₀.012 a₁.012)
      (sym A₀₂₀.2 a₀.020 a₁.020) (sym A₀₂₁.2 a₀.021 a₁.021)
      (sym A₁₀₂.2 a₀.102 a₁.102) (sym A₁₁₂.2 a₀.112 a₁.112)
      (sym A₁₂₀.2 a₀.120 a₁.120) (sym A₁₂₁.2 a₀.121 a₁.121)
      (sym A₂₀₀.2 a₀.200 a₁.200) (sym A₂₀₁.2 a₀.201 a₁.201)
      (sym A₂₁₀.2 a₀.210 a₁.210) (sym A₂₁₁.2 a₀.211 a₁.211)
      (sym f₀₀₂.2 .id.1 a₀.002 a₁.002) (sym f₀₁₂.2 .id.1 a₀.012 a₁.012)
      (sym f₀₂₀.2 .id.1 a₀.020 a₁.020) (sym f₀₂₁.2 .id.1 a₀.021 a₁.021)
      (sym f₁₀₂.2 .id.1 a₀.102 a₁.102) (sym f₁₁₂.2 .id.1 a₀.112 a₁.112)
      (sym f₁₂₀.2 .id.1 a₀.120 a₁.120) (sym f₁₂₁.2 .id.1 a₀.121 a₁.121)
      (sym f₂₀₀.2 .id.1 a₀.200 a₁.200) (sym f₂₀₁.2 .id.1 a₀.201 a₁.201)
      (sym f₂₁₀.2 .id.1 a₀.210 a₁.210) (sym f₂₁₁.2 .id.1 a₀.211 a₁.211)
      (A₀₂₂.2⁽³¹²⁾ a₀.022 a₁.022) (A₁₂₂.2⁽³¹²⁾ a₀.122 a₁.122)
      (A₂₀₂.2⁽³¹²⁾ a₀.202 a₁.202) (A₂₁₂.2⁽³¹²⁾ a₀.212 a₁.212)
      (A₂₂₀.2⁽³¹²⁾ a₀.220 a₁.220) (A₂₂₁.2⁽³¹²⁾ a₀.221 a₁.221)
      (f₀₂₂.2⁽³¹²⁾ .id.1 a₀.022 a₁.022) (f₁₂₂.2⁽³¹²⁾ .id.1 a₀.122 a₁.122)
      (f₂₀₂.2⁽³¹²⁾ .id.1 a₀.202 a₁.202) (f₂₁₂.2⁽³¹²⁾ .id.1 a₀.212 a₁.212)
      (f₂₂₀.2⁽³¹²⁾ .id.1 a₀.220 a₁.220) (f.2⁽³¹²⁾ .id.1 a₀.221 a₁.221)
      (f₂₂₁.2⁽³¹²⁾ .id.1 a₀.221 a₁.221) (A₂₂₂.2⁽⁴¹²³⁾ a₀.222 a₁.222)
      (f₂₂₂.2⁽⁴¹²³⁾ .id.1 a₀.222 a₁.222)
| .id.1 ⤇ a₀ a₁ ⤇
    fibProp_rr (A₂₀₀ a₀.00 a₁.00) (A₂₀₁ a₀.01 a₁.01) (A₂₀₂ a₀.02 a₁.02)
      (A₂₁₀ a₀.10 a₁.10) (A₂₁₁ a₀.11 a₁.11) (A₂₁₂ a₀.12 a₁.12)
      (f₂₀₀ .id a₀.00 a₁.00) (f₂₀₁ .id a₀.01 a₁.01)
      (f₂₀₂ .id.1 a₀.02 a₁.02) (f₂₁₀ .id a₀.10 a₁.10)
      (f₂₁₁ .id a₀.11 a₁.11) (f₂₁₂ .id.1 a₀.12 a₁.12) (A₂₂₀ a₀.20 a₁.20)
      (A₂₂₁ a₀.21 a₁.21) (f₂₂₀ .id.1 a₀.20 a₁.20) (f .id.1 a₀.21 a₁.21)
      (f₂₂₁ .id.1 a₀.21 a₁.21) (A₂₂₂ a₀.22 a₁.22) (f₂₂₂ .id.1 a₀.22 a₁.22)
| .id.2 ⤇ a₀ a₁ ⤇
    fibProp_rr (A₀₂₀ a₀.00 a₁.00) (A₀₂₁ a₀.01 a₁.01) (A₀₂₂ a₀.02 a₁.02)
      (A₁₂₀ a₀.10 a₁.10) (A₁₂₁ a₀.11 a₁.11) (A₁₂₂ a₀.12 a₁.12)
      (f₀₂₀ .id a₀.00 a₁.00) (f₀₂₁ .id a₀.01 a₁.01)
      (f₀₂₂ .id.1 a₀.02 a₁.02) (f₁₂₀ .id a₀.10 a₁.10)
      (f₁₂₁ .id a₀.11 a₁.11) (f₁₂₂ .id.1 a₀.12 a₁.12)
      (sym A₂₂₀ a₀.20 a₁.20) (sym A₂₂₁ a₀.21 a₁.21)
      (sym f₂₂₀ .id.1 a₀.20 a₁.20) (sym f .id.1 a₀.21 a₁.21)
      (sym f₂₂₁ .id.1 a₀.21 a₁.21) (A₂₂₂⁽²¹³⁾ a₀.22 a₁.22)
      (f₂₂₂⁽²¹³⁾ .id.1 a₀.22 a₁.22)
| .id.3 ⤇ f₂₂₂ .id.3]

`-------------------


`Claude also filled in the last id.p comatch
def fib_hProp_lemma : Br_hPropᵈ Type isFibrant ≔ [
| .relate_l.p ↦ A₀ A₁ f₀ f f₁ A₂ f₂ ↦ fibProp_l A₀ A₁ A₂ f₀ f f₁ f₂
| .relate_r.p ↦ A₀ A₁ f₀ f f₁ A₂ f₂ ↦ fibProp_r A₀ A₁ A₂ f₀ f f₁ f₂
| .id.p ↦ A₀ A₁ f₀ f₁ ↦ [
  | .relate_l.p ↦ A₂₀ A₂₁ f₂₀ f f₂₁ A₂₂ f₂₂ ↦
      fibProp_ll A₀.0 A₀.1 A₀.2 A₁.0 A₁.1 A₁.2 f₀.0 f₀.1 f₀.2 f₁.0 f₁.1
        f₁.2 A₂₀ A₂₁ f₂₀ f f₂₁ A₂₂ f₂₂
  | .relate_r.p ↦ A₂₀ A₂₁ f₂₀ f f₂₁ A₂₂ f₂₂ ↦
      fibProp_rr A₀.0 A₀.1 A₀.2 A₁.0 A₁.1 A₁.2 f₀.0 f₀.1 f₀.2 f₁.0 f₁.1
        f₁.2 A₂₀ A₂₁ f₂₀ f f₂₁ A₂₂ f₂₂
  | .id.p ↦ A₂₀ A₂₁ f₂₀ f₂₁ ↦ [
    | .relate_l.p ↦ A₃₀ A₃₁ f₃₀ f f₃₁ A₃₂ f₃₂ ↦
        fibProp_lll A₀.00 A₀.01 A₀.10 A₀.11 A₁.00 A₁.01 A₁.10 A₁.11 f₀.00
          f₀.01 f₀.10 f₀.11 f₁.00 f₁.01 f₁.10 f₁.11 A₀.02 A₀.12 A₀.20 A₀.21
          A₁.02 A₁.12 A₁.20 A₁.21 A₂₀.0 A₂₀.1 A₂₁.0 A₂₁.1 f₀.02 f₀.12 f₀.20
          f₀.21 f₁.02 f₁.12 f₁.20 f₁.21 f₂₀.0 f₂₀.1 f₂₁.0 f₂₁.1 A₀.22 A₁.22
          A₂₀.2 A₂₁.2 A₃₀ A₃₁ f₀.22 f₁.22 f₂₀.2 f₂₁.2 f₃₀ f f₃₁ A₃₂ f₃₂
    | .relate_r.p ↦ A₃₀ A₃₁ f₃₀ f f₃₁ A₃₂ f₃₂ ↦
        fibProp_rrr A₀.00 A₀.01 A₀.10 A₀.11 A₁.00 A₁.01 A₁.10 A₁.11 f₀.00
          f₀.01 f₀.10 f₀.11 f₁.00 f₁.01 f₁.10 f₁.11 A₀.02 A₀.12 A₀.20 A₀.21
          A₁.02 A₁.12 A₁.20 A₁.21 A₂₀.0 A₂₀.1 A₂₁.0 A₂₁.1 f₀.02 f₀.12 f₀.20
          f₀.21 f₁.02 f₁.12 f₁.20 f₁.21 f₂₀.0 f₂₀.1 f₂₁.0 f₂₁.1 A₀.22 A₁.22
          A₂₀.2 A₂₁.2 A₃₀ A₃₁ f₀.22 f₁.22 f₂₀.2 f₂₁.2 f₃₀ f f₃₁ A₃₂ f₃₂
    | .id.p ↦ ¿ʔ]]]





` Misc ideas -- not yet finished
`-------------
def fib_Pi (A₀ A₁ : Type) (A₂ : A₀ → A₁ → Type) (f₀ : isFibrant A₀)
  (f₁ : isFibrant A₁) (f₂ : (a₀ : A₀) → (a₁ : A₁) → isFibrant (A₂ a₀ a₁))
  : isFibrant ((a₀ : A₀) → (a₁ : A₁) → A₂ a₀ a₁)
  ≔ ¿ʔ 

def fib_hProp_lemma (A : Type) (El : A → Type) (P : A → Type)
  (f : (a : A) → P a → isFibrant (El a))
  (p : (a : A) → isFibrant (El a) → P a)
  : Br_hPropᵈ A P
  ≔ [
| .relate_l.p ↦ ¿ʔ
| .relate_r.p ↦ ¿ʔ
| .id.p ↦ a₀ a₁ p₀ p₁ ↦
    fib_hProp_lemma (A.2 a₀ a₁)
      (a₂ ↦ (x₀ : El.0 a₀) → (x₁ : El.1 a₁) → (El.2 a₂) x₀ x₁)
      (a₂ ↦ P.2 a₂ p₀ p₁)
      (a₂ p₂ ↦
       fib_Pi (El.0 a₀) (El.1 a₁) (x₀ x₁ ↦ El.2 a₂ x₀ x₁) (f.0 a₀ p₀)
         (f.1 a₁ p₁) (f.2 a₂ p₂ .id)) (a₂ f₂ ↦ ¿p.2 a₂ (f.2 a₂ ʔ)]

def fib_hProp_lemma (A : Type) (El : A → Type) (P : A → Type)
  (f : (a : A) → P a → isFibrant (El a))
  : Br_hPropᵈ A P
  ≔ [
| .relate_l.p ↦ a₀ a₁ p₀ p p₁ a₂ p₂ ↦ ¿f.2 a₂ p₂ .liftrʔ
| .relate_r.p ↦ ¿ʔ
| .id.p ↦ a₀ a₁ p₀ p₁ ↦
    fib_hProp_lemma (A.2 a₀ a₁)
      (a₂ ↦ (x₀ : El.0 a₀) → (x₁ : El.1 a₁) → (El.2 a₂) x₀ x₁)
      (a₂ ↦ P.2 a₂ p₀ p₁)
      (a₂ p₂ ↦
       fib_Pi (El.0 a₀) (El.1 a₁) (x₀ x₁ ↦ El.2 a₂ x₀ x₁) (f.0 a₀ p₀)
         (f.1 a₁ p₁) (f.2 a₂ p₂ .id))]



def fib_hProp_lemma_alt (A : Type) (El : A → Type) (P : Type → Type)
  (f : (a : A) → P (El a) → isFibrant (El a))
  : Br_hPropᵈ A (a ↦ P (El a))
  ≔ [
| .relate_l.p ↦ ¿fibProp_lʔ
| .relate_r.p ↦ ¿ʔ
| .id.p ↦ a₀ a₁ p₀ p₁ ↦
    ¿fib_hProp_lemma (A.2 a₀ a₁) (a₂ ↦ ((x₀: El.0 a₀)-> (x₁: El.1 a₁)-> (El.2 a₂) x₀ x₁))  ! f.2 ʔ]

def fib_hProp_lemma_Type : Br_hPropᵈ Type isFibrant
  ≔ fib_hProp_lemma Type (a ↦ a) isFibrant (A f ↦ f)
`-------------
` end misc 



def Br_hPropᵈ_fib : Br_hPropᵈ Type isFibrant ≔ [
| .relate_l.p ↦ A₀ A₁ f₀ f f₁ A₂ f₂ ↦ fibProp_l A₀ A₁ A₂ f₀ f f₁ f₂
| .relate_r.p ↦ A₀ A₁ f₀ f f₁ A₂ f₂ ↦ fibProp_r A₀ A₁ A₂ f₀ f f₁ f₂
| .id.p ↦ A₀ A₁ f₀ f₁ ↦ ¿ʔ]


` MAIN LEMMAS
`-------------
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

`-------------



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



def BrisFib_fib (A₀ A₁:Type) (A₂:Br Type A₀ A₁) (f₀:isFibrant A₀) (f₁:isFibrant A₁) : isFibrant (Br isFibrant A₂ f₀ f₁) := ?

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
