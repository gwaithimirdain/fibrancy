{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"
import "univalence"

def vsurj (A B : Type) (f : A → B) : Type ≔ codata [
| s .surj : B → A
| s .surjeq : (b : B) → Br B (f (s .surj b)) b
| s .id.p
  : (a0 : A.0) (a1 : A.1)
    → vsurj (A.2 a0 a1) (B.2 (f.0 a0) (f.1 a1)) (a2 ↦ f.2 a2) ]

section genVsurj ≔
  axiom F : (A B : Type) (f : A → B) → Type
  axiom surj : (A B : Type) (f : A → B) → F A B f → B → A
  axiom surjeq
    : (A B : Type) (f : A → B) (x : F A B f) (b : B)
      → Br B (f (surj A B f x b)) b
  axiom id
    : (A₀ A₁ : Type) (A₂ : Br Type A₀ A₁) (B₀ B₁ : Type)
      (B₂ : Br Type B₀ B₁) (f₀ : A₀ → B₀) (f₁ : A₁ → B₁)
      (f₂ : Br (A B ↦ A → B) A₂ B₂ f₀ f₁) → (a₀ : A₀) (a₁ : A₁)
      → F (A₂ a₀ a₁) (B₂ (f₀ a₀) (f₁ a₁)) (a₂ ↦ f₂ a₂)
  def gen (A B : Type) (f : A → B) (x : F A B f) : vsurj A B f ≔ [
  | .surj ↦ surj A B f x
  | .surjeq ↦ surjeq A B f x
  | .id.p ↦ a₀ a₁ ↦
      gen (A.2 a₀ a₁) (B.2 (f.0 a₀) (f.1 a₁)) (a₂ ↦ f.2 a₂)
        (id A.0 A.1 A.2 B.0 B.1 B.2 f.0 f.1 f.2 a₀ a₁)]
end

section isFibGen ≔
  axiom F : Type → Type
  axiom trr
    : (X₀ X₁ : Type) (X₂ : Br Type X₀ X₁) (f₀ : F X₀) (f₁ : F X₁)
      (f₂ : Br F X₂ f₀ f₁) → X₀
      → X₁
  axiom trl
    : (X₀ X₁ : Type) (X₂ : Br Type X₀ X₁) (f₀ : F X₀) (f₁ : F X₁)
      (f₂ : Br F X₂ f₀ f₁) → X₁
      → X₀
  axiom liftr
    : (X₀ X₁ : Type) (X₂ : Br Type X₀ X₁) (f₀ : F X₀) (f₁ : F X₁)
      (f₂ : Br F X₂ f₀ f₁) (x₀ : X₀)
      → X₂ x₀ (trr X₀ X₁ X₂ f₀ f₁ f₂ x₀)
  axiom liftl
    : (X₀ X₁ : Type) (X₂ : Br Type X₀ X₁) (f₀ : F X₀) (f₁ : F X₁)
      (f₂ : Br F X₂ f₀ f₁) (x₁ : X₁)
      → X₂ (trl X₀ X₁ X₂ f₀ f₁ f₂ x₁) x₁
  axiom id
    : (X₀ X₁ : Type) (X₂ : Br Type X₀ X₁) (f₀ : F X₀) (f₁ : F X₁)
      (f₂ : Br F X₂ f₀ f₁) (x₀ : X₀) (x₁ : X₁)
      → F (X₂ x₀ x₁)

  def gen (X : Type) (f : F X) : isFibrant X ≔ [
  | .trr.p ↦ trr X.0 X.1 X.2 f.0 f.1 f.2
  | .trl.p ↦ trl X.0 X.1 X.2 f.0 f.1 f.2
  | .liftr.p ↦ liftr X.0 X.1 X.2 f.0 f.1 f.2
  | .liftl.p ↦ liftl X.0 X.1 X.2 f.0 f.1 f.2
  | .id.p ↦ x₀ x₁ ↦ gen (X.2 x₀ x₁) (id X.0 X.1 X.2 f.0 f.1 f.2 x₀ x₁)]
end

{`
a₁=======a₁
|        |
|   ∥    |A₂ .f .liftl a₁
|   V    |
a₀.......A₂ .f .trl a₁
`}
def untrl (A₀ A₁ : Fib) (A₂ : Br Fib A₀ A₁) (a₀ : A₀ .t) (a₁ : A₁ .t)
  (a₂ : A₂ .t a₀ a₁)
  : Br (A₀ .t) a₀ (A₂ .f .trl a₁)
  ≔ rel A₂ .f .id.2 a₂ (A₂ .f .liftl a₁) .trl (rel a₁)
`  A₂ .f .id
`  rel (A₂ .f .id)
` same error message for the above two lines

def unliftl (A₀ A₁ : Fib) (A₂ : Br Fib A₀ A₁) (a₀ : A₀ .t) (a₁ : A₁ .t)
  (a₂ : A₂ .t a₀ a₁)
  : sym (Br (A₂ .t)) a₂ (A₂ .f .liftl a₁) (untrl A₀ A₁ A₂ a₀ a₁ a₂)
      (rel a₁)
  ≔ rel A₂ .f .id.2 a₂ (A₂ .f .liftl a₁) .liftl (rel a₁)

` def to𝕗Rel (A₀ A₁ : Fib) (A₂ : Br Fib A₀ A₁) : A₀ .t → A₁ .t → Fib
`  ≔ a₀ a₁ ↦ (t ≔ A₂ .t a₀ a₁, f ≔ A₂ .f .id a₀ a₁)

def comp_vv (A B C : Fib) 
  (f : A .t → B .t)(fe : (b : B .t) → isContr (Σ𝕗 A (a ↦ Id𝕗 B (f a) b)))
  (g : B .t → C .t)(ge : (c : C .t) → isContr (Σ𝕗 B (b ↦ Id𝕗 C (g b) c))) :
  (c : C .t) → isContr (Σ𝕗 A (a ↦ Id𝕗 C (g (f a)) c)) ≔
     c ↦ (center ≔ (fst ≔ fe (ge c .center .fst) .center .fst, snd ≔ concat C (g (f (fe (ge c .center .fst) .center .fst))) (g (ge c .center .fst)) c (rel g (fe (ge c .center .fst) .center .snd)) (ge c .center .snd)), contract ≔ ae ↦ ¿ʔ)

{`
def univalence_vv (A B : Fib) (f : A .t → B .t)
  (fe : (b : B .t) → isContr (Σ𝕗 A (a ↦ Id𝕗 B (f a) b)))
  : Br Fib A B
`}

def comp (A B C : Fib)(e : Br Fib A B)(f : Br Fib B C) : Br Fib A C ≔ ¿ʔ

def help (∂₀ : Fib)(∂₁ : Fib)(∂₂ : Fib⁽ᵖ⁾ ∂₀ ∂₁)(R₀ : ∂₀ .t → Fib)(R₁ R₁' : ∂₁ .t → Fib)
  (R₂ : (∂₂ .t ⇒ Fib⁽ᵖ⁾) R₀ R₁)(R₁₂ : Br (∂₁ .t → Fib) R₁ R₁') : (∂₂ .t ⇒ Fib⁽ᵖ⁾) R₀ R₁'
  ≔ x ⤇ comp (R₀ x.0) (R₁ x.1) (R₁' x.1) (R₂ x.2) (R₁₂ (rel x.1))

section gen𝕗Fib ≔
  def F (X : Type) : Type ≔ sig (
    ∂ : Fib,
    P : (∂ .t → Fib) → Fib,
    f : X → Σ (∂ .t → Fib) (R ↦ P R .t),
    v : vsurj X (Σ (∂ .t → Fib) (R ↦ P R .t)) f )
  def trr (X₀ X₁ : Type) (X₂ : Br Type X₀ X₁) (f₀ : F X₀) (f₁ : F X₁)
    (f₂ : Br F X₂ f₀ f₁) (x₀ : X₀)
    : X₁
    ≔
    let R₀ ≔ f₀ .f x₀ .fst in
    let p₀ ≔ f₀ .f x₀ .snd in
    f₁
      .v
      .surj
        (y₁ ↦ R₀ (f₂ .∂ .f .trl y₁),
         f₂
           .P {R₀} {y₁ ↦ R₀ (f₂ .∂ .f .trl y₁)}
             ({y₀} {y₁} y₂ ↦
              rel (f₀ .f x₀ .fst) {y₀} {f₂ .∂ .f .trl y₁}
                (untrl (f₀ .∂) (f₁ .∂) (f₂ .∂) y₀ y₁ y₂))
           .f
           .trr p₀)

  def liftr (X₀ X₁ : Type) (X₂ : Br Type X₀ X₁) (u₀ : F X₀) (u₁ : F X₁)
    (u₂ : Br F X₂ u₀ u₁) (x₀ : X₀)
    : X₂ x₀ (trr X₀ X₁ X₂ u₀ u₁ u₂ x₀)
    ≔
    let ∂₀ : Fib                                                                                                                                              ≔ u₀ .∂ in
    let ∂₁ : Fib                                                                                                                                              ≔ u₁ .∂ in
    let ∂₂ : Fib⁽ᵖ⁾ ∂₀ ∂₁                                                                                                                                     ≔ u₂ .∂ in
    let P₀ : (∂₀ .t → Fib) → Fib                                                                                                                              ≔ u₀ .P in
    let P₁ : (∂₁ .t → Fib) → Fib                                                                                                                              ≔ u₁ .P in
    let P₂ : {R₀ : ∂₀ .t → Fib}{R₁ : ∂₁ .t → Fib} (R₂ : {𝑦₀ : ∂₀ .t} {𝑦₁ : ∂₁ .t} (𝑦₂ : ∂₂ .t 𝑦₀ 𝑦₁) →⁽ᵖ⁾ Fib⁽ᵖ⁾ (R₀ 𝑦₀) (R₁ 𝑦₁)) →⁽ᵖ⁾ Fib⁽ᵖ⁾ (P₀ R₀) (P₁ R₁) ≔ u₂ .P in
    let f₀ : X₀ → Σ (∂₀ .t → Fib) (R ↦ P₀ R .t)                                                                                                               ≔ u₀ .f in
    let f₁ : X₁ → Σ (∂₁ .t → Fib) (R ↦ P₁ R .t)                                                                                                               ≔ u₁ .f in
    let f₂ : {𝑥₀ : X₀}{𝑥₁ : X₁}(𝑥₂ : X₂ 𝑥₀ 𝑥₁) →⁽ᵖ⁾ Σ⁽ᵖ⁾ (∂₂ .t ⇒ Fib⁽ᵖ⁾){R ↦ P₀ R .t}{R ↦ P₁ R .t} (R ⤇ P₂ R.2 .t) (f₀ 𝑥₀) (f₁ 𝑥₁)                           ≔ u₂ .f in
    let v₀ : vsurj X₀ (Σ (∂₀ .t → Fib) (R ↦ P₀ R .t)) f₀                                                                                                      ≔ u₀ .v in
    let v₁ : vsurj X₁ (Σ (∂₁ .t → Fib) (R ↦ P₁ R .t)) f₁                                                                                                      ≔ u₁ .v in
    let v₂ : vsurj⁽ᵖ⁾ X₂ (Σ⁽ᵖ⁾ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t} (R ⤇ P₂ R.2 .t)) f₂ v₀ v₁                                                         ≔ u₂ .v in
    let R₀ : ∂₀ .t → Fib ≔ f₀ x₀ .fst in
    let R₁ : ∂₁ .t → Fib ≔ y₁ ↦ f₀ x₀ .fst (∂₂ .f .trl y₁) in
    let R₂ : {𝑦₀ : ∂₀ .t}{𝑦₁ : ∂₁ .t}(𝑦₂ : ∂₂ .t 𝑦₀ 𝑦₁) →⁽ᵖ⁾ Fib⁽ᵖ⁾ (R₀ 𝑦₀) (R₁ 𝑦₁)
           ≔ {y₀} {y₁} y₂ ↦ rel R₀ {y₀} {∂₂ .f .trl y₁} (untrl ∂₀ ∂₁ ∂₂ y₀ y₁ y₂) in
    let p₀ : P₀ R₀ .t    ≔ f₀ x₀ .snd in
    let p₁ : P₁ R₁ .t    ≔ P₂ R₂ .f .trr p₀ in
    let p₂ : P₂ R₂ .t p₀ p₁ ≔ P₂ R₂ .f .liftr p₀ in
    let Rp₂ : rel Σ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t} (R ⤇ P₂ R.2 .t) (R₀ , p₀) (R₁ , p₁)
             ≔ (fst ≔ R₂, snd ≔ p₂) in
    let Rp₁₂ : Br (Σ (∂₁ .t → Fib) (R ↦ P₁ R .t)) (f₁ (v₁ .surj (R₁ , p₁))) (R₁ , p₁)
             ≔ v₁ .surjeq (R₁ , p₁) in
    let res : rel Σ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t} (R ⤇ P₂ R.2 .t) (R₀ , p₀) (f₁ (v₁ .surj (R₁ , p₁)))
            ≔ ¿ʔ in
    v₂ .id x₀ (v₁ .surj (R₁ , p₁)) .surj res

` v₁ .surjeq (R₁ , p₁)

  def id (X₀ X₁ : Type) (X₂ : Br Type X₀ X₁) (u₀ : F X₀) (u₁ : F X₁)
    (u₂ : Br F X₂ u₀ u₁) (x₀ : X₀) (x₁ : X₁)
    : F (X₂ x₀ x₁)
    ≔
    let ∂₀ ≔ u₀ .∂ in
    let ∂₁ ≔ u₁ .∂ in
    let ∂₂ ≔ u₂ .∂ in
    let P₀ ≔ u₀ .P in
    let P₁ ≔ u₁ .P in
    let P₂ ≔ u₂ .P in
    let f₀ ≔ u₀ .f in
    let f₁ ≔ u₁ .f in
    let f₂ ≔ u₂ .f in
    let v₀ ≔ u₀ .v in
    let v₁ ≔ u₁ .v in
    let v₂ ≔ u₂ .v in
    (∂ ≔ Σ𝕗 ∂₀ (y₀ ↦ Σ𝕗 ∂₁ (y₁ ↦ to𝕗Rel ∂₀ ∂₁ ∂₂ y₀ y₁)),
     P ≔ ¿ʔ,
     f ≔ ¿ʔ,
     v ≔ ¿ʔ)
end

def f (A₀ A₁ : Type)(A₂ : Br Type A₀ A₁)(f₀ : isFibrant A₀)(f₁ : isFibrant A₁) :
  Br isFibrant A₂ f₀ f₁ ≔ [ .trr.p ⤇ ¿ʔ
| .trr.1 ⤇ ¿ʔ
| .trl.p ⤇ ¿ʔ
| .trl.1 ⤇ ¿ʔ
| .liftr.p ⤇ ¿ʔ
| .liftr.1 ⤇ ¿ʔ
| .liftl.p ⤇ ¿ʔ
| .liftl.1 ⤇ ¿ʔ
| .id.p ⤇ ¿ʔ
| .id.1 ⤇ ¿ʔ]




def BrIsFibUnfolded (A₀ A₁ : Type) (A₂ : Type⁽ᵖ⁾ A₀ A₁) (f₀ : isFibrant A₀)
  (f₁ : isFibrant A₁)
  : Type
  ≔ codata [
| f₂ .trr : A₀ → A₁
| f₂ .trr'.p
  : {𝑥₀ : A₀.0} {𝑥₁ : A₁.0} (𝑥₂ : A₂.0 𝑥₀ 𝑥₁)
    →⁽ᵖ⁾ A₂.1 (f₀.2 .trr 𝑥₀) (f₁.2 .trr 𝑥₁)
| f₂ .trl : A₁ → A₀
| f₂ .trl'.p
  : {𝑥₀ : A₀.1} {𝑥₁ : A₁.1} (𝑥₂ : A₂.1 𝑥₀ 𝑥₁)
    →⁽ᵖ⁾ A₂.0 (f₀.2 .trl 𝑥₀) (f₁.2 .trl 𝑥₁)
| f₂ .liftr : (a₀ : A₀) → A₂ a₀ (f₂ .trr a₀)
| f₂ .liftr'.p : ¿ʔ
`  {a₀₀ : A₀.0} {a₀₁ : A₁.0} (a₀₂ : A₂.0 a₀₀ a₀₁)
`  →⁽ᵖ⁾ sym A₂.2 a₀₂ (sym ? .trr.1 a₀₂) (f₀.2 .liftr a₀₀) (f₁.2 .liftr a₀₁)
| f₂ .liftl : (a₁ : A₁) → A₂ (f₂ .trl a₁) a₁
| f₂ .id : (a₀ : A₀) (a₁ : A₁) → isFibrant (A₂ a₀ a₁) ]
` xxx
` 
def unfold (A₀ A₁ : Type) (A₂ : Type⁽ᵖ⁾ A₀ A₁) (f₀ : isFibrant A₀)
  (f₁ : isFibrant A₁)
  : Br isFibrant A₂ f₀ f₁ ≅ BrIsFibUnfolded A₀ A₁ A₂ f₀ f₁
  ≔ adjointify (Br isFibrant A₂ f₀ f₁) (BrIsFibUnfolded A₀ A₁ A₂ f₀ f₁)
      (f₂ ↦ ¿ʔ)
      (f₂ ↦
       [ .trr.p ⤇ f₂ .trr'
       | .trr.1 ⤇ f₂ .trr
       | .trl.p ⤇ f₂ .trl'
       | .trl.1 ⤇ f₂ .trl
       | .liftr.p ⤇ ¿ʔ
       | .liftr.1 ⤇ f₂ .liftr
       | .liftl.p ⤇ ¿ʔ
       | .liftl.1 ⤇ ¿ʔ
       | .id.p ⤇ ¿ʔ
       | .id.1 ⤇ f₂ .id]) ¿ʔ ¿ʔ
def to11 (A₀ A₁ : Fib)(A₂ : Br Fib A₀ A₁) : 
  ≔ ¿ʔ
