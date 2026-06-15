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

def to𝕗Rel (A₀ A₁ : Fib) (A₂ : Br Fib A₀ A₁) : A₀ .t → A₁ .t → Fib
  ≔ a₀ a₁ ↦ (t ≔ A₂ .t a₀ a₁, f ≔ A₂ .f .id a₀ a₁)

def isEquiv (A B : Fib) (f : A .t → B .t) : Type
  ≔ (b : B .t) → isContr (Σ𝕗 A (a ↦ Id𝕗 B (f a) b))

` TODO: rename
def apply (A B C : Fib) (f : A .t → B .t) (fe : isEquiv A B f)
  (g : B .t → C .t) (c : C .t)
  : Σ (B .t) (b ↦ Br (C .t) (g b) c) → Σ (A .t) (a ↦ Br (C .t) (g (f a)) c)
  ≔ be ↦
  let b ≔ be .fst in
  let e ≔ be .snd in
  (fst ≔ fe b .center .fst,
   snd ≔
     concat C (g (f (fe (be .fst) .center .fst))) (g (be .fst)) c
       (rel g (fe b .center .snd)) e)

` TODO: rename
def eee (A : Fib) (B C : A .t → Fib) (f : (a : A .t) → B a .t → C a .t)
  (a₀ a₁ : A .t) (b₀ : B a₀ .t) (b₁ : B a₁ .t)
  (e : Id𝕗 (Σ𝕗 A B) (a₀, b₀) (a₁, b₁) .t)
  : Id𝕗 (Σ𝕗 A C) (a₀, f a₀ b₀) (a₁, f a₁ b₁) .t
  ≔ (fst ≔ e .fst, snd ≔ rel f (e .fst) (e .snd))

def concat_1p' (A : Fib) (x y : A .t) (p : Br (A .t) x y)
  : Br (Br (A .t) x y) p (concat A x x y (rel x) p)
  ≔ inverse (Id𝕗 A x y) (concat A x x y (rel x) p) p (concat_1p A x y p)

def comp_Eqv (A B C : Fib) (f : A .t → B .t) (fe : isEquiv A B f)
  (g : B .t → C .t) (ge : isEquiv B C g)
  : isEquiv A C (a ↦ g (f a))
  ≔ c ↦ (
  center ≔ apply A B C f fe g c (ge c .center),
  contract ≔ ae ↦
    let a ≔ ae .fst in
    let e ≔ ae .snd in
    concat (Σ𝕗 A (a ↦ Id𝕗 C (g (f a)) c)) (a, e)
      (apply A B C f fe g c (f a, e)) (apply A B C f fe g c (ge c .center))
      (concat (Σ𝕗 A (a' ↦ Id𝕗 C (g (f a')) c)) (a, e)
         (a, concat C (g (f a)) (g (f a)) c (rel (g (f a))) e)
         (apply A B C f fe g c (f a, e))
         (fst ≔ rel a, snd ≔ concat_1p' C (g (f a)) c e)
         (eee A (a' ↦ Id𝕗 B (f a') (f a)) (a' ↦ Id𝕗 C (g (f a')) c)
            (a' z ↦ concat C (g (f a')) (g (f a)) c (rel g z) e) a
            (fe (f (ae .fst)) .center .fst) (rel f (rel a))
            (fe (f (ae .fst)) .center .snd)
            (fe (f a) .contract (a, rel (f a)))))
      (rel (apply A B C f fe g c) (ge c .contract (f a, e))))

def is11_of_bisim (A B : Fib) (R : A .t → B .t → Fib) (bs : isBisim A B R)
  : is11 A B R
  ≔ (
  contrr ≔ a ↦ (
    center ≔ (fst ≔ bs .trr a, snd ≔ bs .liftr a),
    contract ≔ be ↦
      let b ≔ be .fst in
      let e ≔ be .snd in
      (fst ≔ rel bs .id a b e a (bs .trr a) (bs .liftr a) .trr (rel a),
       snd ≔ rel bs .id a b e a (bs .trr a) (bs .liftr a) .liftr (rel a))),
  contrl ≔ b ↦ (
    center ≔ (fst ≔ bs .trl b, snd ≔ bs .liftl b),
    contract ≔ ae ↦
      let a ≔ ae .fst in
      let e ≔ ae .snd in
      (fst ≔ rel bs .id a b e (bs .trl b) b (bs .liftl b) .trl (rel b),
       snd ≔ rel bs .id a b e (bs .trl b) b (bs .liftl b) .liftl (rel b))))

def isEqv_of_is11 (A B : Fib) (R : A .t → B .t → Fib) (re : is11 A B R)
  : Σ (A .t → B .t) (f ↦ isEquiv A B f)
  ≔ (
  fst ≔ a ↦ re .contrr a .center .fst,
  snd ≔ b ↦ (
    center ≔ (
      fst ≔ re .contrl b .center .fst,
      snd ≔
        inverse B b (re .contrr (re .contrl b .center .fst) .center .fst)
          (re
           .contrr (re .contrl b .center .fst)
           .contract (fst ≔ b, snd ≔ re .contrl b .center .snd)
           .fst)),
    contract ≔ ae ↦
      let a ≔ ae .fst in
      let e ≔ ae .snd in
      ¿ʔ))

def comp (A B C : Fib) (e : Br Fib A B) (e' : Br Fib B C) : Br Fib A C ≔
  let R : A .t → B .t → Fib ≔ a b ↦ Idd𝕗 A B e a b in
  let f : A .t → B .t
    ≔ isEqv_of_is11 A B R (is11_of_bisim A B R (bisim_of_Id A B e)) .fst in
  let fe : isEquiv A B f
    ≔ isEqv_of_is11 A B R (is11_of_bisim A B R (bisim_of_Id A B e)) .snd in
  let R' : B .t → C .t → Fib ≔ b c ↦ Idd𝕗 B C e' b c in
  let f' : B .t → C .t
    ≔ isEqv_of_is11 B C R' (is11_of_bisim B C R' (bisim_of_Id B C e')) .fst
    in
  let fe' : isEquiv B C f'
    ≔ isEqv_of_is11 B C R' (is11_of_bisim B C R' (bisim_of_Id B C e')) .snd
    in
  univalence_vv A C (a ↦ f' (f a)) (comp_Eqv A B C f fe f' fe')

def comp1 (∂ : Fib) (P : (∂ .t → Fib) → Fib)
  (Rp Rp' Rp'' : Σ (∂ .t → Fib) (R ↦ P R .t))
  (e : Br (Σ (∂ .t → Fib) (R ↦ P R .t)) Rp Rp')
  (e' : Br (Σ (∂ .t → Fib) (R ↦ P R .t)) Rp' Rp'')
  : Br (Σ (∂ .t → Fib) (R ↦ P R .t)) Rp Rp'
  ≔ (fst ≔ {y₀} {y₁} y₂ ↦ ¿ʔ, snd ≔ ¿ʔ)

def inv (A B : Fib) (e : Br Fib A B) : Br Fib B A ≔ ¿ʔ

def help (∂₀ : Fib) (∂₁ : Fib) (∂₂ : Fib⁽ᵖ⁾ ∂₀ ∂₁) (R₀ : ∂₀ .t → Fib)
  (R₁ R₁' : ∂₁ .t → Fib) (R₂ : (∂₂ .t ⇒ Fib⁽ᵖ⁾) R₀ R₁)
  (R₁₂ : Br (∂₁ .t → Fib) R₁ R₁')
  : (∂₂ .t ⇒ Fib⁽ᵖ⁾) R₀ R₁'
  ≔ x ⤇ comp (R₀ x.0) (R₁ x.1) (R₁' x.1) (R₂ x.2) (R₁₂ (rel x.1))

def BrFibRest (A₀ A₁ : Fib) (A₂ : Br Type (A₀ .t) (A₁ .t))
  (_ : (x₀ : A₀ .t) → (x₁ : A₁ .t) → isFibrant (A₂ x₀ x₁))
  : Type
  ≔ codata [
| x .trr1 : A₀ .t → A₁ .t
| x .trr.p
  : {𝑥₀ : A₀.0 .t} {𝑥₁ : A₁.0 .t} (𝑥₂ : A₂.0 𝑥₀ 𝑥₁)
    →⁽ᵖ⁾ A₂.1 (A₀.2 .f .trr 𝑥₀) (A₁.2 .f .trr 𝑥₁)
| x .trl1 : A₁ .t → A₀ .t
| x .trl.p
  : {𝑥₀ : A₀.1 .t} {𝑥₁ : A₁.1 .t} (𝑥₂ : A₂.1 𝑥₀ 𝑥₁)
    →⁽ᵖ⁾ A₂.0 (A₀.2 .f .trl 𝑥₀) (A₁.2 .f .trl 𝑥₁)
| x .liftr1 : (a₀ : A₀ .t) → A₂ a₀ (x .trr1 a₀)
| x .liftr.p
  : {a₀₀ : A₀.0 .t} {a₀₁ : A₁.0 .t} (a₀₂ : A₂.0 a₀₀ a₀₁)
    →⁽ᵖ⁾ sym (A₂.2) a₀₂ (x.2 .trr a₀₂) (A₀.2 .f .liftr a₀₀)
           (A₁.2 .f .liftr a₀₁)
| x .liftl1 : (a₁ : A₁ .t) → A₂ (x .trl1 a₁) a₁
| x .liftl.p
  : {a₁₀ : A₀.1 .t} {a₁₁ : A₁.1 .t} (a₁₂ : A₂.1 a₁₀ a₁₁)
    →⁽ᵖ⁾ sym (A₂.2) (x.2 .trl a₁₂) a₁₂ (A₀.2 .f .liftl a₁₀)
           (A₁.2 .f .liftl a₁₁)
| x .id.p
  : {a₀₀ : A₀.0 .t} {a₀₁ : A₁.0 .t} (a₀₂ : A₂.0 a₀₀ a₀₁) {a₁₀ : A₀.1 .t}
    {a₁₁ : A₁.1 .t} (a₁₂ : A₂.1 a₁₀ a₁₁)
    →⁽ᵖ⁾ isFibrant⁽ᵖ⁾ (sym (A₂.2) a₀₂ a₁₂) (A₀.2 .f .id a₀₀ a₁₀)
           (A₁.2 .f .id a₀₁ a₁₁) ]

def BrFibRest (A₀ A₁ : Fib) (A₂ : (A₀ .t) → (A₁ .t) → Type) : Type
  ≔ codata [
| x .trr1 : A₀ .t → A₁ .t
| x .trr.p
  : (𝑥₀ : A₀.0 .t) (𝑥₁ : A₁.0 .t) (𝑥₂ : A₂.0 𝑥₀ 𝑥₁)
    → A₂.1 (A₀.2 .f .trr 𝑥₀) (A₁.2 .f .trr 𝑥₁)
| x .trl1 : A₁ .t → A₀ .t
| x .trl.p
  : (𝑥₀ : A₀.1 .t) (𝑥₁ : A₁.1 .t) (𝑥₂ : A₂.1 𝑥₀ 𝑥₁)
    → A₂.0 (A₀.2 .f .trl 𝑥₀) (A₁.2 .f .trl 𝑥₁)
| x .liftr1 : (a₀ : A₀ .t) → A₂ a₀ (x .trr1 a₀)
| x .liftr.p
  : (a₀₀ : A₀.0 .t) (a₀₁ : A₁.0 .t) (a₀₂ : A₂.0 a₀₀ a₀₁)
    → A₂.2 (A₀.2 .f .liftr a₀₀) (A₁.2 .f .liftr a₀₁) a₀₂
        (x.2 .trr a₀₀ a₀₁ a₀₂)
| x .liftl1 : (a₁ : A₁ .t) → A₂ (x .trl1 a₁) a₁
| x .liftl.p
  : (a₁₀ : A₀.1 .t) (a₁₁ : A₁.1 .t) (a₁₂ : A₂.1 a₁₀ a₁₁)
    → A₂.2 (A₀.2 .f .liftl a₁₀) (A₁.2 .f .liftl a₁₁) (x.2 .trl a₁₀ a₁₁ a₁₂)
        a₁₂
`sym (A₂.2) (x.2 .trl a₁₂) a₁₂ (A₀.2 .f .liftl a₁₀)
`    (A₁.2 .f .liftl a₁₁)
| x .id.p
  : (a₀₀ : A₀.0 .t) (a₀₁ : A₁.0 .t) (a₀₂ : A₂.0 a₀₀ a₀₁) (a₁₀ : A₀.1 .t)
    (a₁₁ : A₁.1 .t) (a₁₂ : A₂.1 a₁₀ a₁₁)
    → ¿isFibrant⁽ᵖ⁾ ( (A₂.2) a₀₂ a₁₂ (A₀.2 .f .id a₀₀ a₁₀)
`    (A₁.2 .f .id a₀₁ a₁₁))ʔ `isFibrant⁽ᵖ⁾ (sym (A₂.2) a₀₂ a₁₂) (A₀.2 .f .id a₀₀ a₁₀)
`    (A₁.2 .f .id a₀₁ a₁₁)
]

def T (A : Type) (f : isFibrant A) : Type ≔ codata [
| x .des.p : (a₀ : A.0) → (a₁ : A.1) → A.2 a₀ a₁ ]

def isFibT (A : Type) (f : isFibrant A) : isFibrant (T A f) ≔ [
| .trr.p ↦ x ↦ [
  | .des.p ↦ a₀ a₁ ↦
      let a₀₂ ≔ x.2 .des (f.20 .trl a₀) (f.21 .trl a₁) in
      ¿(sym f.22) .id.1 ʔ]
| .trl.p ↦ ¿ʔ
| .liftr.p ↦ ¿ʔ
| .liftl.p ↦ ¿ʔ
| .id.p ↦ ¿ʔ] 

def funΣ (A B : Type) (f : A → B) (P : A → Type) (Q : B → Type)
  (g : (a : A) → (P a) → Q (f a))
  : (Σ A P) → Σ B Q
  ≔ x ↦ (fst ≔ f (x .fst), snd ≔ g (x .fst) (x .snd))

def vsurj_Σ (A B : Type) (f : A → B) (fs : vsurj A B f) (P : A → Fib)
  (Q : B → Fib) (R : (a : A) → Br Fib (P a) (Q (f a)))
  : vsurj (Σ A (a ↦ P a .t)) (Σ B (b ↦ Q b .t))
      (funΣ A B f (a ↦ P a .t) (b ↦ Q b .t) (a p ↦ R a .f .trr p))
  ≔ [
| .surj ↦
    funΣ B A (fs .surj) (b ↦ Q b .t) (a ↦ P a .t)
      (b q ↦
       let g₁ : Q b .t → Q (f (fs .surj b)) .t
         ≔ rel Q (fs .surjeq b) .f .trl in
       let g₂ : Q (f (fs .surj b)) .t → P (fs .surj b) .t
         ≔ R (fs .surj b) .f .trl in
       g₂ (g₁ q))
| .surjeq ↦ x ↦
    let b ≔ x .fst in
    let q ≔ x .snd in
    (fst ≔ fs .surjeq b, snd ≔ ¿rel Q (fs .surjeq b) .f .liftl qʔ)
| .id.p ↦ ¿ʔ]    

def BrFibUnfolded (A₀ A₁ : Fib) : Type ≔ sig (
  R : Br Type (A₀ .t) (A₁ .t),
  Rf : (a₀ : A₀ .t) (a₁ : A₁ .t) → isFibrant (R a₀ a₁),
  rest : BrFibRest A₀ A₁ R )

`| x .id1 : (a₀ : A₀ .t) (a₁ : A₁ .t) → isFibrant (x .R a₀ a₁)

def BrIsFib_eq (A₀ A₁ : Fib) : Br Fib A₀ A₁ ≅ BrFibUnfolded A₀ A₁ ≔ (
  to ≔ x ↦ (
    x .t,
    x .f .id,
    [ .trr1 ↦ x .f .trr
    | .trr.p ↦ x.2 .f .trr.2
    | .trl1 ↦ x .f .trl
    | .trl.p ↦ x.2 .f .trl.2
    | .liftr1 ↦ x .f .liftr
    | .liftr.p ↦ x.2 .f .liftr.2
    | .liftl1 ↦ x .f .liftl
    | .liftl.p ↦ x.2 .f .liftl.2
    | .id.p ↦ x.2 .f .id.2]),
  fro ≔ x ↦ (
    t ≔ x .R,
    f ≔ [
    | .trr.p ⤇ x.2 .rest .trr
    | .trr.1 ⤇ x .rest .trr1
    | .trl.p ⤇ x.2 .rest .trl
    | .trl.1 ⤇ x .rest .trl1
    | .liftr.p ⤇ x.2 .rest .liftr
    | .liftr.1 ⤇ x .rest .liftr1
    | .liftl.p ⤇ x.2 .rest .liftl
    | .liftl.1 ⤇ x .rest .liftl1
    | .id.p ⤇ x.2 .rest .id
    | .id.1 ⤇ x .Rf]),
  fro_to ≔ ¿ʔ,
  to_fro ≔ ¿ʔ,
  to_fro_to ≔ ¿ʔ)

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
    let ∂₀ : Fib ≔ u₀ .∂ in
    let ∂₁ : Fib ≔ u₁ .∂ in
    let ∂₂ : Fib⁽ᵖ⁾ ∂₀ ∂₁ ≔ u₂ .∂ in
    let P₀ : (∂₀ .t → Fib) → Fib ≔ u₀ .P in
    let P₁ : (∂₁ .t → Fib) → Fib ≔ u₁ .P in
    let P₂
      : {R₀ : ∂₀ .t → Fib} {R₁ : ∂₁ .t → Fib}
        (R₂
        : {𝑦₀ : ∂₀ .t} {𝑦₁ : ∂₁ .t} (𝑦₂ : ∂₂ .t 𝑦₀ 𝑦₁)
          →⁽ᵖ⁾ Fib⁽ᵖ⁾ (R₀ 𝑦₀) (R₁ 𝑦₁))
        →⁽ᵖ⁾ Fib⁽ᵖ⁾ (P₀ R₀) (P₁ R₁)
      ≔ u₂ .P in
    let f₀ : X₀ → Σ (∂₀ .t → Fib) (R ↦ P₀ R .t) ≔ u₀ .f in
    let f₁ : X₁ → Σ (∂₁ .t → Fib) (R ↦ P₁ R .t) ≔ u₁ .f in
    let f₂
      : {𝑥₀ : X₀} {𝑥₁ : X₁} (𝑥₂ : X₂ 𝑥₀ 𝑥₁)
        →⁽ᵖ⁾ Σ⁽ᵖ⁾ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t}
               (R ⤇ P₂ R.2 .t) (f₀ 𝑥₀) (f₁ 𝑥₁)
      ≔ u₂ .f in
    let v₀ : vsurj X₀ (Σ (∂₀ .t → Fib) (R ↦ P₀ R .t)) f₀ ≔ u₀ .v in
    let v₁ : vsurj X₁ (Σ (∂₁ .t → Fib) (R ↦ P₁ R .t)) f₁ ≔ u₁ .v in
    let v₂
      : vsurj⁽ᵖ⁾ X₂
          (Σ⁽ᵖ⁾ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t}
             (R ⤇ P₂ R.2 .t)) f₂ v₀ v₁
      ≔ u₂ .v in
    let R₀ : ∂₀ .t → Fib ≔ f₀ x₀ .fst in
    let R₁ : ∂₁ .t → Fib ≔ y₁ ↦ f₀ x₀ .fst (∂₂ .f .trl y₁) in
    let R₂
      : {𝑦₀ : ∂₀ .t} {𝑦₁ : ∂₁ .t} (𝑦₂ : ∂₂ .t 𝑦₀ 𝑦₁)
        →⁽ᵖ⁾ Fib⁽ᵖ⁾ (R₀ 𝑦₀) (R₁ 𝑦₁)
      ≔ {y₀} {y₁} y₂ ↦
        rel R₀ {y₀} {∂₂ .f .trl y₁} (untrl ∂₀ ∂₁ ∂₂ y₀ y₁ y₂) in
    let p₀ : P₀ R₀ .t ≔ f₀ x₀ .snd in
    let p₁ : P₁ R₁ .t ≔ P₂ R₂ .f .trr p₀ in
    let p₂ : P₂ R₂ .t p₀ p₁ ≔ P₂ R₂ .f .liftr p₀ in
    let Rp₂
      : rel Σ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t} (R ⤇ P₂ R.2 .t)
          (R₀, p₀) (R₁, p₁) ≔ (fst ≔ R₂, snd ≔ p₂) in
    let Rp₁₂
      : Br (Σ (∂₁ .t → Fib) (R ↦ P₁ R .t)) (f₁ (v₁ .surj (R₁, p₁)))
          (R₁, p₁)
      ≔ v₁ .surjeq (R₁, p₁) in
    let res
      : rel Σ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t} (R ⤇ P₂ R.2 .t)
          (R₀, p₀) (f₁ (v₁ .surj (R₁, p₁)))
      ≔ ¿f₀ x₀ .sndʔ in
    v₂ .id x₀ (v₁ .surj (R₁, p₁)) .surj res

{`
(
      fst ≔ {y₀} {y₁} y₂ ↦
        comp (R₀ y₀) (R₁ y₁) (f₁ (v₁ .surj (R₁, p₁)) .fst y₁) (Rp₂ .fst y₂)
          (inv (f₁ (v₁ .surj (R₁, p₁)) .fst y₁) (R₁ y₁)
             (Rp₁₂ .fst (rel y₁))),
      snd ≔ ¿ʔ)
`}

  def id (X₀ X₁ : Type) (X₂ : Br Type X₀ X₁) (u₀ : F X₀) (u₁ : F X₁)
    (u₂ : Br F X₂ u₀ u₁) (x₀ : X₀) (x₁ : X₁)
    : F (X₂ x₀ x₁)
    ≔
    let ∂₀ : Fib ≔ u₀ .∂ in
    let ∂₁ : Fib ≔ u₁ .∂ in
    let ∂₂ : Fib⁽ᵖ⁾ ∂₀ ∂₁ ≔ u₂ .∂ in
    let P₀ : (∂₀ .t → Fib) → Fib ≔ u₀ .P in
    let P₁ : (∂₁ .t → Fib) → Fib ≔ u₁ .P in
    let P₂
      : {R₀ : ∂₀ .t → Fib} {R₁ : ∂₁ .t → Fib}
        (R₂
        : {𝑦₀ : ∂₀ .t} {𝑦₁ : ∂₁ .t} (𝑦₂ : ∂₂ .t 𝑦₀ 𝑦₁)
          →⁽ᵖ⁾ Fib⁽ᵖ⁾ (R₀ 𝑦₀) (R₁ 𝑦₁))
        →⁽ᵖ⁾ Fib⁽ᵖ⁾ (P₀ R₀) (P₁ R₁)
      ≔ u₂ .P in
    let f₀ : X₀ → Σ (∂₀ .t → Fib) (R ↦ P₀ R .t) ≔ u₀ .f in
    let f₁ : X₁ → Σ (∂₁ .t → Fib) (R ↦ P₁ R .t) ≔ u₁ .f in
    let R₀ : ∂₀ .t → Fib ≔ f₀ x₀ .fst in
    let R₁ : ∂₁ .t → Fib ≔ f₁ x₁ .fst in
    let p₀ : P₀ R₀ .t ≔ f₀ x₀ .snd in
    let p₁ : P₁ R₁ .t ≔ f₁ x₁ .snd in
    let f₂
      : {𝑥₀ : X₀} {𝑥₁ : X₁} (𝑥₂ : X₂ 𝑥₀ 𝑥₁)
        →⁽ᵖ⁾ Σ⁽ᵖ⁾ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t}
               (R ⤇ P₂ R.2 .t) (f₀ 𝑥₀) (f₁ 𝑥₁)
      ≔ u₂ .f in
    let g
      : (X₂ x₀ x₁)
        → Σ⁽ᵖ⁾ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t} (R ⤇ P₂ R.2 .t)
            (f₀ x₀) (f₁ x₁)
      ≔ x₂ ↦ f₂ {x₀} {x₁} x₂ in
    let v₀ : vsurj X₀ (Σ (∂₀ .t → Fib) (R ↦ P₀ R .t)) f₀ ≔ u₀ .v in
    let v₁ : vsurj X₁ (Σ (∂₁ .t → Fib) (R ↦ P₁ R .t)) f₁ ≔ u₁ .v in
    let v₂
      : vsurj⁽ᵖ⁾ X₂
          (Σ⁽ᵖ⁾ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t}
             (R ⤇ P₂ R.2 .t)) f₂ v₀ v₁
      ≔ u₂ .v in
    (∂ ≔ Σ𝕗 ∂₀ (y₀ ↦ Σ𝕗 ∂₁ (y₁ ↦ to𝕗Rel ∂₀ ∂₁ ∂₂ y₀ y₁)),
     P ≔ ¿ʔ,
     f ≔ ¿ʔ,
     v ≔ ¿ʔ)
end
