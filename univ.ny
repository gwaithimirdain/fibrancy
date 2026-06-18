{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"
import "univalence"


` copy and paste from vsurj.ny
`==========================================

def mapΣ (A B : Type) (f : A → B) (Aᵈ : A → Type) (Bᵈ : B → Type)
  (fᵈ : (x : A) → Aᵈ x → Bᵈ (f x))
  : Σ A Aᵈ → Σ B Bᵈ
  ≔ u ↦ (f (u .fst), fᵈ (u .fst) (u .snd))

def vsurj (A B : Type) (f : A → B) : Type ≔ codata [
| s .surj : B → A
| s .surjeq : (b : B) → Br B (f (s .surj b)) b
| s .id.p
  : (a0 : A.0) (a1 : A.1)
    → vsurj (A.2 a0 a1) (B.2 (f.0 a0) (f.1 a1)) (a2 ↦ f.2 a2) ]

` copy and paste from vsurj.ny
def vsurj_eqv (A0 B0 : Type) (f0 : A0 → B0) (A1 B1 : Type) (f1 : A1 → B1)
  (eA : A0 ≅ A1) (eB : B0 ≅ B1)
  (ef : (x : A0) → eq.eq B1 (eB .to (f0 x)) (f1 (eA .to x)))
  (s0 : vsurj A0 B0 f0)
  : vsurj A1 B1 f1
  ≔ [
| .surj ↦ b1 ↦ eA .to (s0 .surj (eB .fro b1))
| .surjeq ↦ b1 ↦
    eq.trr2 B1 B1 (x y ↦ Br B1 x y) (eB .to (f0 (s0 .surj (eB .fro b1))))
      (f1 (eA .to (s0 .surj (eB .fro b1)))) (ef (s0 .surj (eB .fro b1)))
      (eB .to (eB .fro b1)) b1 (eB .to_fro b1)
      (rel (eB .to) (s0 .surjeq (eB .fro b1)))
| .id.p ↦ a0 a1 ↦
    vsurj_eqv (A0.2 (eA.0 .fro a0) (eA.1 .fro a1))
      (B0.2 (f0.0 (eA.0 .fro a0)) (f0.1 (eA.1 .fro a1))) (a2 ↦ f0.2 a2)
      (A1.2 a0 a1) (B1.2 (f1.0 a0) (f1.1 a1)) (a2 ↦ f1.2 a2)
      (Id_eqv A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 eA.0 eA.1 eA.2 a0 a1)
      (comp_eqv (B0.2 (f0.0 (eA.0 .fro a0)) (f0.1 (eA.1 .fro a1)))
         (B0.2 (eB.0 .fro (f1.0 a0)) (eB.1 .fro (f1.1 a1)))
         (B1.2 (f1.0 a0) (f1.1 a1))
         (eqv_trr2 B0.0 B0.1 (x y ↦ B0.2 x y) (f0.0 (eA.0 .fro a0))
            (eB.0 .fro (f1.0 a0))
            (eqv_transpose A0.0 B0.0 f0.0 A1.0 B1.0 f1.0 eA.0 eB.0 ef.0 a0)
            (f0.1 (eA.1 .fro a1)) (eB.1 .fro (f1.1 a1))
            (eqv_transpose A0.1 B0.1 f0.1 A1.1 B1.1 f1.1 eA.1 eB.1 ef.1 a1))
         (Id_eqv B0.0 B0.1 B0.2 B1.0 B1.1 B1.2 eB.0 eB.1 eB.2 (f1.0 a0)
            (f1.1 a1)))
      ` Hole to be filled here, should be just lots of path algebra
      (a2 ↦
       ¿
Id_eq B1.0 B1.1 B1.2 (eB.0 .to (f0.0 (eA.0 .fro a0))) (eB.1 .to (f0.1 (eA.1 .fro a1))) (eB.2 .to (f0.2 a2)) (f1.0 (eA.0 .to (eA.0 .fro a0))) (f1.1 (eA.1 .to (eA.1 .fro a1)))  (f1.2 (eA.2 .to a2)) (ef.0 (eA.0 .fro a0)) (ef.1 (eA.1 .fro a1)) (ef.2 a2)
 ʔ)
      (s0.2 .id (eA.0 .fro a0) (eA.1 .fro a1))]

{` To build this, we start with a dependent/displayed version of very-surjective. `}
def vsurjᵈ (A B : Type) (f : A → B) (Aᵈ : A → Type) (Bᵈ : B → Type)
  (fᵈ : (x : A) → Aᵈ x → Bᵈ (f x)) (s : vsurj A B f)
  : Type
  ≔ codata [
| t .surj : (b : B) → Bᵈ b → Aᵈ (s .surj b)
| t .surjeq
  : (b : B) (b' : Bᵈ b)
    → Br Bᵈ (s .surjeq b) (fᵈ (s .surj b) (t .surj b b')) b'
| t .id.p
  : (a0 : A.0) (a0' : Aᵈ.0 a0) (a1 : A.1) (a1' : Aᵈ.1 a1)
    → vsurjᵈ (A.2 a0 a1) (B.2 (f.0 a0) (f.1 a1)) (a2 ↦ f.2 a2)
        (a2 ↦ Aᵈ.2 a2 a0' a1') (b2 ↦ Bᵈ.2 b2 (fᵈ.0 a0 a0') (fᵈ.1 a1 a1'))
        (a2 a2' ↦ fᵈ.2 a2 a2') (s.2 .id a0 a1) ]

{` A displayed very-surjective map over a very-surjective one has a very-surjective Σ-map. `}
def vsurjΣ (A B : Type) (f : A → B) (Aᵈ : A → Type) (Bᵈ : B → Type)
  (fᵈ : (x : A) → Aᵈ x → Bᵈ (f x)) (s : vsurj A B f)
  (sᵈ : vsurjᵈ A B f Aᵈ Bᵈ fᵈ s)
  : vsurj (Σ A Aᵈ) (Σ B Bᵈ) (mapΣ A B f Aᵈ Bᵈ fᵈ)
  ≔ [
| .surj ↦ v ↦ (s .surj (v .fst), sᵈ .surj (v .fst) (v .snd))
| .surjeq ↦ v ↦ (s .surjeq (v .fst), sᵈ .surjeq (v .fst) (v .snd))
| .id.p ↦ u0 u1 ↦
    vsurj_eqv
      (Σ (A.2 (u0 .fst) (u1 .fst)) (a2 ↦ Aᵈ.2 a2 (u0 .snd) (u1 .snd)))
      (Σ (B.2 (f.0 (u0 .fst)) (f.1 (u1 .fst)))
         (b2 ↦
          Bᵈ.2 b2 (fᵈ.0 (u0 .fst) (u0 .snd)) (fᵈ.1 (u1 .fst) (u1 .snd))))
      (mapΣ (A.2 (u0 .fst) (u1 .fst)) (B.2 (f.0 (u0 .fst)) (f.1 (u1 .fst)))
         (a2 ↦ f.2 {u0 .fst} {u1 .fst} a2)
         (a2 ↦ Aᵈ.2 a2 (u0 .snd) (u1 .snd))
         (b2 ↦
          Bᵈ.2 b2 (fᵈ.0 (u0 .fst) (u0 .snd)) (fᵈ.1 (u1 .fst) (u1 .snd)))
         (a2 a2' ↦ fᵈ.2 a2 a2')) (Σ⁽ᵖ⁾ A.2 Aᵈ.2 u0 u1)
      (Σ⁽ᵖ⁾ B.2 Bᵈ.2 (mapΣ A.0 B.0 f.0 Aᵈ.0 Bᵈ.0 fᵈ.0 u0)
         (mapΣ A.1 B.1 f.1 Aᵈ.1 Bᵈ.1 fᵈ.1 u1))
      (a2 ↦ rel mapΣ A.2 B.2 f.2 Aᵈ.2 Bᵈ.2 fᵈ.2 a2)
      (id_Σ_iso A.0 A.1 A.2 Aᵈ.0 Aᵈ.1 Aᵈ.2 (u0 .fst) (u1 .fst) (u0 .snd)
         (u1 .snd))
      (id_Σ_iso B.0 B.1 B.2 Bᵈ.0 Bᵈ.1 Bᵈ.2 (f.0 (u0 .fst)) (f.1 (u1 .fst))
         (fᵈ.0 (u0 .fst) (u0 .snd)) (fᵈ.1 (u1 .fst) (u1 .snd))) (u2 ↦ rfl.)
      (vsurjΣ (A.2 (u0 .fst) (u1 .fst))
         (B.2 (f.0 (u0 .fst)) (f.1 (u1 .fst))) (a2 ↦ f.2 a2)
         (a2 ↦ Aᵈ.2 a2 (u0 .snd) (u1 .snd))
         (b2 ↦
          Bᵈ.2 b2 (fᵈ.0 (u0 .fst) (u0 .snd)) (fᵈ.1 (u1 .fst) (u1 .snd)))
         (a2 a2' ↦ fᵈ.2 a2 a2') (s .id (u0 .fst) (u1 .fst))
         (sᵈ .id (u0 .fst) (u0 .snd) (u1 .fst) (u1 .snd)))]


def vsurj_gel (A0 A1 : Type)
  : vsurj (Br Type A0 A1) (A0 → A1 → Type) (A2 ↦ a0 a1 ↦ A2 a0 a1)
  ≔ [
| .surj ↦ A2 ↦ Gel A0 A1 A2
| .surjeq ↦ A2 ↦ a0 a1 ⤇
    Gel (Gel A0 A1 A2 a0.0 a1.0) (A2 a0.1 a1.1)
      (a20 a21 ↦ Br A2 a0.2 a1.2 (a20 .ungel) a21)
| .id.p ↦ A20 A21 ↦ [
  | .surj ↦ A22 ↦
      Gel2 A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 A20 A21
        (a00 a01 a02 a10 a11 a12 a20 a21 ↦ A22 a02 a12 a20 a21)
  | .surjeq ↦ A22 ↦ a0 a1 ⤇
      Gel2 (A20 a0.00 a1.00) (A20 a0.01 a1.01) (Br A20 a0.02 a1.02)
        (A21 a0.10 a1.10) (A21 a0.11 a1.11) (Br A21 a0.12 a1.12)
        (Gel2 A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 A20 A21
           (a00 a01 a02 a10 a11 a12 a20 a21 ↦ A22 a02 a12 a20 a21) a0.20
           a1.20) (A22 a0.21 a1.21)
        (a200 a201 a202 a210 a211 a212 a220 a221 ↦
         Br A22 a0.22 a1.22 a202 a212 (a220 .ungel) a221)
  | .id.p ↦ ¿ʔ]]

`==========================================

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

{`def BrFibRest (A₀ A₁ : Fib) (A₂ : (A₀ .t) → (A₁ .t) → Type) : Type
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
]`}

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
  : Σ A P → Σ B Q
  ≔ ap ↦ (fst ≔ f (ap .fst), snd ≔ g (ap .fst) (ap .snd))

def trr_trl (A₀ A₁ : Fib) (A₂ : Br Fib A₀ A₁) (a₁ : A₁ .t)
  : Br (A₁ .t) a₁ (A₂ .f .trr (A₂ .f .trl a₁))
  ≔ A₂⁽ᵖ⁾
      .f
      .id.2 (A₂ .f .liftl a₁) (A₂ .f .liftr (A₂ .f .trl a₁))
      .trr ((A₂ .f .trl a₁)⁽ᵖ⁾)

def funext (A B : Fib) (f g : A .t → B .t)
  (H : (x : A .t) → Id𝕗 B (f x) (g x) .t)
  : Br (A .t → B .t) f g
  ≔ a ⤇ J A a.0 (a1 a2 ↦ Id𝕗 B (f a.0) (g a1)) (H a.0) a.1 a.2

def blip (A0 A1 : Fib) (A2 : Br Fib A0 A1) (f : A0 .t → A1 .t)
  (H : (x : A0 .t) → Id𝕗 A1 (f x) (A2 .f .trr x) .t)
  : Br Fib A0 A1
  ≔ (
  t ≔ A2 .t,
  f ≔ [
  | .trr.p ⤇ a2 ⤇ A2 .f .trr.2 a2
  | .trr.1 ⤇ f
  | .trl.p ⤇ a2 ⤇ A2 .f .trl.2 a2
  | .trl.1 ⤇ A2 .f .trl
  | .liftr.p ⤇ a2 ⤇ A2 .f .liftr.2 a2
  | .liftr.1 ⤇ a0 ↦ rel A2 .f .id.1 (rel a0) (H a0) .trl (A2 .f .liftr a0)
  | .liftl.p ⤇ a2 ⤇ A2 .f .liftl.2 a2
  | .liftl.1 ⤇ A2 .f .liftl
  | .id.p ⤇ a02 a12 ⤇ A2 .f .id.2 a02 a12
  | .id.1 ⤇ A2 .f .id])

def vsurj_Σ (A B : Type) (f : A → B) (v : vsurj A B f) (P : A → Fib)
  (Q : B → Fib) (r : (a : A) → Br Fib (P a) (Q (f a)))
  : let g : (a : A) (p : P a .t) → Q (f a) .t ≔ a p ↦ r a .f .trr p in
    vsurj (Σ A (a ↦ P a .t)) (Σ B (b ↦ Q b .t))
      (ap ↦ (f (ap .fst), g (ap .fst) (ap .snd)))
  ≔
  let g : (a : A) (p : P a .t) → Q (f a) .t ≔ a p ↦ r a .f .trr p in
  [ .surj ↦ bq ↦
      let b ≔ bq .fst in
      let q ≔ bq .snd in
      (fst ≔ v .surj b,
       snd ≔ r (v .surj b) .f .trl (Q⁽ᵖ⁾ (v .surjeq b) .f .trl q))
  | .surjeq ↦ bq ↦
      let b ≔ bq .fst in
      let q ≔ bq .snd in
      let a ≔ v .surj b in
      let e : Br B (f a) b ≔ v .surjeq b in
      (fst ≔ e,
       snd ≔
         let q₀₀ ≔ Q⁽ᵖ⁾ e .f .trl q in
         let q₀₁ ≔ r a .f .trr (r a .f .trl q₀₀) in
         let q₀₂ ≔ trr_trl (P a) (Q (f a)) (r a) q₀₀ in
         let q₁₀ ≔ q in
         let q₁₁ ≔ q in
         let q₁₂ ≔ q⁽ᵖ⁾ in
         let q₂₁ ≔ Q⁽ᵖ⁾ e .f .liftl q in
         Q⁽ᵖᵖ⁾ (e⁽ᵖ⁾) .f .id.1 q₀₂ q₁₂ .trr q₂₁)
  | .id.p ↦ ap₀ ap₁ ↦
      let a₀ ≔ ap₀ .fst in
      let p₀ ≔ ap₀ .snd in
      let a₁ ≔ ap₁ .fst in
      let p₁ ≔ ap₁ .snd in
      let A₂ ≔ A.2 a₀ a₁ in
      let B₂ ≔ B.2 (f.0 a₀) (f.1 a₁) in
      let f₂ : A₂ → B₂ ≔ a₂ ↦ f.2 a₂ in
      let v₂ : vsurj A₂ B₂ f₂ ≔ v.2 .id a₀ a₁ in
      let Q₂ : B₂ → Fib ≔ b₂ ↦ (
        Q.2 b₂ .t (g.0 a₀ p₀) (g.1 a₁ p₁),
        Q.2 b₂ .f .id (g.0 a₀ p₀) (g.1 a₁ p₁)) in
      let P₂ : A₂ → Fib ≔ a₂ ↦ (P.2 a₂ .t p₀ p₁, P.2 a₂ .f .id p₀ p₁) in
      let r₂ : (a₂ : A₂) → Fib⁽ᵖ⁾ (P₂ a₂) (Q₂ (f₂ a₂))
        ≔ a₂ ↦
          blip (Idd𝕗 (P.0 a₀) (P.1 a₁) (P.2 a₂) p₀ p₁)
            (Idd𝕗 (Q.0 (f.0 a₀)) (Q.1 (f.1 a₁)) (Q.2 (f.2 a₂)) (g.0 a₀ p₀)
               (g.1 a₁ p₁))
            (sym (r.2 a₂) .t (r.0 a₀ .f .liftr p₀) (r.1 a₁ .f .liftr p₁),
             sym (r.2 a₂)
               .f
               .id.1 (r.0 a₀ .f .liftr p₀) (r.1 a₁ .f .liftr p₁))
            (p₂ ↦ g.2 a₂ p₂)
            (p₂ ↦
             rel
                 (sym (r.2 a₂)
                  .f
                  .id.1 (r.0 a₀ .f .liftr p₀) (r.1 a₁ .f .liftr p₁))
             .id.2 (sym (r.2 a₂ .f .liftr.1 p₂))
               (sym (r.2 a₂)
                .f
                .id.1 (r.0 a₀ .f .liftr p₀) (r.1 a₁ .f .liftr p₁)
                .liftr p₂)
             .trr (rel p₂)) in
      let res
        : vsurj (Σ A₂ (a₂ ↦ P₂ a₂ .t)) (Σ B₂ (b₂ ↦ Q₂ b₂ .t))
            (ap₂ ↦ (f₂ (ap₂ .fst), g.2 (ap₂ .fst) (ap₂ .snd)))
        ≔ vsurj_Σ A₂ B₂ f₂ v₂ P₂ Q₂ r₂ in
      vsurj_eqv (Σ A₂ (a₂ ↦ P₂ a₂ .t)) (Σ B₂ (b₂ ↦ Q₂ b₂ .t))
        (ap₂ ↦ (f₂ (ap₂ .fst), g.2 (ap₂ .fst) (ap₂ .snd)))
        (Σ⁽ᵖ⁾ A.2 {a ↦ P.0 a .t} {a ↦ P.1 a .t} (a ⤇ P.2 a.2 .t) ap₀ ap₁)
        (Σ⁽ᵖ⁾ B.2 {b ↦ Q.0 b .t} {b ↦ Q.1 b .t} (b ⤇ Q.2 b.2 .t)
           (f.0 a₀, r.0 a₀ .f .trr p₀) (f.1 a₁, r.1 a₁ .f .trr p₁))
        (a2 ↦ (f.2 (a2 .fst), r.2 (a2 .fst) .f .trr.1 (a2 .snd)))
        (id_Σ_iso A.0 A.1 A.2 (a ↦ P.0 a .t) (a ↦ P.1 a .t)
           (a ⤇ P.2 {a.0} {a.1} a.2 .t) a₀ a₁ p₀ p₁)
        (id_Σ_iso B.0 B.1 B.2 (a ↦ Q.0 a .t) (a ↦ Q.1 a .t)
           (a ⤇ Q.2 {a.0} {a.1} a.2 .t) (f.0 a₀) (f.1 a₁)
           (r.0 a₀ .f .trr p₀) (r.1 a₁ .f .trr p₁)) (ap₂ ↦ rfl.) res]

def BrFibUnfolded (A₀ A₁ : Fib) : Type ≔ sig (
  R : Br Type (A₀ .t) (A₁ .t),
  Rf : (a₀ : A₀ .t) (a₁ : A₁ .t) → isFibrant (R a₀ a₁),
  rest : BrFibRest A₀ A₁ R Rf )

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
            (R₀, p₀) (R₁, p₁)
      ≔ x₂ ↦ f₂ {x₀} {x₁} x₂ in
    let v₀ : vsurj X₀ (Σ (∂₀ .t → Fib) (R ↦ P₀ R .t)) f₀ ≔ u₀ .v in
    let v₁ : vsurj X₁ (Σ (∂₁ .t → Fib) (R ↦ P₁ R .t)) f₁ ≔ u₁ .v in
    let v₂
      : vsurj⁽ᵖ⁾ X₂
          (Σ⁽ᵖ⁾ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t}
             (R ⤇ P₂ R.2 .t)) f₂ v₀ v₁
      ≔ u₂ .v in
    let vg
      : vsurj (X₂ x₀ x₁)
          (Σ⁽ᵖ⁾ (∂₂ .t ⇒ Fib⁽ᵖ⁾) {R ↦ P₀ R .t} {R ↦ P₁ R .t}
             (R ⤇ P₂ R.2 .t) (R₀, p₀) (R₁, p₁)) g
      ≔ v₂ .id.1 x₀ x₁ in
    (∂ ≔ Σ𝕗 ∂₀ (y₀ ↦ Σ𝕗 ∂₁ (y₁ ↦ to𝕗Rel ∂₀ ∂₁ ∂₂ y₀ y₁)),
     P ≔ ¿ʔ,
     f ≔ ¿ʔ,
     v ≔ ¿ʔ)
end



axiom A : Type

def T : Type ≔ codata [ x .des.p : A ]

axiom x : T

echo rel (rel x) .des.1

axiom A : Type
axiom B : Type
axiom F : Br Type A B

axiom a : A
axiom b : B

echo (Gel A B (x y ↦ F x y) a b)

def GelRoundTrip (A B : Type) (F : Br Type A B) (a : A) (b : B)
  : Br Type (F a b) (Gel A B (x y ↦ F x y) a b)
  ≔ Gel (F a b) (Gel A B (x y ↦ F x y) a b)
      (f f' ↦ rel (F a b) f (f' .ungel))

def funExt (A : Type) (P : A → Type) (f g : (x : A) → P x)
  : ((x : A) → Br (P x) (f x) (g x)) → Br ((x : A) → P x) f g
  ≔ p ↦ x ⤇ ¿ʔ

def vsurjFun (A : Type) (P Q : A → Type) (f : (a : A) → P a → Q a)
  (fv : (a : A) → vsurj (P a) (Q a) (f a))
  : vsurj ((x : A) → P x) ((x : A) → Q x) (g x ↦ f x (g x))
  ≔ [
| .surj ↦ g x ↦ fv x .surj (g x)
| .surjeq ↦ g ↦
    funExt A Q (x ↦ f x (fv x .surj (g x))) g (x ↦ fv x .surjeq (g x))
| .id.p ↦ p0 p1 ↦
    ¿vsurjFun (sig (fst : A.0, snd: A.1, thd : A.2 fst snd)) (x ↦ P.2 (x .2) (p0 (x .0)))ʔ]

def P (A₀ A₁ : Fib) (A₂ : Br Type (A₀ .t) (A₁ .t)) : Type
  ≔ Σ ((a₀ : A₀ .t) → (a₁ : A₁ .t) → isFibrant (A₂ a₀ a₁))
      (A₂f ↦ BrFibRest A₀ A₁ A₂ A₂f)

def fiblemma1 (A₀ A₁ : Fib) (A₂ : Br Type (A₀ .t) (A₁ .t))
  : isFibrant (P A₀ A₁ A₂)
  ≔ [
| .trr.p ↦ ¿ʔ
| .trl.p ↦ ¿ʔ
| .liftr.p ↦ ¿ʔ
| .liftl.p ↦ ¿ʔ
| .id.p ↦ ¿ʔ]

def vsurjd_fun (A₀ A₁ : Type) : Br Type A₀ A₁ → A₀ → A₁ → Type
  ≔ A₂ ↦ a₀ a₁ ↦ A₂ a₀ a₁

`def vsurjd_fund (A₀ A₁ : Type) (A₂: Br Type A₀ A₁) (R:A₀ → A₁→ Type) 

def vsurjd_lemma  (A₀ A₁ : Type) : vsurjᵈ (Br Type A₀ A₁) (A₀ → A₁→ Type) (A₂ ↦ a₀ a₁ ↦ A₂ a₀ a₁)
(A₂ ↦ (a₀:A₀)->(a₁:A₁) -> isFibrant (A₂ a₀ a₁))
(R ↦ (a₀:A₀)->(a₁:A₁) -> isFibrant ((Gel A₀ A₁ R) a₀ a₁))
(A₂ ↦ f ↦ a₀ a₁ ↦ f a₀ a₁) (vsurj_gel A₀ A₁) := ?
