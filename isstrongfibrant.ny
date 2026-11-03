{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "fibrant_types"
import "sfib_eq_lemmas"

{` Strong fibrancy is a higher coinductive predicate: an identification of strongly 
fibrant types is a 1-1 correspondence, with contractibility measured by the Martin-Lof 
identity type, and its underlying correspondence is also strongly fibrant. `}
def isStrongFibrant (A : Type) : Type ≔ codata [
| x .trr.p : (a₀ : A.0) → eq.iscontr (Σ A.1 (a₁ ↦ A.2 a₀ a₁))
| x .trl.p : (a₁ : A.1) → eq.iscontr (Σ A.0 (a₀ ↦ A.2 a₀ a₁))
| x .id.p : (a₀ : A.0) (a₁ : A.1) → isStrongFibrant (A.2 a₀ a₁) ]

{` A strongly fibrant type is a type that is strongly fibrant. `}
def SFib : Type ≔ sig ( t : Type, f : isStrongFibrant t )

{` The bridge/identity types of a strongly fibrant type are strongly fibrant. `}
def Id𝕤 (A : SFib) (x y : A .t) : SFib ≔ (Br A .t x y, rel A .f .id x y)

{` Dependent version `}
def Idd𝕤 (A0 A1 : SFib) (A2 : Br SFib A0 A1) (a0 : A0 .t) (a1 : A1 .t)
  : SFib
  ≔ (A2 .t a0 a1, A2 .f .id a0 a1)

{` Any strongly fibrant type is fibrant: transport and lifting are the two components of 
the center of contraction. `}
def issfib_to_isfib (A : Type) (sA : isStrongFibrant A) : isFibrant A ≔ [
| .trr.p ↦ a0 ↦ sA.2 .trr a0 .center .fst
| .trl.p ↦ a1 ↦ sA.2 .trl a1 .center .fst
| .liftr.p ↦ a0 ↦ sA.2 .trr a0 .center .snd
| .liftl.p ↦ a1 ↦ sA.2 .trl a1 .center .snd
| .id.p ↦ a0 a1 ↦ issfib_to_isfib (A.2 a0 a1) (sA.2 .id a0 a1)]

def Fib_of_SFib (A : SFib) : Fib ≔ (A .t, issfib_to_isfib (A .t) (A .f))

{` Basic higher groupoid operations. `}
def stransport (A : Type) (B : A → SFib) (x y : A) (p : Br A x y)
  : B x .t → B y .t
  ≔ b ↦ rel B p .f .trr b .center .fst

{` The lift of a transport. `}
def slift (A : Type) (B : A → SFib) (x y : A) (p : Br A x y) (b : B x .t)
  : Br B p .t b (stransport A B x y p b)
  ≔ rel B p .f .trr b .center .snd

{` Transports and their lifts are unique up to the Martin-Lof identity type. `}
def stransport_uniq (A : Type) (B : A → SFib) (x y : A) (p : Br A x y)
  (b : B x .t) (b' : B y .t) (q : Br B p .t b b')
  : eq (Σ (B y .t) (z ↦ Br B p .t b z)) (b', q)
      (stransport A B x y p b, slift A B x y p b)
  ≔ rel B p .f .trr b .contract (b', q)

def sconcat (A : SFib) (x y z : A .t) (p : Br (A .t) x y)
  (q : Br (A .t) y z)
  : Br (A .t) x z
  ≔ rel (Id𝕤 A x) q .f .trr p .center .fst

def sinverse (A : SFib) (x y : A .t) (p : Br (A .t) x y) : Br (A .t) y x
  ≔ rel ((z ↦ Id𝕤 A z x) : A .t → SFib) p .f .trr (rel x) .center .fst

def stransport2 (A : Type) (B : A → SFib) (x y : A) (p q : Br A x y)
  (r : Br (Br A x y) p q) (b : B x .t)
  : Br (B y .t) (stransport A B x y p b) (stransport A B x y q b)
  ≔ B⁽ᵖᵖ⁾ r
      .f
      .id.2 (slift A B x y p b) (slift A B x y q b)
      .trr (rel b)
      .center
      .fst

{` Uniform higher operations on squares, arising from higher coinductive fields `}
def refl_stransport_1 (A : Type) (B : A → SFib) (x₀₀ x₀₁ : A)
  (x₀₂ : Br A x₀₀ x₀₁) (x₁₀ x₁₁ : A) (x₁₂ : Br A x₁₀ x₁₁)
  (x₂₀ : Br A x₀₀ x₁₀) (x₂₁ : Br A x₀₁ x₁₁)
  (x₂₂ : Br (Br A) x₀₂ x₁₂ x₂₀ x₂₁) (y₀ : B x₀₀ .t) (y₁ : B x₀₁ .t)
  (y₂ : Br B x₀₂ .t y₀ y₁)
  : Br B x₁₂
  .t (stransport A B x₀₀ x₁₀ x₂₀ y₀) (stransport A B x₀₁ x₁₁ x₂₁ y₁)
  ≔ Br (Br B) x₂₂ .f .trr.1 y₂ .center .fst

def refl_stransport_2 (A : Type) (B : A → SFib) (x₀₀ x₀₁ : A)
  (x₀₂ : Br A x₀₀ x₀₁) (x₁₀ x₁₁ : A) (x₁₂ : Br A x₁₀ x₁₁)
  (x₂₀ : Br A x₀₀ x₁₀) (x₂₁ : Br A x₀₁ x₁₁)
  (x₂₂ : Br (Br A) x₀₂ x₁₂ x₂₀ x₂₁) (y₀ : B x₀₀ .t) (y₁ : B x₁₀ .t)
  (y₂ : Br B x₂₀ .t y₀ y₁)
  : Br B x₂₁
  .t (stransport A B x₀₀ x₀₁ x₀₂ y₀) (stransport A B x₁₀ x₁₁ x₁₂ y₁)
  ≔ Br (Br B) x₂₂ .f .trr.2 y₂ .center .fst

{` Two-dimensional globular identity types (which compute to squares with rel on two sides). `}
def Id𝕤2 (A : SFib) (x y : A .t) (p q : Br (A .t) x y) : SFib
  ≔ Id𝕤 (Id𝕤 A x y) p q

{` The right identity law. `}
def sconcat_p1 (A : SFib) (x y : A .t) (p : Br (A .t) x y)
  : Br (Br (A .t) x y) (sconcat A x y y p (rel y)) p
  ≔ sinverse (Id𝕤 A x y) p (sconcat A x y y p (rel y))
      (rel (Id𝕤 A x) (rel y) .f .trr p .center .snd)

{` The Paulin-Möhring identity type eliminator. `}
def sJ (A : SFib) (a : A .t) (P : (y : A .t) → Br (A .t) a y → SFib)
  (pa : P a (rel a) .t) (b : A .t) (p : Br (A .t) a b)
  : P b p .t
  ≔
  let sq ≔ rel (Id𝕤 A a) p .f in
  let q ≔ sq .trr (rel a) .center .fst in
  let s ≔ sq .trr (rel a) .center .snd in
  rel P {a} {b} q {rel a} {p} (sym s) .f .trr pa .center .fst

{` The type of squares in a strongly fibrant type is also strongly fibrant. `}
def Sq𝕤 (A : SFib) (x00 x01 : A .t) (x02 : Br (A .t) x00 x01)
  (x10 x11 : A .t) (x12 : Br (A .t) x10 x11) (x20 : Br (A .t) x00 x10)
  (x21 : Br (A .t) x01 x11)
  : SFib
  ≔ (
  Br (Br A) .t x02 x12 x20 x21,
  Br (Br A) .f .id.1 x02 x12 .id.1 x20 x21)

{` Connection squares. `}
def sconn (A : SFib) (x y : A .t) (p : Br (A .t) x y)
  : Sq𝕤 A x y p y y (rel y) p (rel y) .t
  ≔ sJ A x (z q ↦ Sq𝕤 A x z q z z (rel z) q (rel z)) (rel (rel x)) y p

def scoconn (A : SFib) (x y : A .t) (p : Br (A .t) x y)
  : Sq𝕤 A x x (rel x) x y p (rel x) p .t
  ≔ sJ A x (z q ↦ Sq𝕤 A x x (rel x) x z q (rel x) q) (rel (rel x)) y p

{` The left identity law. `}
def sconcat_1p (A : SFib) (x y : A .t) (p : Br (A .t) x y)
  : Br (Br (A .t) x y) (sconcat A x x y (rel x) p) p
  ≔ rel (Id𝕤2 A x) p (rel (Id𝕤 A x) p .f .trr (rel x) .center .snd)
        (scoconn A x y p)
      .f
      .trr (rel (rel x))
      .center
      .fst

{` Finally, the typal β-rule for the J-eliminator. `}
def sJβ (A : SFib) (a : A .t) (P : (y : A .t) → Br (A .t) a y → SFib)
  (pa : P a (rel a) .t)
  : Br (P a (rel a) .t) pa (sJ A a P pa a (rel a))
  ≔
  let sq ≔ rel (Id𝕤 A a) (rel a) .f .trr (rel a) .center in
  let q ≔ sq .fst in
  let s ≔ sq .snd in
  let cube
    ≔ rel (Sq𝕤 A) (rel a) (rel a) a⁽ᵖᵖ⁾ (rel a) (rel a) s a⁽ᵖᵖ⁾ a⁽ᵖᵖ⁾
        .f
        .trr a⁽ᵖᵖ⁾
        .center in
  let t ≔ cube .fst in
  let c ≔ cube .snd in
  P⁽ᵖᵖ⁾ (sym t) c⁽³²¹⁾
    .f
    .id.2 (rel pa) (rel P q (sym s) .f .trr pa .center .snd)
    .trr (rel pa)
    .center
    .fst

{` Since contractibility in isStrongFibrant is up to the Martin-Lof identity type,
the bridges of a strongly fibrant type are no more than strict equalities. `}

{` A strict equality gives a bridge. `}
def eq.to_Br (X : Type) (x y : X) (e : eq X x y) : Br X x y ≔ match e [
| rfl. ↦ rel x]

{` The based bridge space. `}
def Singl (A : SFib) (a : A .t) : Type ≔ Σ (A .t) (z ↦ Br (A .t) a z)

{` Every based bridge is strictly equal to reflexivity, since both are strictly equal
to the center of contraction. `}
def ssingl (A : SFib) (a b : A .t) (p : Br (A .t) a b)
  : eq (Singl A a) (a, rel a) (b, p)
  ≔
  let c ≔ rel A .f .trr a in
  eq.cat (Singl A a) (a, rel a) (c .center) (b, p) (c .contract (a, rel a))
    (eq.inv (Singl A a) (b, p) (c .center) (c .contract (b, p)))

{` Hence a bridge gives a strict equality. `}
def sbridge_to_eq (A : SFib) (a b : A .t) (p : Br (A .t) a b)
  : eq (A .t) a b
  ≔ eq.ap (Singl A a) (A .t) (u ↦ u .fst) (a, rel a) (b, p)
      (ssingl A a b p)

{` The two round trips are strictly the identity. `}
def sbridge_fro_to (A : SFib) (a b : A .t) (p : Br (A .t) a b)
  : eq (Br (A .t) a b) (eq.to_Br (A .t) a b (sbridge_to_eq A a b p)) p
  ≔
  let aux
    : (u : Singl A a) (e : eq (Singl A a) (a, rel a) u)
      → eq (Br (A .t) a (u .fst))
          (eq.to_Br (A .t) a (u .fst)
             (eq.ap (Singl A a) (A .t) (v ↦ v .fst) (a, rel a) u e))
          (u .snd) ≔ u e ↦ match e [ rfl. ↦ rfl. ] in
  aux (b, p) (ssingl A a b p)

def sbridge_to_fro (A : SFib) (a b : A .t) (e : eq (A .t) a b)
  : eq (eq (A .t) a b) (sbridge_to_eq A a b (eq.to_Br (A .t) a b e)) e
  ≔ match e [
| rfl. ↦
    eq.ap_cat_inv (Singl A a) (A .t) (v ↦ v .fst) (a, rel a)
      (rel A .f .trr a .center) (rel A .f .trr a .contract (a, rel a))]

{` So bridges and strict equalities in a strongly fibrant type are equivalent. `}
def sbridge_eqv_eq (A : SFib) (a b : A .t) : Br (A .t) a b ≅ eq (A .t) a b
  ≔ adjointify (Br (A .t) a b) (eq (A .t) a b) (sbridge_to_eq A a b)
      (eq.to_Br (A .t) a b) (sbridge_fro_to A a b) (sbridge_to_fro A a b)
