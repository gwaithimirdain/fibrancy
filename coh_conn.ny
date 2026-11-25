{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "bookhott"
import "isfibrant"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"

{` A bridge is left-connectable if it has a left-connection square together with a left-connection cube, and similarly for right-connectable. `}

def lconnectable (A : Type) (a0 a1 : A) (a2 : Br A a0 a1) : Type
  ≔ Σ (A⁽ᵖᵖ⁾ (rel a0) a2 (rel a0) a2)
      (lconn ↦ A⁽ᵖᵖᵖ⁾ a0⁽ᵖᵖ⁾ (sym lconn) a0⁽ᵖᵖ⁾ (sym lconn) a0⁽ᵖᵖ⁾ lconn)

def rconnectable (A : Type) (a0 a1 : A) (a2 : Br A a0 a1) : Type
  ≔ Σ (A⁽ᵖᵖ⁾ a2 (rel a1) a2 (rel a1))
      (rconn ↦ A⁽ᵖᵖᵖ⁾ rconn a1⁽ᵖᵖ⁾ rconn a1⁽ᵖᵖ⁾ rconn a1⁽ᵖᵖ⁾)

{` If the type is fibrant, then so are the types of connectabilities. `}

def 𝕗lconnectable (A : Type) (fA : isFibrant A) (a0 a1 : A)
  (a2 : Br A a0 a1)
  : isFibrant (lconnectable A a0 a1 a2)
  ≔ 𝕗Σ (A⁽ᵖᵖ⁾ (rel a0) a2 (rel a0) a2)
      (lconn ↦ A⁽ᵖᵖᵖ⁾ a0⁽ᵖᵖ⁾ (sym lconn) a0⁽ᵖᵖ⁾ (sym lconn) a0⁽ᵖᵖ⁾ lconn)
      (fA⁽ᵖᵖ⁾ .id.1 (rel a0) a2 .id (rel a0) a2)
      (lconn ↦
       fA⁽ᵖᵖᵖ⁾
       .id.1 a0⁽ᵖᵖ⁾ (sym lconn)
       .id.1 a0⁽ᵖᵖ⁾ (sym lconn)
       .id.1 a0⁽ᵖᵖ⁾ lconn)

def 𝕗rconnectable (A : Type) (fA : isFibrant A) (a0 a1 : A)
  (a2 : Br A a0 a1)
  : isFibrant (rconnectable A a0 a1 a2)
  ≔ 𝕗Σ (A⁽ᵖᵖ⁾ a2 (rel a1) a2 (rel a1))
      (rconn ↦ A⁽ᵖᵖᵖ⁾ rconn a1⁽ᵖᵖ⁾ rconn a1⁽ᵖᵖ⁾ rconn a1⁽ᵖᵖ⁾)
      (fA⁽ᵖᵖ⁾ .id.1 a2 (rel a1) .id a2 (rel a1))
      (rconn ↦
       fA⁽ᵖᵖᵖ⁾ .id.1 rconn a1⁽ᵖᵖ⁾ .id.1 rconn a1⁽ᵖᵖ⁾ .id.1 rconn a1⁽ᵖᵖ⁾)

{` In fact, if the type is fibrant, then the types of connectabilities are actually contractible. `}

def iscontr_lconnectable_isfibrant (A : Type) (fA : isFibrant A)
  (a0 a1 : A) (a2 : Br A a0 a1)
  : isContr (lconnectable A a0 a1 a2, 𝕗lconnectable A fA a0 a1 a2)
  ≔
  let Af : Fib ≔ (A, fA) in
  let Ap0 ≔ Id𝕗 Af a0 a0 in
  let Ap1 ≔ Id𝕗 Af a0 a1 in
  let Ap2 : Br Fib Ap0 Ap1 ≔ (A⁽ᵖᵖ⁾ (rel a0) a2, fA⁽ᵖᵖ⁾ .id.1 (rel a0) a2)
  in
  let App0 : Fib
    ≔ Sq𝕗 Af a0 a0 (rel a0) a0 a0 (rel a0) (rel a0) (rel a0) in
  let App1 : Fib ≔ Sq𝕗 Af a0 a0 (rel a0) a0 a1 a2 (rel a0) a2 in
  let App2
    : (u : Σ𝕗 (Id𝕗 Af a0 a1) (a2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 (rel a0) a2ish) .t)
      → Br Fib App0 App1 ≔ u ↦ (
    A⁽ᵖᵖᵖ⁾ a0⁽ᵖᵖ⁾ (sym (u .1)) a0⁽ᵖᵖ⁾ (sym (u .1)),
    fA⁽ᵖᵖᵖ⁾ .id.1 a0⁽ᵖᵖ⁾ (sym (u .1)) .id.1 a0⁽ᵖᵖ⁾ (sym (u .1))) in
  {` We first expand by adding a contractible space in the middle.  The result is isomorphic to
  sig (
  lconn : A⁽ᵖᵖ⁾ (rel a0) a2 (rel a0) a2,
  a2ish : Br A a0 a1,
  lconnish : A⁽ᵖᵖ⁾ (rel a0) a2 (rel a0) a2ish,
  lcube : A⁽ᵖᵖᵖ⁾ a0⁽ᵖᵖ⁾ (sym lconnish) a0⁽ᵖᵖ⁾ (sym lconnish) a0⁽ᵖᵖ⁾ lconn )
  where (lconn, lcube) become the components of lconnectable if lconnish=lconn, and (a2ish, lconnish) are contractible being a based lifting space.  Note that although the types of (a2ish, lconnish) don't depend on lconn, we can't add them "at the bottom" because we want to contract them away to (a2, lconn). `}
  iscontr_Σmid (Idd𝕗 Ap0 Ap1 Ap2 (rel a0) a2)
    (_ ↦ Σ𝕗 (Id𝕗 Af a0 a1) (a2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 (rel a0) a2ish))
    (lconn u ↦ Idd𝕗 App0 App1 (App2 u) a0⁽ᵖᵖ⁾ lconn)
    (_ ↦ iscontr_liftr Ap0 Ap1 Ap2 (rel a0)) (lconn ↦ (a2, lconn))
    {` Now, however, we can rearrange to put (a2ish, lconnish) at the bottom and (lconn, lcube) at the top, and each of those pairs is separately contractible.  In the latter case, this requires having replaced lconn with lconnish in two places, so that (lconn, lcube) becomes another based lifting space. `}
    (iscontr_retract
       (Σ𝕗 (Σ𝕗 (Id𝕗 Af a0 a1) (a2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 (rel a0) a2ish))
          (u ↦
           Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2 (rel a0) a2)
             (lconn ↦ Idd𝕗 App0 App1 (App2 u) a0⁽ᵖᵖ⁾ lconn)))
       (Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2 (rel a0) a2)
          (lconn ↦
           Σ𝕗 (Σ𝕗 (Id𝕗 Af a0 a1) (a2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 (rel a0) a2ish))
             (u ↦ Idd𝕗 App0 App1 (App2 u) a0⁽ᵖᵖ⁾ lconn)))
       (x ↦ (x .1 .0, (x .0, x .1 .1))) (y ↦ (y .1 .0, (y .0, y .1 .1)))
       (y ↦ rel y)
       (iscontr_Σ
          (Σ𝕗 (Id𝕗 Af a0 a1) (a2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 (rel a0) a2ish))
          (u ↦
           Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2 (rel a0) a2)
             (lconn ↦ Idd𝕗 App0 App1 (App2 u) a0⁽ᵖᵖ⁾ lconn))
          (iscontr_liftr Ap0 Ap1 Ap2 (rel a0))
          (u ↦ iscontr_liftr App0 App1 (App2 u) a0⁽ᵖᵖ⁾)))

{` Thanks to Claude for doing the grunt work in adapting the left case to the right case. `}
def iscontr_rconnectable_isfibrant (A : Type) (fA : isFibrant A)
  (a0 a1 : A) (a2 : Br A a0 a1)
  : isContr (rconnectable A a0 a1 a2, 𝕗rconnectable A fA a0 a1 a2)
  ≔
  let Af : Fib ≔ (A, fA) in
  let Ap0 ≔ Id𝕗 Af a0 a1 in
  let Ap1 ≔ Id𝕗 Af a1 a1 in
  let Ap2 : Br Fib Ap0 Ap1 ≔ (A⁽ᵖᵖ⁾ a2 (rel a1), fA⁽ᵖᵖ⁾ .id.1 a2 (rel a1))
  in
  let App0 : Fib ≔ Sq𝕗 Af a0 a1 a2 a1 a1 (rel a1) a2 (rel a1) in
  let App1 : Fib
    ≔ Sq𝕗 Af a1 a1 (rel a1) a1 a1 (rel a1) (rel a1) (rel a1) in
  let App2
    : (u : Σ𝕗 (Id𝕗 Af a0 a1) (a2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 a2ish (rel a1)) .t)
      → Br Fib App0 App1 ≔ u ↦ (
    A⁽ᵖᵖᵖ⁾ (sym (u .1)) a1⁽ᵖᵖ⁾ (sym (u .1)) a1⁽ᵖᵖ⁾,
    fA⁽ᵖᵖᵖ⁾ .id.1 (sym (u .1)) a1⁽ᵖᵖ⁾ .id.1 (sym (u .1)) a1⁽ᵖᵖ⁾) in
  {` As for lconnectable, we expand by a contractible space in the middle, isomorphic to
  sig (
  rconn : A⁽ᵖᵖ⁾ a2 (rel a1) a2 (rel a1),
  a2ish : Br A a0 a1,
  rconnish : A⁽ᵖᵖ⁾ a2 (rel a1) a2ish (rel a1),
  rcube : A⁽ᵖᵖᵖ⁾ (sym rconnish) a1⁽ᵖᵖ⁾ (sym rconnish) a1⁽ᵖᵖ⁾ rconn a1⁽ᵖᵖ⁾ )
  Now the two occurrences of rconn that we replace share the edge given by the first argument of rconn, so rconnish must vary that edge; since that argument belongs to the bridge of types Ap2 rather than being an endpoint, we vary it in sym rconn instead, and use the section (a2, sym rconn).  Everything else is dual, using left lifting instead of right lifting. `}
  iscontr_Σmid (Idd𝕗 Ap0 Ap1 Ap2 a2 (rel a1))
    (_ ↦ Σ𝕗 (Id𝕗 Af a0 a1) (a2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 a2ish (rel a1)))
    (rconn u ↦ Idd𝕗 App0 App1 (App2 u) rconn a1⁽ᵖᵖ⁾)
    (_ ↦ iscontr_liftl Ap0 Ap1 Ap2 (rel a1)) (rconn ↦ (a2, sym rconn))
    (iscontr_retract
       (Σ𝕗 (Σ𝕗 (Id𝕗 Af a0 a1) (a2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 a2ish (rel a1)))
          (u ↦
           Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2 a2 (rel a1))
             (rconn ↦ Idd𝕗 App0 App1 (App2 u) rconn a1⁽ᵖᵖ⁾)))
       (Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2 a2 (rel a1))
          (rconn ↦
           Σ𝕗 (Σ𝕗 (Id𝕗 Af a0 a1) (a2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 a2ish (rel a1)))
             (u ↦ Idd𝕗 App0 App1 (App2 u) rconn a1⁽ᵖᵖ⁾)))
       (x ↦ (x .1 .0, (x .0, x .1 .1))) (y ↦ (y .1 .0, (y .0, y .1 .1)))
       (y ↦ rel y)
       (iscontr_Σ
          (Σ𝕗 (Id𝕗 Af a0 a1) (a2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 a2ish (rel a1)))
          (u ↦
           Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2 a2 (rel a1))
             (rconn ↦ Idd𝕗 App0 App1 (App2 u) rconn a1⁽ᵖᵖ⁾))
          (iscontr_liftl Ap0 Ap1 Ap2 (rel a1))
          (u ↦ iscontr_liftl App0 App1 (App2 u) a1⁽ᵖᵖ⁾)))

{` A type has connections if all its bridges are both left and right connectable. `}

def connectable (A : Type) (a0 a1 : A) (a2 : Br A a0 a1) : Type ≔ sig (
  lconn : lconnectable A a0 a1 a2,
  rconn : rconnectable A a0 a1 a2 )

def hasConn (A : Type) : Type
  ≔ (a0 a1 : A) (a2 : Br A a0 a1) → connectable A a0 a1 a2

{` In particular, therefore, fibrant types have connections. `}

def hasconn_isfibrant (A : Type) (fA : isFibrant A) : hasConn A
  ≔ a0 a1 a2 ↦ (
  lconn ≔ iscontr_lconnectable_isfibrant A fA a0 a1 a2 .center,
  rconn ≔ iscontr_rconnectable_isfibrant A fA a0 a1 a2 .center)

{` As do "conditionally fibrant" types. `}

def hasconn_condfib (A : Type) (fA : A → isFibrant A) : hasConn A
  ≔ a0 a1 a2 ↦ (
  lconn ≔ iscontr_lconnectable_isfibrant A (fA a0) a0 a1 a2 .center,
  rconn ≔ iscontr_rconnectable_isfibrant A (fA a0) a0 a1 a2 .center)

{` Total bridge spaces preserve types with connections. `}

def hasconn_totBr (A : Type) (c : hasConn A)
  : hasConn (Σ (A × A) (u ↦ Br A (u .0) (u .1)))
  ≔ a0 a1 a2 ↦ (
  lconn ≔ (
    ((c (a0 .0 .0) (a1 .0 .0) (a2 .0 .0) .lconn .0,
      c (a0 .0 .1) (a1 .0 .1) (a2 .0 .1) .lconn .0),
     (rel c (a0 .1) (a1 .1) (sym (a2 .1)) .lconn .0)⁽³¹²⁾),
    ((c (a0 .0 .0) (a1 .0 .0) (a2 .0 .0) .lconn .1,
      c (a0 .0 .1) (a1 .0 .1) (a2 .0 .1) .lconn .1),
     (rel c (a0 .1) (a1 .1) (sym (a2 .1)) .lconn .1)⁽⁴¹²³⁾)),
  rconn ≔ (
    ((c (a0 .0 .0) (a1 .0 .0) (a2 .0 .0) .rconn .0,
      c (a0 .0 .1) (a1 .0 .1) (a2 .0 .1) .rconn .0),
     (rel c (a0 .1) (a1 .1) (sym (a2 .1)) .rconn .0)⁽³¹²⁾),
    ((c (a0 .0 .0) (a1 .0 .0) (a2 .0 .0) .rconn .1,
      c (a0 .0 .1) (a1 .0 .1) (a2 .0 .1) .rconn .1),
     (rel c (a0 .1) (a1 .1) (sym (a2 .1)) .rconn .1)⁽⁴¹²³⁾)))

{` Dependent versions of connectability: given a type family B over A and connection data in A, the dependent connection squares and cubes in B over it. (Claude) `}

def lconnectableᵈ (A : Type) (B : A → Type) (x0 x1 : A) (x2 : Br A x0 x1)
  (sc : lconnectable A x0 x1 x2) (b0 : B x0) (b1 : B x1)
  (b2 : rel B x2 b0 b1)
  : Type
  ≔ Σ (B⁽ᵖᵖ⁾ (sc .0) (rel b0) b2 (rel b0) b2)
      (t ↦ B⁽ᵖᵖᵖ⁾ (sc .1) b0⁽ᵖᵖ⁾ (sym t) b0⁽ᵖᵖ⁾ (sym t) b0⁽ᵖᵖ⁾ t)

def rconnectableᵈ (A : Type) (B : A → Type) (x0 x1 : A) (x2 : Br A x0 x1)
  (sc : rconnectable A x0 x1 x2) (b0 : B x0) (b1 : B x1)
  (b2 : rel B x2 b0 b1)
  : Type
  ≔ Σ (B⁽ᵖᵖ⁾ (sc .0) b2 (rel b1) b2 (rel b1))
      (t ↦ B⁽ᵖᵖᵖ⁾ (sc .1) t b1⁽ᵖᵖ⁾ t b1⁽ᵖᵖ⁾ t b1⁽ᵖᵖ⁾)

def 𝕗lconnectableᵈ (A : Type) (B : A → Type)
  (fB : (x : A) → isFibrant (B x)) (x0 x1 : A) (x2 : Br A x0 x1)
  (sc : lconnectable A x0 x1 x2) (b0 : B x0) (b1 : B x1)
  (b2 : rel B x2 b0 b1)
  : isFibrant (lconnectableᵈ A B x0 x1 x2 sc b0 b1 b2)
  ≔ 𝕗Σ (B⁽ᵖᵖ⁾ (sc .0) (rel b0) b2 (rel b0) b2)
      (t ↦ B⁽ᵖᵖᵖ⁾ (sc .1) b0⁽ᵖᵖ⁾ (sym t) b0⁽ᵖᵖ⁾ (sym t) b0⁽ᵖᵖ⁾ t)
      (fB⁽ᵖᵖ⁾ (sc .0) .id.1 (rel b0) b2 .id (rel b0) b2)
      (t ↦
       fB⁽ᵖᵖᵖ⁾ (sc .1)
       .id.1 b0⁽ᵖᵖ⁾ (sym t)
       .id.1 b0⁽ᵖᵖ⁾ (sym t)
       .id.1 b0⁽ᵖᵖ⁾ t)

def 𝕗rconnectableᵈ (A : Type) (B : A → Type)
  (fB : (x : A) → isFibrant (B x)) (x0 x1 : A) (x2 : Br A x0 x1)
  (sc : rconnectable A x0 x1 x2) (b0 : B x0) (b1 : B x1)
  (b2 : rel B x2 b0 b1)
  : isFibrant (rconnectableᵈ A B x0 x1 x2 sc b0 b1 b2)
  ≔ 𝕗Σ (B⁽ᵖᵖ⁾ (sc .0) b2 (rel b1) b2 (rel b1))
      (t ↦ B⁽ᵖᵖᵖ⁾ (sc .1) t b1⁽ᵖᵖ⁾ t b1⁽ᵖᵖ⁾ t b1⁽ᵖᵖ⁾)
      (fB⁽ᵖᵖ⁾ (sc .0) .id.1 b2 (rel b1) .id b2 (rel b1))
      (t ↦ fB⁽ᵖᵖᵖ⁾ (sc .1) .id.1 t b1⁽ᵖᵖ⁾ .id.1 t b1⁽ᵖᵖ⁾ .id.1 t b1⁽ᵖᵖ⁾)

{` If the family is fibrant, the dependent connectabilities are contractible, by the same argument as in the non-dependent case.  Importantly, the *base* type does not need to be fibrant.  (Claude) `}

def iscontr_lconnectableᵈ_isfibrant (A : Type) (B : A → Type)
  (fB : (x : A) → isFibrant (B x)) (x0 x1 : A) (x2 : Br A x0 x1)
  (sc : lconnectable A x0 x1 x2) (b0 : B x0) (b1 : B x1)
  (b2 : rel B x2 b0 b1)
  : isContr
      (lconnectableᵈ A B x0 x1 x2 sc b0 b1 b2,
       𝕗lconnectableᵈ A B fB x0 x1 x2 sc b0 b1 b2)
  ≔
  let s ≔ sc .0 in
  let c ≔ sc .1 in
  let Ap0 ≔ Id𝕗 (B x0, fB x0) b0 b0 in
  let Ap1 : Fib ≔ (rel B x2 b0 b1, rel fB x2 .id b0 b1) in
  let Ap2 : Br Fib Ap0 Ap1 ≔ (
    B⁽ᵖᵖ⁾ s (rel b0) b2,
    fB⁽ᵖᵖ⁾ s .id.1 (rel b0) b2) in
  let App0 : Fib ≔ (
    B⁽ᵖᵖ⁾ x0⁽ᵖᵖ⁾ (rel b0) (rel b0) (rel b0) (rel b0),
    fB⁽ᵖᵖ⁾ x0⁽ᵖᵖ⁾ .id.1 (rel b0) (rel b0) .id (rel b0) (rel b0)) in
  let App1 : Fib ≔ Idd𝕗 Ap0 Ap1 Ap2 (rel b0) b2 in
  let App2
    : (u : Σ𝕗 Ap1 (b2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 (rel b0) b2ish) .t)
      → Br Fib App0 App1 ≔ u ↦ (
    B⁽ᵖᵖᵖ⁾ c b0⁽ᵖᵖ⁾ (sym (u .1)) b0⁽ᵖᵖ⁾ (sym (u .1)),
    fB⁽ᵖᵖᵖ⁾ c .id.1 b0⁽ᵖᵖ⁾ (sym (u .1)) .id.1 b0⁽ᵖᵖ⁾ (sym (u .1))) in
  iscontr_Σmid (Idd𝕗 Ap0 Ap1 Ap2 (rel b0) b2)
    (_ ↦ Σ𝕗 Ap1 (b2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 (rel b0) b2ish))
    (t u ↦ Idd𝕗 App0 App1 (App2 u) b0⁽ᵖᵖ⁾ t)
    (_ ↦ iscontr_liftr Ap0 Ap1 Ap2 (rel b0)) (t ↦ (b2, t))
    (iscontr_retract
       (Σ𝕗 (Σ𝕗 Ap1 (b2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 (rel b0) b2ish))
          (u ↦
           Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2 (rel b0) b2)
             (t ↦ Idd𝕗 App0 App1 (App2 u) b0⁽ᵖᵖ⁾ t)))
       (Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2 (rel b0) b2)
          (t ↦
           Σ𝕗 (Σ𝕗 Ap1 (b2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 (rel b0) b2ish))
             (u ↦ Idd𝕗 App0 App1 (App2 u) b0⁽ᵖᵖ⁾ t)))
       (x ↦ (x .1 .0, (x .0, x .1 .1))) (y ↦ (y .1 .0, (y .0, y .1 .1)))
       (y ↦ rel y)
       (iscontr_Σ (Σ𝕗 Ap1 (b2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 (rel b0) b2ish))
          (u ↦
           Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2 (rel b0) b2)
             (t ↦ Idd𝕗 App0 App1 (App2 u) b0⁽ᵖᵖ⁾ t))
          (iscontr_liftr Ap0 Ap1 Ap2 (rel b0))
          (u ↦ iscontr_liftr App0 App1 (App2 u) b0⁽ᵖᵖ⁾)))

{` In the right-hand case, unlike the non-dependent one, the two faces of the cube that we replace lie over the square s itself rather than its symmetry, so the varying square must lie over sym s; thus we need a second bridge of types Ap2, distinct from the bridge Ap2s that the dependent connection square lies over. `}

def iscontr_rconnectableᵈ_isfibrant (A : Type) (B : A → Type)
  (fB : (x : A) → isFibrant (B x)) (x0 x1 : A) (x2 : Br A x0 x1)
  (sc : rconnectable A x0 x1 x2) (b0 : B x0) (b1 : B x1)
  (b2 : rel B x2 b0 b1)
  : isContr
      (rconnectableᵈ A B x0 x1 x2 sc b0 b1 b2,
       𝕗rconnectableᵈ A B fB x0 x1 x2 sc b0 b1 b2)
  ≔
  let s ≔ sc .0 in
  let c ≔ sc .1 in
  let Ap0 : Fib ≔ (rel B x2 b0 b1, rel fB x2 .id b0 b1) in
  let Ap1 ≔ Id𝕗 (B x1, fB x1) b1 b1 in
  let Ap2s : Br Fib Ap0 Ap1 ≔ (
    B⁽ᵖᵖ⁾ s b2 (rel b1),
    fB⁽ᵖᵖ⁾ s .id.1 b2 (rel b1)) in
  let Ap2 : Br Fib Ap0 Ap1 ≔ (
    B⁽ᵖᵖ⁾ (sym s) b2 (rel b1),
    fB⁽ᵖᵖ⁾ (sym s) .id.1 b2 (rel b1)) in
  let App0 : Fib ≔ Idd𝕗 Ap0 Ap1 Ap2s b2 (rel b1) in
  let App1 : Fib ≔ (
    B⁽ᵖᵖ⁾ x1⁽ᵖᵖ⁾ (rel b1) (rel b1) (rel b1) (rel b1),
    fB⁽ᵖᵖ⁾ x1⁽ᵖᵖ⁾ .id.1 (rel b1) (rel b1) .id (rel b1) (rel b1)) in
  let App2
    : (u : Σ𝕗 Ap0 (b2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 b2ish (rel b1)) .t)
      → Br Fib App0 App1 ≔ u ↦ (
    B⁽ᵖᵖᵖ⁾ c (sym (u .1)) b1⁽ᵖᵖ⁾ (sym (u .1)) b1⁽ᵖᵖ⁾,
    fB⁽ᵖᵖᵖ⁾ c .id.1 (sym (u .1)) b1⁽ᵖᵖ⁾ .id.1 (sym (u .1)) b1⁽ᵖᵖ⁾) in
  iscontr_Σmid (Idd𝕗 Ap0 Ap1 Ap2s b2 (rel b1))
    (_ ↦ Σ𝕗 Ap0 (b2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 b2ish (rel b1)))
    (t u ↦ Idd𝕗 App0 App1 (App2 u) t b1⁽ᵖᵖ⁾)
    (_ ↦ iscontr_liftl Ap0 Ap1 Ap2 (rel b1)) (t ↦ (b2, sym t))
    (iscontr_retract
       (Σ𝕗 (Σ𝕗 Ap0 (b2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 b2ish (rel b1)))
          (u ↦
           Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2s b2 (rel b1))
             (t ↦ Idd𝕗 App0 App1 (App2 u) t b1⁽ᵖᵖ⁾)))
       (Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2s b2 (rel b1))
          (t ↦
           Σ𝕗 (Σ𝕗 Ap0 (b2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 b2ish (rel b1)))
             (u ↦ Idd𝕗 App0 App1 (App2 u) t b1⁽ᵖᵖ⁾)))
       (x ↦ (x .1 .0, (x .0, x .1 .1))) (y ↦ (y .1 .0, (y .0, y .1 .1)))
       (y ↦ rel y)
       (iscontr_Σ (Σ𝕗 Ap0 (b2ish ↦ Idd𝕗 Ap0 Ap1 Ap2 b2ish (rel b1)))
          (u ↦
           Σ𝕗 (Idd𝕗 Ap0 Ap1 Ap2s b2 (rel b1))
             (t ↦ Idd𝕗 App0 App1 (App2 u) t b1⁽ᵖᵖ⁾))
          (iscontr_liftl Ap0 Ap1 Ap2 (rel b1))
          (u ↦ iscontr_liftl App0 App1 (App2 u) b1⁽ᵖᵖ⁾)))

{` The Σ of a fibrant family over a type with connections has connections.  This is analogous to the proof that connectability in a fibrant type is contractible: we build the corresponding types of dependent cubes in B over the connection data of A and show that it is contractible, hence in particular inhabited. `}
def hasconn_Σfib (A : Type) (B : A → Type) (cA : hasConn A)
  (fB : (x : A) → isFibrant (B x))
  : hasConn (Σ A B)
  ≔ a0 a1 a2 ↦
  let cx ≔ cA (a0 .fst) (a1 .fst) (a2 .fst) in
  let l
    ≔ iscontr_lconnectableᵈ_isfibrant A B fB (a0 .fst) (a1 .fst) (a2 .fst)
        (cx .lconn) (a0 .snd) (a1 .snd) (a2 .snd) .center in
  let r
    ≔ iscontr_rconnectableᵈ_isfibrant A B fB (a0 .fst) (a1 .fst) (a2 .fst)
        (cx .rconn) (a0 .snd) (a1 .snd) (a2 .snd) .center in
  (lconn ≔ ((cx .lconn .0, l .0), (cx .lconn .1, l .1)),
   rconn ≔ ((cx .rconn .0, r .0), (cx .rconn .1, r .1)))

{` Functions preserve connectability. `}
def ap_connectable (A B : Type) (f : A → B) (a0 a1 : A) (a2 : Br A a0 a1)
  (c : connectable A a0 a1 a2)
  : connectable B (f a0) (f a1) (rel f a2)
  ≔ (
  lconn ≔ (f⁽ᵖᵖ⁾ (c .lconn .0), f⁽ᵖᵖᵖ⁾ (c .lconn .1)),
  rconn ≔ (f⁽ᵖᵖ⁾ (c .rconn .0), f⁽ᵖᵖᵖ⁾ (c .rconn .1)))

{` Transporting connectability along outer equalities of endpoints. `}
def trr2_connectable (B : Type) (x0 x1 : B) (x2 : eq B x0 x1) (y0 y1 : B)
  (y2 : eq B y0 y1) (p : Br B x0 y0) (c : connectable B x0 y0 p)
  : connectable B x1 y1 (eq.trr2 B B (x y ↦ Br B x y) x0 x1 x2 y0 y1 y2 p)
  ≔ match x2, y2 [ rfl., rfl. ↦ c ]

{` Having connections is preserved by isomorphisms: we pull a bridge back to A, take its connections there, push them forward to B, and transport them back along the counit, using the outer equality between the transported bridge and the original one induced by the bridge of the counit. `}
def hasconn_eqv (A B : Type) (e : A ≅ B) (cA : hasConn A) : hasConn B
  ≔ b0 b1 b2 ↦
  let f ≔ e .to in
  let g ≔ e .fro in
  let fg : B → B ≔ x ↦ f (g x) in
  let ε ≔ e .to_fro in
  eq.trr (Br B b0 b1) (p ↦ connectable B b0 b1 p)
    (eq.trr2 B B (x y ↦ Br B x y) (fg b0) b0 (ε b0) (fg b1) b1 (ε b1)
       (rel fg b2)) b2
    (Id_eq B B (Br B) (fg b0) (fg b1) (rel fg b2) b0 b1 b2 (ε b0) (ε b1)
       (rel ε b2))
    (trr2_connectable B (fg b0) b0 (ε b0) (fg b1) b1 (ε b1) (rel fg b2)
       (ap_connectable A B f (g b0) (g b1) (rel g b2)
          (cA (g b0) (g b1) (rel g b2))))

{` The universe of non-fibrant types has connections.  Because it is not fibrant, its type of connections is not contractible, and in particular it has many different inhabitants, most of them trivial or uninteresting.  Here we give it an "interesting" connection structure, which should in particular lift to (the unique) connection structure on Fib.  `}
def hasconn_Type : hasConn Type ≔ A0 A1 A2 ↦ (
  lconn ≔ (
    {` We need to fill a square in which two *adjacent* sides are heterogeneous and the other two homogeneous.  We do this by giving a homogeneous diagonal bridge together with a homogeneous triangle (square with one side degenerate) and a heterogeneous triangle.  `}
    sig (
      a .bridge : Br A0 a.10 a.01,
      a .homog : Br (Br A0) a.02 (a .bridge) a.20 (rel a.01),
      a .heter : Br A2 (a .bridge) (rel a.11) a.12 a.21 ),
    {` Now we need to fill a cube in which three of the squares are "mixed heterogeneous" cut by a diagonal bridge, as above.  Those three diagonal bridges together can be thought of as slicing off one corner of the cube, leaving a solid with three square faces and four triangle faces: three right triangles that are the homogeneous triangles from the decomposed faces, and one equilateral triangle formed by the newly added bridges.  The solid that was cut off is a triangular prism with that bridge-triangle as base and the other three sides the heterogeneous triangles. `}
    sig (
    {` Here is the bridge-triangle. `}
      a .triangle : Br (Br A0) (rel a.101) (sym a.212 .bridge)
                      (a.221 .bridge) (sym a.122 .bridge),
    {` And here is the heterogeneous triangular prism, which is easy to represent as a cube with two degenerate sides. `}
      a .heter : A2⁽ᵖᵖ⁾ (a .triangle) a.111⁽ᵖᵖ⁾ (rel a.121)
                   (sym a.212 .heter) (a.221 .heter) (sym a.122 .heter),
    {` The cube with one corner sliced off can't be represented as a single cube.  We slice it again along a square that incorporates two of the diagonal bridges and the two original edges adjacent to the other diagonal bridge.  (Thanks to Claude for working out this decomposition, with some hints.) `}
      a .square : Br (Br A0) a.021 (sym a.122 .bridge) a.201
                    (sym a.212 .bridge),
    {` What's left after we slice that off can be represented as a cube with one degenerate edge, adjacent to two of the homogeneous triangles. `}
      a .homog : A0⁽ᵖᵖᵖ⁾ a.022 (sym (sym a.122 .homog)) a.202
                   (sym (sym a.212 .homog)) a.220 (a .square),
    {` The remaining piece is a "pillow" that composes the bridge-triangle with the third homogeneous triangle to make the slicing square.  This is a cube with some degenerate faces, but one of those faces has to be a connection square.  Our type A doesn't necessarily have all connections, but we can just assert that one of its bridges is connectable, since in the fibrant case this assertion will be contractible. `}
      a .212bconn : lconnectable A0 a.011 a.110 (sym a.212 .bridge),
      a .pillow : A0⁽ᵖᵖᵖ⁾ (rel a.021) (a .triangle) (rel a.201)
                    (a .212bconn .0) (a.221 .homog) (a .square) )),
  rconn ≔ (
    sig (
      a .bridge : Br A1 a.01 a.10,
      a .heter : Br A2 (rel a.00) (a .bridge) a.02 a.20,
      a .homog : Br (Br A1) (rel a.01) a.12 (a .bridge) a.21 ),
    sig (
      a .triangle : Br (Br A1) (a.022 .bridge) (rel a.100) (a.202 .bridge)
                      (a.220 .bridge),
      a .heter : A2⁽ᵖᵖ⁾ a.000⁽ᵖᵖ⁾ (a .triangle) (a.022 .heter) (rel a.200)
                   (a.202 .heter) (a.220 .heter),
      a .square : Br (Br A1) (a.022 .bridge) a.120 (a.202 .bridge) a.210,
      a .homog : A1⁽ᵖᵖᵖ⁾ (a.022 .homog) a.122 (a.202 .homog) a.212
                   (a .square) a.221,
      a .022bconn : rconnectable A1 a.001 a.010 (a.022 .bridge),
      a .pillow : A1⁽ᵖᵖᵖ⁾ (a .022bconn .0) (rel a.120) (a .triangle)
                    (rel a.210) (a .square) (a.220 .homog) )))
