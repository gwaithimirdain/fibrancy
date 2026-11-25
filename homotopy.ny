{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "fibrant_types"
import "bookhott"
import "hott_bookhott"

{` Contractibility `}

def isContr (A : Fib) : Type ≔ sig (
  center : A .t,
  contract : (a : A .t) → Br (A .t) a center )

{` Based path spaces are contractible `}
def iscontr_idfrom (A : Fib) (a0 : A .t)
  : isContr (Σ𝕗 A (a1 ↦ Id𝕗 A a0 a1))
  ≔ (
  center ≔ (a0, rel a0),
  contract ≔ a1_a2 ↦
    let a1 ≔ a1_a2 .fst in
    let a2 ≔ a1_a2 .snd in
    (rel ((z ↦ Id𝕗 A z a0) : A .t → Fib) a2 .f .trr (rel a0),
     sym (rel ((z ↦ Id𝕗 A z a0) : A .t → Fib) a2 .f .liftr (rel a0))))

def iscontr_idto (A : Fib) (a1 : A .t) : isContr (Σ𝕗 A (a0 ↦ Id𝕗 A a0 a1))
  ≔ (
  center ≔ (a1, rel a1),
  contract ≔ a0_a2 ↦
    let a0 ≔ a0_a2 .fst in
    let a2 ≔ a0_a2 .snd in
    (a2, conn A a0 a1 a2))

{` More generally, spaces of lifts are contractible `}
def iscontr_liftr (A0 A1 : Fib) (A2 : Br Fib A0 A1) (a0 : A0 .t)
  : isContr (Σ𝕗 A1 (a1 ↦ Idd𝕗 A0 A1 A2 a0 a1))
  ≔ (
  center ≔ (A2 .f .trr a0, A2 .f .liftr a0),
  contract ≔ a12 ↦ (
    rel A2 .f .id.2 (a12 .snd) (A2 .f .liftr a0) .trr (rel a0),
    sym (rel A2 .f .id.2 (a12 .snd) (A2 .f .liftr a0) .liftr (rel a0))))

def iscontr_liftl (A0 A1 : Fib) (A2 : Br Fib A0 A1) (a1 : A1 .t)
  : isContr (Σ𝕗 A0 (a0 ↦ Idd𝕗 A0 A1 A2 a0 a1))
  ≔ (
  center ≔ (A2 .f .trl a1, A2 .f .liftl a1),
  contract ≔ a02 ↦ (
    rel A2 .f .id.2 (a02 .snd) (A2 .f .liftl a1) .trl (rel a1),
    sym (rel A2 .f .id.2 (a02 .snd) (A2 .f .liftl a1) .liftl (rel a1))))

def prop_iscontr (A : Fib) (Ac : isContr A) (x y : A .t) : Br (A .t) x y
  ≔ concat A x (Ac .center) y (Ac .contract x)
      (inverse A y (Ac .center) (Ac .contract y))

{` Any two paths in a contractible space are equal. `}
def eq_iscontr (A : Fib) (Ac : isContr A) (x y : A .t) (p q : Br A .t x y)
  : Br (Br A .t x y) p q
  ≔ sym
        (A⁽ᵖᵖᵖ⁾
         .f
         .id.1 (rel Ac .contract (rel x)) (rel Ac .contract (rel y)))
      .id.1 (sym (rel Ac .contract p)) (sym (rel Ac .contract q))
      .trl (Ac .center)⁽ᵖᵖ⁾

{` Sums of contractible types are contractible `}
def iscontr_Σ (A : Fib) (B : A .t → Fib) (Ac : isContr A)
  (Bc : (a : A .t) → isContr (B a))
  : isContr (Σ𝕗 A B)
  ≔ (
  center ≔ (Ac .center, Bc (Ac .center) .center),
  contract ≔ u ↦ (
    Ac .contract (u .fst),
    rel (Br B (Ac .contract (u .fst)))
      .f
      .id.1 (rel (u .snd))
        (Bc (Ac .center)
         .contract (Br B (Ac .contract (u .fst)) .f .trr (u .snd)))
      .trr (Br B (Ac .contract (u .fst)) .f .liftr (u .snd))))

{` Contractibility transfers to retracts. `}
def iscontr_retract (A B : Fib) (r : A .t → B .t) (s : B .t → A .t)
  (ε : (b : B .t) → Br (B .t) (r (s b)) b) (Ac : isContr A)
  : isContr B
  ≔ (
  center ≔ r (Ac .center),
  contract ≔ b ↦
    concat B b (r (s b)) (r (Ac .center)) (inverse B (r (s b)) b (ε b))
      (rel r (Ac .contract (s b))))

{` The base of a contracible Σ under contractible fibers is contractible. `}
def iscontr_Σbase (A : Fib) (B : A .t → Fib)
  (Bc : (a : A .t) → isContr (B a)) (ABc : isContr (Σ𝕗 A B))
  : isContr A
  ≔ (
  center ≔ ABc .center .fst,
  contract ≔ a ↦ ABc .contract (a, Bc a .center) .fst)

{` The fiber of a contractible Σ over a contractible base is contractible. `}
def iscontr_Σfib (A : Fib) (B : A .t → Fib) (Ac : isContr A)
  (ABc : isContr (Σ𝕗 A B)) (a : A .t)
  : isContr (B a)
  ≔ iscontr_retract (Σ𝕗 A B) (B a)
      (u ↦ Br B (prop_iscontr A Ac (u .0) a) .f .trr (u .1)) (b ↦ (a, b))
      (b ↦
       B⁽ᵖᵖ⁾ (sym (eq_iscontr A Ac a a (prop_iscontr A Ac a a) (rel a)))
       .f
       .id.1 (Br B (prop_iscontr A Ac a a) .f .liftr b) (rel b)
       .trr (rel b)) ABc

{` And likewise for an "inner contractibility" `}
def iscontr_Σmid (A : Fib) (B : A .t → Fib)
  (C : (a : A .t) (b : B a .t) → Fib) (Bc : (a : A .t) → isContr (B a))
  (s : (a : A .t) → B a .t) (ABCc : isContr (Σ𝕗 A (a ↦ Σ𝕗 (B a) (C a))))
  : isContr (Σ𝕗 A (a ↦ C a (s a)))
  ≔ iscontr_retract (Σ𝕗 A (a ↦ Σ𝕗 (B a) (C a))) (Σ𝕗 A (a ↦ C a (s a)))
      (v ↦
       (v .0,
        Br (C (v .0))
            (prop_iscontr (B (v .0)) (Bc (v .0)) (s (v .0)) (v .1 .0))
          .f
          .trl (v .1 .1))) (u ↦ (u .0, (s (u .0), u .1)))
      (u ↦
       (rel (u .0),
        (C (u .0))⁽ᵖᵖ⁾
            (sym
               (eq_iscontr (B (u .0)) (Bc (u .0)) (s (u .0)) (s (u .0))
                  (prop_iscontr (B (u .0)) (Bc (u .0)) (s (u .0))
                     (s (u .0))) (rel (s (u .0)))))
          .f
          .id.1
            (Br (C (u .0))
                 (prop_iscontr (B (u .0)) (Bc (u .0)) (s (u .0)) (s (u .0)))
             .f
             .liftl (u .1)) (rel (u .1))
          .trl (rel (u .1)))) ABCc

{` 1-1 correspondences `}

{` A correspondence is 1-1 if it is unique in both directions. `}
def is11 (A B : Fib) (R : A .t → B .t → Fib) : Type ≔ sig (
  contrr : (a : A .t) → isContr (Σ𝕗 B (b ↦ R a b)),
  contrl : (b : B .t) → isContr (Σ𝕗 A (a ↦ R a b)) )

{` A 1-1 correspondence induces another one on identity types.  This is where the real work of univalence lies. `}
def is11_Id (A0 A1 : Fib) (A2 : Br Fib A0 A1) (B0 B1 : Fib)
  (B2 : Br Fib B0 B1) (R0 : A0 .t → B0 .t → Fib) (re0 : is11 A0 B0 R0)
  (R1 : A1 .t → B1 .t → Fib) (re1 : is11 A1 B1 R1)
  (R2 : Br ((X Y ↦ (X .t → Y .t → Fib)) : (X Y : Fib) → Type) A2 B2 R0 R1)
  (re2 : rel is11 A2 B2 R2 re0 re1) (a0 : A0 .t) (a1 : A1 .t) (b0 : B0 .t)
  (b1 : B1 .t) (r0 : R0 a0 b0 .t) (r1 : R1 a1 b1 .t)
  : is11 (Idd𝕗 A0 A1 A2 a0 a1) (Idd𝕗 B0 B1 B2 b0 b1)
      (a2 b2 ↦ (R2 a2 b2 .t r0 r1, R2 a2 b2 .f .id r0 r1))
  ≔ (
  contrr ≔ a2 ↦
    let S : (y0 : B0 .t) (y1 : B1 .t) → R0 a0 y0 .t → R1 a1 y1 .t → Fib
      ≔ y0 y1 z0 z1 ↦
        Σ𝕗 (Idd𝕗 B0 B1 B2 y0 y1)
          (y2 ↦ Idd𝕗 (R0 a0 y0) (R1 a1 y1) (R2 a2 y2) z0 z1) in
    let b0' : B0 .t ≔ re0 .contrr a0 .center .fst in
    let b1' : B1 .t ≔ re1 .contrr a1 .center .fst in
    let r0' : R0 a0 b0' .t ≔ re0 .contrr a0 .center .snd in
    let r1' : R1 a1 b1' .t ≔ re1 .contrr a1 .center .snd in
    let u : S b0' b1' r0' r1' .t ≔ (
      re2 .contrr a2 .center .fst,
      re2 .contrr a2 .center .snd) in
    let p0 : Br B0 .t b0 b0' ≔ re0 .contrr a0 .contract (b0, r0) .fst in
    let p1 : Br B1 .t b1 b1' ≔ re1 .contrr a1 .contract (b1, r1) .fst in
    let q0 : Br (R0 a0) p0 .t r0 r0'
      ≔ re0 .contrr a0 .contract (b0, r0) .snd in
    let q1 : Br (R1 a1) p1 .t r1 r1'
      ≔ re1 .contrr a1 .contract (b1, r1) .snd in
    (rel S p0 p1 q0 q1 .f .trl u,
     v2 ↦
       let w
         ≔ re2
             .contrr a2
             .contract {(b0, r0)} {(b1, r1)} (v2 .fst, v2 .snd) in
       S⁽ᵖᵖ⁾ (sym (rel p0)) (sym (rel p1)) (sym (rel q0)) (sym (rel q1))
         .f
         .id.1 {v2} {u} (sym w .fst, sym w .snd)
           (rel S p0 p1 q0 q1 .f .liftl u)
         .trl (rel u)),
  contrl ≔ b2 ↦
    let S : (x0 : A0 .t) (x1 : A1 .t) → R0 x0 b0 .t → R1 x1 b1 .t → Fib
      ≔ x0 x1 z0 z1 ↦
        Σ𝕗 (Idd𝕗 A0 A1 A2 x0 x1)
          (x2 ↦ Idd𝕗 (R0 x0 b0) (R1 x1 b1) (R2 x2 b2) z0 z1) in
    let a0' : A0 .t ≔ re0 .contrl b0 .center .fst in
    let a1' : A1 .t ≔ re1 .contrl b1 .center .fst in
    let r0' : R0 a0' b0 .t ≔ re0 .contrl b0 .center .snd in
    let r1' : R1 a1' b1 .t ≔ re1 .contrl b1 .center .snd in
    let u : S a0' a1' r0' r1' .t ≔ (
      re2 .contrl b2 .center .fst,
      re2 .contrl b2 .center .snd) in
    let p0 : Br A0 .t a0 a0' ≔ re0 .contrl b0 .contract (a0, r0) .fst in
    let p1 : Br A1 .t a1 a1' ≔ re1 .contrl b1 .contract (a1, r1) .fst in
    let q0 : Br R0 p0 (rel b0) .t r0 r0'
      ≔ re0 .contrl b0 .contract (a0, r0) .snd in
    let q1 : Br R1 p1 (rel b1) .t r1 r1'
      ≔ re1 .contrl b1 .contract (a1, r1) .snd in
    (rel S p0 p1 q0 q1 .f .trl u,
     v2 ↦
       let w
         ≔ re2
             .contrl b2
             .contract {(a0, r0)} {(a1, r1)} (v2 .fst, v2 .snd) in
       S⁽ᵖᵖ⁾ (sym (rel p0)) (sym (rel p1)) (sym (rel q0)) (sym (rel q1))
         .f
         .id.1 {v2} {u} (sym w .fst, sym w .snd)
           (rel S p0 p1 q0 q1 .f .liftl u)
         .trl (rel u)))

{` Bisimulations `}

{` A bisimulation between types is a bitotal relation that induces another bisimulation on identity types, higher-coinductively. `}
def isBisim (A B : Fib) (R : A .t → B .t → Fib) : Type ≔ codata [
| x .trr : A .t → B .t
| x .liftr : (a : A .t) → R a (x .trr a) .t
| x .trl : B .t → A .t
| x .liftl : (b : B .t) → R (x .trl b) b .t
| x .id.p
  : (a0 : A.0 .t) (b0 : B.0 .t) (r0 : R.0 a0 b0 .t) (a1 : A.1 .t)
    (b1 : B.1 .t) (r1 : R.1 a1 b1 .t)
    → isBisim (A.2 .t a0 a1, A.2 .f .id a0 a1)
        (B.2 .t b0 b1, B.2 .f .id b0 b1)
        (a2 b2 ↦ (R.2 a2 b2 .t r0 r1, R.2 a2 b2 .f .id r0 r1)) ]

{` Any 1-1 correspondence is a bisimulation, because 1-1 correspondences lift to identity types. `}
def bisim_of_11 (A B : Fib) (R : A .t → B .t → Fib) (re : is11 A B R)
  : isBisim A B R
  ≔ [
| .trr ↦ a ↦ re .contrr a .center .fst
| .liftr ↦ a ↦ re .contrr a .center .snd
| .trl ↦ b ↦ re .contrl b .center .fst
| .liftl ↦ b ↦ re .contrl b .center .snd
| .id.p ↦ a0 b0 r0 a1 b1 r1 ↦
    bisim_of_11 (A.2 .t a0 a1, A.2 .f .id a0 a1)
      (B.2 .t b0 b1, B.2 .f .id b0 b1)
      (a2 b2 ↦ (R.2 a2 b2 .t r0 r1, R.2 a2 b2 .f .id r0 r1))
      (is11_Id A.0 A.1 A.2 B.0 B.1 B.2 R.0 re.0 R.1 re.1 R.2 re.2 a0 a1 b0
         b1 r0 r1)]

{` Bisimulations transfer across Book HoTT equivalences. `}
def isbisim_eqv (A B : Fib) (R S : A .t → B .t → Fib)
  (e : (a : A .t) (b : B .t) → R a b .t ≅ S a b .t) (re : isBisim A B R)
  : isBisim A B S
  ≔ [
| .trr ↦ a ↦ re .trr a
| .liftr ↦ a ↦ e a (re .trr a) .to (re .liftr a)
| .trl ↦ b ↦ re .trl b
| .liftl ↦ b ↦ e (re .trl b) b .to (re .liftl b)
| .id.p ↦ a0 b0 s0 a1 b1 s1 ↦
    let r0 ≔ e.0 a0 b0 .fro s0 in
    let r1 ≔ e.1 a1 b1 .fro s1 in
    isbisim_eqv (A.2 .t a0 a1, A.2 .f .id a0 a1)
      (B.2 .t b0 b1, B.2 .f .id b0 b1)
      (a2 b2 ↦ (R.2 a2 b2 .t r0 r1, R.2 a2 b2 .f .id r0 r1))
      (a2 b2 ↦ (S.2 a2 b2 .t s0 s1, S.2 a2 b2 .f .id s0 s1))
      (a2 b2 ↦
       Id_eqv (R.0 a0 b0 .t) (R.1 a1 b1 .t) (R.2 a2 b2 .t) (S.0 a0 b0 .t)
         (S.1 a1 b1 .t) (S.2 a2 b2 .t) (e.0 a0 b0) (e.1 a1 b1) (e.2 a2 b2)
         s0 s1) (re.2 .id a0 b0 r0 a1 b1 r1)]

{` The converse of univalence: any identification of fibrant types is a bisimulation. `}
def bisim_of_Id (A0 A1 : Fib) (A2 : Br Fib A0 A1)
  : isBisim A0 A1 (a0 a1 ↦ Idd𝕗 A0 A1 A2 a0 a1)
  ≔ [
| .trr ↦ A2 .f .trr
| .liftr ↦ A2 .f .liftr
| .trl ↦ A2 .f .trl
| .liftl ↦ A2 .f .liftl
| .id.p ↦ a0 b0 r0 a1 b1 r1 ↦
    isbisim_eqv (A0.2 .t a0 a1, A0.2 .f .id a0 a1)
      (A1.2 .t b0 b1, A1.2 .f .id b0 b1)
      (a2 b2 ↦ (sym A2.2 .t r0 r1 a2 b2, sym A2.2 .f .id.1 r0 r1 .id a2 b2))
      (a2 b2 ↦ (A2.2 .t a2 b2 r0 r1, A2.2 .f .id.1 a2 b2 .id r0 r1))
      (a2 b2 ↦
       sym_eqv (A0.0 .t) (A1.0 .t) (A2.0 .t) (A0.1 .t) (A1.1 .t) (A2.1 .t)
         (A0.2 .t) (A1.2 .t) (sym A2.2 .t) a0 b0 r0 a1 b1 r1 a2 b2)
      (bisim_of_Id (A0.2 .t a0 a1, A0.2 .f .id a0 a1)
         (A1.2 .t b0 b1, A1.2 .f .id b0 b1)
         (sym A2.2 .t r0 r1, sym A2.2 .f .id.1 r0 r1))]
