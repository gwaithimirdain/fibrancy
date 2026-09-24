{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "isstrongfibrant"

{` The strong analogue of fibrant_types.ny: the basic type formers preserve
strong fibrancy. The types themselves, their codes, and the isomorphisms
characterizing their bridge types are those of fibrant_types.ny; only the
fibrancy witnesses are new. `}

{` Contractibility passes to retracts. `}
def eq.iscontr_retract (X Y : Type) (Φ : X → Y) (Ψ : Y → X)
  (r : (y : Y) → eq Y (Φ (Ψ y)) y) (c : eq.iscontr X)
  : eq.iscontr Y
  ≔ (
  center ≔ Φ (c .center),
  contract ≔ y ↦
    eq.cat Y y (Φ (Ψ y)) (Φ (c .center)) (eq.inv Y (Φ (Ψ y)) y (r y))
      (eq.ap X Y Φ (Ψ y) (c .center) (c .contract (Ψ y))))

{` Variants of Id_eq: an Id of equalities induces an equality in the total space
of either variable. `}
def Id_eq_Σr (A0 A1 : Type) (A2 : Br Type A0 A1) (a00 : A0) (a01 : A1)
  (a02 : A2 a00 a01) (a10 : A0) (a11 : A1) (a12 : A2 a10 a11)
  (a20 : eq A0 a00 a10) (a21 : eq A1 a01 a11)
  (a22 : Br eq A2 a02 a12 a20 a21)
  : eq (Σ A1 (x ↦ A2 a10 x))
      (a01, eq.trr A0 (x ↦ A2 x a01) a00 a10 a20 a02) (a11, a12)
  ≔ match a22 [ rfl. ⤇ rfl. ]

def Id_eq_Σl (A0 A1 : Type) (A2 : Br Type A0 A1) (a00 : A0) (a01 : A1)
  (a02 : A2 a00 a01) (a10 : A0) (a11 : A1) (a12 : A2 a10 a11)
  (a20 : eq A0 a00 a10) (a21 : eq A1 a01 a11)
  (a22 : Br eq A2 a02 a12 a20 a21)
  : eq (Σ A0 (x ↦ A2 x a11))
      (a00, eq.trr A1 (x ↦ A2 a00 x) a01 a11 a21 a02) (a10, a12)
  ≔ match a22 [ rfl. ⤇ rfl. ]

{` Just as with fibrancy, to prove that anything is strongly fibrant by
corecursion we need to transport strong fibrancy across Book-HoTT
equivalences. `}
def 𝕤eqv (A B : Type) (e : A ≅ B) (sA : isStrongFibrant A)
  : isStrongFibrant B
  ≔ [
| .trr.p ↦ b0 ↦
    eq.iscontr_retract (Σ A.1 (a1 ↦ A.2 (e.0 .fro b0) a1))
      (Σ B.1 (b1 ↦ B.2 b0 b1))
      (u ↦
       (e.1 .to (u .fst),
        eq.trr B.0 (b ↦ B.2 b (e.1 .to (u .fst))) (e.0 .to (e.0 .fro b0))
          b0 (e.0 .to_fro b0) (e.2 .to (u .snd))))
      (v ↦ (e.1 .fro (v .fst), e.2 .fro (v .snd)))
      (v ↦
       Id_eq_Σr B.0 B.1 B.2 (e.0 .to (e.0 .fro b0))
         (e.1 .to (e.1 .fro (v .fst))) (e.2 .to (e.2 .fro (v .snd))) b0
         (v .fst) (v .snd) (e.0 .to_fro b0) (e.1 .to_fro (v .fst))
         (e.2 .to_fro (v .snd))) (sA.2 .trr (e.0 .fro b0))
| .trl.p ↦ b1 ↦
    eq.iscontr_retract (Σ A.0 (a0 ↦ A.2 a0 (e.1 .fro b1)))
      (Σ B.0 (b0 ↦ B.2 b0 b1))
      (u ↦
       (e.0 .to (u .fst),
        eq.trr B.1 (b ↦ B.2 (e.0 .to (u .fst)) b) (e.1 .to (e.1 .fro b1))
          b1 (e.1 .to_fro b1) (e.2 .to (u .snd))))
      (v ↦ (e.0 .fro (v .fst), e.2 .fro (v .snd)))
      (v ↦
       Id_eq_Σl B.0 B.1 B.2 (e.0 .to (e.0 .fro (v .fst)))
         (e.1 .to (e.1 .fro b1)) (e.2 .to (e.2 .fro (v .snd))) (v .fst) b1
         (v .snd) (e.0 .to_fro (v .fst)) (e.1 .to_fro b1)
         (e.2 .to_fro (v .snd))) (sA.2 .trl (e.1 .fro b1))
| .id.p ↦ b0 b1 ↦
    𝕤eqv (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
      (Id_eqv A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1)
      (sA.2 .id (e.0 .fro b0) (e.1 .fro b1))]

{` The unit type `}

def 𝕤⊤ : isStrongFibrant ⊤ ≔ [
| .trr.p ↦ x ↦ (((), ()), a ↦ rfl.)
| .trl.p ↦ x ↦ (((), ()), a ↦ rfl.)
| .id.p ↦ x y ↦ 𝕤eqv ⊤ (Br ⊤ x y) (id_⊤_iso x y) 𝕤⊤]

def ⊤𝕤 : SFib ≔ (⊤, 𝕤⊤)

{` Product types `}

def 𝕤prod (A B : Type) (𝕤A : isStrongFibrant A) (𝕤B : isStrongFibrant B)
  : isStrongFibrant (A × B)
  ≔ [
| .trr.p ↦ u ↦ (
    ((𝕤A .trr (u .fst) .center .fst, 𝕤B .trr (u .snd) .center .fst),
     (𝕤A .trr (u .fst) .center .snd, 𝕤B .trr (u .snd) .center .snd)),
    v ↦
      eq.ap2 (Σ A.1 (a ↦ A.2 (u .fst) a)) (Σ B.1 (b ↦ B.2 (u .snd) b))
        (Σ (A.1 × B.1) (w ↦ Br prod A.2 B.2 u w))
        (x y ↦ ((x .fst, y .fst), (x .snd, y .snd)))
        (v .fst .fst, v .snd .fst) (𝕤A .trr (u .fst) .center)
        (𝕤A .trr (u .fst) .contract (v .fst .fst, v .snd .fst))
        (v .fst .snd, v .snd .snd) (𝕤B .trr (u .snd) .center)
        (𝕤B .trr (u .snd) .contract (v .fst .snd, v .snd .snd)))
| .trl.p ↦ u ↦ (
    ((𝕤A .trl (u .fst) .center .fst, 𝕤B .trl (u .snd) .center .fst),
     (𝕤A .trl (u .fst) .center .snd, 𝕤B .trl (u .snd) .center .snd)),
    v ↦
      eq.ap2 (Σ A.0 (a ↦ A.2 a (u .fst))) (Σ B.0 (b ↦ B.2 b (u .snd)))
        (Σ (A.0 × B.0) (w ↦ Br prod A.2 B.2 w u))
        (x y ↦ ((x .fst, y .fst), (x .snd, y .snd)))
        (v .fst .fst, v .snd .fst) (𝕤A .trl (u .fst) .center)
        (𝕤A .trl (u .fst) .contract (v .fst .fst, v .snd .fst))
        (v .fst .snd, v .snd .snd) (𝕤B .trl (u .snd) .center)
        (𝕤B .trl (u .snd) .contract (v .fst .snd, v .snd .snd)))
| .id.p ↦ u0 u1 ↦
    𝕤eqv (A.2 (u0 .fst) (u1 .fst) × B.2 (u0 .snd) (u1 .snd))
      (rel prod A.2 B.2 u0 u1)
      (id_prod_iso A.0 A.1 A.2 B.0 B.1 B.2 (u0 .fst) (u1 .fst) (u0 .snd)
         (u1 .snd))
      (𝕤prod (A.2 (u0 .fst) (u1 .fst)) (B.2 (u0 .snd) (u1 .snd))
         (𝕤A .id (u0 .fst) (u1 .fst)) (𝕤B .id (u0 .snd) (u1 .snd)))]

def prod𝕤 (A B : SFib) : SFib ≔ (
  A .t × B .t,
  𝕤prod (A .t) (B .t) (A .f) (B .f))

notation(2) A "×𝕤" B ≔ prod𝕤 A B

{` Σ-types `}

{` A dependent equality into a contractible fiber: any element is equal, over
any equality of the base, to the center. `}
def eqd_contr (X : Type) (F : X → Type) (x c : X) (e : eq X x c) (y : F x)
  (k : eq.iscontr (F c))
  : eqd X F x c e y (k .center)
  ≔ match e [ rfl. ↦ k .contract y ]

{` A Σ-type over a contractible base, whose fiber over the center is
contractible, is contractible. `}
def eq.iscontr_Σ (X : Type) (Q : X → Type) (cX : eq.iscontr X)
  (cQ : eq.iscontr (Q (cX .center)))
  : eq.iscontr (Σ X Q)
  ≔ (
  center ≔ (cX .center, cQ .center),
  contract ≔ w ↦
    ap2d X Q (Σ X Q) (x q ↦ (x, q)) (w .fst) (cX .center)
      (cX .contract (w .fst)) (w .snd) (cQ .center)
      (eqd_contr X Q (w .fst) (cX .center) (cX .contract (w .fst)) (w .snd)
         cQ))

{` The total space of bridges in a Σ-type is, by η, the same as a Σ-type of
total spaces, so this is an instance of eq.iscontr_Σ. For .id, bridges in a
Σ-type are equivalent (id_Σ_iso) to a Σ-type of bridges, which is strongly
fibrant by corecursion. `}
def 𝕤Σ (A : Type) (B : A → Type) (𝕤A : isStrongFibrant A)
  (𝕤B : (x : A) → isStrongFibrant (B x))
  : isStrongFibrant (Σ A B)
  ≔ [
| .trr.p ↦ u ↦
    let SA : Type ≔ Σ A.1 (a ↦ A.2 (u .fst) a) in
    let SB : SA → Type
      ≔ x ↦ Σ (B.1 (x .fst)) (b ↦ B.2 (x .snd) (u .snd) b) in
    let cA ≔ 𝕤A .trr (u .fst) in
    eq.iscontr_retract (Σ SA SB) (Σ (Σ A.1 B.1) (w ↦ Br Σ A.2 B.2 u w))
      (x ↦ ((x .fst .fst, x .snd .fst), (x .fst .snd, x .snd .snd)))
      (v ↦ ((v .fst .fst, v .snd .fst), (v .fst .snd, v .snd .snd)))
      (v ↦ rfl.)
      (eq.iscontr_Σ SA SB cA (𝕤B.2 (cA .center .snd) .trr (u .snd)))
| .trl.p ↦ u ↦
    let SA : Type ≔ Σ A.0 (a ↦ A.2 a (u .fst)) in
    let SB : SA → Type
      ≔ x ↦ Σ (B.0 (x .fst)) (b ↦ B.2 (x .snd) b (u .snd)) in
    let cA ≔ 𝕤A .trl (u .fst) in
    eq.iscontr_retract (Σ SA SB) (Σ (Σ A.0 B.0) (w ↦ Br Σ A.2 B.2 w u))
      (x ↦ ((x .fst .fst, x .snd .fst), (x .fst .snd, x .snd .snd)))
      (v ↦ ((v .fst .fst, v .snd .fst), (v .fst .snd, v .snd .snd)))
      (v ↦ rfl.)
      (eq.iscontr_Σ SA SB cA (𝕤B.2 (cA .center .snd) .trl (u .snd)))
| .id.p ↦ u0 u1 ↦
    𝕤eqv (Σ (A.2 (u0 .fst) (u1 .fst)) (a2 ↦ B.2 a2 (u0 .snd) (u1 .snd)))
      (Br Σ A.2 B.2 u0 u1)
      (id_Σ_iso A.0 A.1 A.2 B.0 B.1 B.2 (u0 .fst) (u1 .fst) (u0 .snd)
         (u1 .snd))
      (𝕤Σ (A.2 (u0 .fst) (u1 .fst)) (a2 ↦ B.2 a2 (u0 .snd) (u1 .snd))
         (𝕤A .id (u0 .fst) (u1 .fst))
         (a2 ↦ 𝕤B.2 a2 .id (u0 .snd) (u1 .snd)))]

{` Strongly fibrant Σ-types `}
def Σ𝕤 (A : SFib) (B : A .t → SFib) : SFib ≔ (
  t ≔ Σ (A .t) (a ↦ B a .t),
  f ≔ 𝕤Σ (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

{` Π-types. Uniqueness of the transported function is an equality of functions,
so this needs funext. `}

{` A Π-type of contractible types is contractible. `}
def eq.iscontr_Π (X : Type) (Y : X → Type) (c : (x : X) → eq.iscontr (Y x))
  : eq.iscontr ((x : X) → Y x)
  ≔ (
  center ≔ x ↦ c x .center,
  contract ≔ f ↦ funext X Y f (x ↦ c x .center) (x ↦ c x .contract (f x)))

{` Transporting the value of a dependent function along an equality of the base
gives its value at the target. `}
def eq.trr_apd (X : Type) (P : X → Type) (k : (x : X) → P x) (x y : X)
  (e : eq X x y)
  : eq (P y) (eq.trr X P x y e (k x)) (k y)
  ≔ match e [ rfl. ↦ rfl. ]

{` If X is contractible, then a Σ-type whose fibers are functions out of X is a
retract of the Σ-type of their values at the center; so it is contractible if
the latter is. `}
def eq.iscontr_ΣΠ (X : Type) (cX : eq.iscontr X) (V : Type)
  (P : X → V → Type) (c : eq.iscontr (Σ V (v ↦ P (cX .center) v)))
  : eq.iscontr (Σ V (v ↦ (x : X) → P x v))
  ≔ eq.iscontr_retract (Σ V (v ↦ P (cX .center) v))
      (Σ V (v ↦ (x : X) → P x v))
      (w ↦
       (w .fst,
        x ↦
          eq.trr X (y ↦ P y (w .fst)) (cX .center) x
            (eq.inv X x (cX .center) (cX .contract x)) (w .snd)))
      (w ↦ (w .fst, w .snd (cX .center)))
      (w ↦
       eq.ap ((x : X) → P x (w .fst)) (Σ V (v ↦ (x : X) → P x v))
         (k ↦ (w .fst, k))
         (x ↦
          eq.trr X (y ↦ P y (w .fst)) (cX .center) x
            (eq.inv X x (cX .center) (cX .contract x))
            (w .snd (cX .center))) (w .snd)
         (funext X (x ↦ P x (w .fst))
            (x ↦
             eq.trr X (y ↦ P y (w .fst)) (cX .center) x
               (eq.inv X x (cX .center) (cX .contract x))
               (w .snd (cX .center))) (w .snd)
            (x ↦
             eq.trr_apd X (y ↦ P y (w .fst)) (w .snd) (cX .center) x
               (eq.inv X x (cX .center) (cX .contract x))))) c

def 𝕤Π (A : Type) (B : A → Type) (𝕤A : isStrongFibrant A)
  (𝕤B : (x : A) → isStrongFibrant (B x))
  : isStrongFibrant ((x : A) → B x)
  ≔ [
| .trr.p ↦ f0 ↦
    eq.iscontr_retract
      ((a1 : A.1)
       → Σ (B.1 a1)
           (b1 ↦
            (u : Σ A.0 (a0 ↦ A.2 a0 a1)) → B.2 (u .snd) (f0 (u .fst)) b1))
      (Σ ((a1 : A.1) → B.1 a1) (f1 ↦ Br Π A.2 B.2 f0 f1))
      (h ↦ (a1 ↦ h a1 .fst, a ⤇ h a.1 .snd (a.0, a.2)))
      (w ↦ a1 ↦ (w .fst a1, u ↦ w .snd (u .snd))) (w ↦ rfl.)
      (eq.iscontr_Π A.1
         (a1 ↦
          Σ (B.1 a1)
            (b1 ↦
             (u : Σ A.0 (a0 ↦ A.2 a0 a1)) → B.2 (u .snd) (f0 (u .fst)) b1))
         (a1 ↦
          eq.iscontr_ΣΠ (Σ A.0 (a0 ↦ A.2 a0 a1)) (𝕤A .trl a1) (B.1 a1)
            (u b1 ↦ B.2 (u .snd) (f0 (u .fst)) b1)
            (𝕤B.2 (𝕤A .trl a1 .center .snd)
             .trr (f0 (𝕤A .trl a1 .center .fst)))))
| .trl.p ↦ f1 ↦
    eq.iscontr_retract
      ((a0 : A.0)
       → Σ (B.0 a0)
           (b0 ↦
            (u : Σ A.1 (a1 ↦ A.2 a0 a1)) → B.2 (u .snd) b0 (f1 (u .fst))))
      (Σ ((a0 : A.0) → B.0 a0) (f0 ↦ Br Π A.2 B.2 f0 f1))
      (h ↦ (a0 ↦ h a0 .fst, a ⤇ h a.0 .snd (a.1, a.2)))
      (w ↦ a0 ↦ (w .fst a0, u ↦ w .snd (u .snd))) (w ↦ rfl.)
      (eq.iscontr_Π A.0
         (a0 ↦
          Σ (B.0 a0)
            (b0 ↦
             (u : Σ A.1 (a1 ↦ A.2 a0 a1)) → B.2 (u .snd) b0 (f1 (u .fst))))
         (a0 ↦
          eq.iscontr_ΣΠ (Σ A.1 (a1 ↦ A.2 a0 a1)) (𝕤A .trr a0) (B.0 a0)
            (u b0 ↦ B.2 (u .snd) b0 (f1 (u .fst)))
            (𝕤B.2 (𝕤A .trr a0 .center .snd)
             .trl (f1 (𝕤A .trr a0 .center .fst)))))
| .id.p ↦ f0 f1 ↦
    𝕤eqv ((a0 : A.0) (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
      (Br Π A.2 B.2 f0 f1) (id_Π_iso A.0 A.1 A.2 B.0 B.1 B.2 f0 f1)
      (𝕤Π A.0 (a0 ↦ (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
         𝕤A.0
         (a0 ↦
          𝕤Π A.1 (a1 ↦ (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1)) 𝕤A.1
            (a1 ↦
             𝕤Π (A.2 a0 a1) (a2 ↦ B.2 a2 (f0 a0) (f1 a1)) (𝕤A.2 .id a0 a1)
               (a2 ↦ 𝕤B.2 a2 .id (f0 a0) (f1 a1)))))]

{` Strongly fibrant Π-types `}
def Π𝕤 (A : SFib) (B : A .t → SFib) : SFib ≔ (
  t ≔ (a : A .t) → B a .t,
  f ≔ 𝕤Π (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

{` Empty type `}

def 𝕤∅ : isStrongFibrant ∅ ≔ [ .trr.p ↦ [ ] | .trl.p ↦ [ ] | .id.p ↦ [ ] ]

def ∅𝕤 : SFib ≔ (∅, 𝕤∅)

{` Gel types `}

def 𝕤Gel (A B : Type) (R : A → B → Type)
  (𝕤R : (a : A) (b : B) → isStrongFibrant (R a b)) (a : A) (b : B)
  : isStrongFibrant (Gel A B R a b)
  ≔ 𝕤eqv (R a b) (Gel A B R a b) (Gel_iso A B R a b) (𝕤R a b)

{` Sum type `}

{` Transport is as for fibrancy: the center of contraction is given by the
corresponding center in A or B. For contractibility, we are given a bridge in
the sum type with one endpoint fixed and the other endpoint variable, and
Narya cannot match on such a bridge directly (it does not refine the variable
endpoint); so we match on the endpoint instead and pass through the codes and
id_sum_iso, whose pointwise data are all that we need. `}
def 𝕤sum (A B : Type) (𝕤A : isStrongFibrant A) (𝕤B : isStrongFibrant B)
  : isStrongFibrant (A ⊔ B)
  ≔ [
| .trr.p ↦ [
  | left. a0 ↦
    ` T: the type we must show contractible, all bridges from left. a0 with a free endpoint





      let T : Type ≔ Σ (A.1 ⊔ B.1) (u1 ↦ Br sum A.2 B.2 (left. a0) u1) in
      ` iso u1: sum_code (left. a0) u1 ≅ Br sum A.2 B.2 (left. a0) u1 (A.2 a0 a1 if u1 = left. a1, ∅ if right)
      let iso ≔ id_sum_iso A.0 A.1 A.2 B.0 B.1 B.2 (left. a0) in
      ` Φ: send the contractible Σ A.1 (A.2 a0) into T by applying left. to the point and the bridge
      let Φ : Σ A.1 (a1 ↦ A.2 a0 a1) → T ≔ w ↦ (
        left. (w .fst),
        left. (w .snd)) in
      ` Ψ: decode a bridge back into A.2 via iso; the right. case is impossible since its code is ∅
      let Ψ
        : (u1 : A.1 ⊔ B.1) → Br sum A.2 B.2 (left. a0) u1
          → Σ A.1 (a1 ↦ A.2 a0 a1) ≔ u1 v ↦ match u1 [
      | left. a1 ↦ (a1, iso (left. a1) .fro v)
      | right. b1 ↦ match (iso (right. b1) .fro v) [ ]] in
      ` r: Φ ∘ Ψ = id on T (via iso's to_fro), so T is a retract of a contractible type
      let r
        : (u1 : A.1 ⊔ B.1) (v : Br sum A.2 B.2 (left. a0) u1)
          → eq T (Φ (Ψ u1 v)) (u1, v) ≔ u1 v ↦ match u1 [
      | left. a1 ↦
          eq.ap (Br sum A.2 B.2 (left. a0) (left. a1)) T
            (x ↦ (left. a1, x)) (left. (iso (left. a1) .fro v)) v
            (iso (left. a1) .to_fro v)
      | right. b1 ↦ match (iso (right. b1) .fro v) [ ]] in
      eq.iscontr_retract (Σ A.1 (a1 ↦ A.2 a0 a1)) T Φ
        (w ↦ Ψ (w .fst) (w .snd)) (w ↦ r (w .fst) (w .snd)) (𝕤A.2 .trr a0)
  | right. b0 ↦
      let T : Type ≔ Σ (A.1 ⊔ B.1) (u1 ↦ Br sum A.2 B.2 (right. b0) u1) in
      let iso ≔ id_sum_iso A.0 A.1 A.2 B.0 B.1 B.2 (right. b0) in
      let Φ : Σ B.1 (b1 ↦ B.2 b0 b1) → T ≔ w ↦ (
        right. (w .fst),
        right. (w .snd)) in
      let Ψ
        : (u1 : A.1 ⊔ B.1) → Br sum A.2 B.2 (right. b0) u1
          → Σ B.1 (b1 ↦ B.2 b0 b1) ≔ u1 v ↦ match u1 [
      | left. a1 ↦ match (iso (left. a1) .fro v) [ ]
      | right. b1 ↦ (b1, iso (right. b1) .fro v)] in
      let r
        : (u1 : A.1 ⊔ B.1) (v : Br sum A.2 B.2 (right. b0) u1)
          → eq T (Φ (Ψ u1 v)) (u1, v) ≔ u1 v ↦ match u1 [
      | left. a1 ↦ match (iso (left. a1) .fro v) [ ]
      | right. b1 ↦
          eq.ap (Br sum A.2 B.2 (right. b0) (right. b1)) T
            (x ↦ (right. b1, x)) (right. (iso (right. b1) .fro v)) v
            (iso (right. b1) .to_fro v)] in
      eq.iscontr_retract (Σ B.1 (b1 ↦ B.2 b0 b1)) T Φ
        (w ↦ Ψ (w .fst) (w .snd)) (w ↦ r (w .fst) (w .snd)) (𝕤B.2 .trr b0)]
| .trl.p ↦ [
  | left. a1 ↦
      let T : Type ≔ Σ (A.0 ⊔ B.0) (u0 ↦ Br sum A.2 B.2 u0 (left. a1)) in
      let iso
        : (u0 : A.0 ⊔ B.0)
          → sum_code A.0 A.1 A.2 B.0 B.1 B.2 u0 (left. a1)
            ≅ Br sum A.2 B.2 u0 (left. a1)
        ≔ u0 ↦ id_sum_iso A.0 A.1 A.2 B.0 B.1 B.2 u0 (left. a1) in
      let Φ : Σ A.0 (a0 ↦ A.2 a0 a1) → T ≔ w ↦ (
        left. (w .fst),
        left. (w .snd)) in
      let Ψ
        : (u0 : A.0 ⊔ B.0) → Br sum A.2 B.2 u0 (left. a1)
          → Σ A.0 (a0 ↦ A.2 a0 a1) ≔ u0 v ↦ match u0 [
      | left. a0 ↦ (a0, iso (left. a0) .fro v)
      | right. b0 ↦ match (iso (right. b0) .fro v) [ ]] in
      let r
        : (u0 : A.0 ⊔ B.0) (v : Br sum A.2 B.2 u0 (left. a1))
          → eq T (Φ (Ψ u0 v)) (u0, v) ≔ u0 v ↦ match u0 [
      | left. a0 ↦
          eq.ap (Br sum A.2 B.2 (left. a0) (left. a1)) T
            (x ↦ (left. a0, x)) (left. (iso (left. a0) .fro v)) v
            (iso (left. a0) .to_fro v)
      | right. b0 ↦ match (iso (right. b0) .fro v) [ ]] in
      eq.iscontr_retract (Σ A.0 (a0 ↦ A.2 a0 a1)) T Φ
        (w ↦ Ψ (w .fst) (w .snd)) (w ↦ r (w .fst) (w .snd)) (𝕤A.2 .trl a1)
  | right. b1 ↦
      let T : Type ≔ Σ (A.0 ⊔ B.0) (u0 ↦ Br sum A.2 B.2 u0 (right. b1)) in
      let iso
        : (u0 : A.0 ⊔ B.0)
          → sum_code A.0 A.1 A.2 B.0 B.1 B.2 u0 (right. b1)
            ≅ Br sum A.2 B.2 u0 (right. b1)
        ≔ u0 ↦ id_sum_iso A.0 A.1 A.2 B.0 B.1 B.2 u0 (right. b1) in
      let Φ : Σ B.0 (b0 ↦ B.2 b0 b1) → T ≔ w ↦ (
        right. (w .fst),
        right. (w .snd)) in
      let Ψ
        : (u0 : A.0 ⊔ B.0) → Br sum A.2 B.2 u0 (right. b1)
          → Σ B.0 (b0 ↦ B.2 b0 b1) ≔ u0 v ↦ match u0 [
      | left. a0 ↦ match (iso (left. a0) .fro v) [ ]
      | right. b0 ↦ (b0, iso (right. b0) .fro v)] in
      let r
        : (u0 : A.0 ⊔ B.0) (v : Br sum A.2 B.2 u0 (right. b1))
          → eq T (Φ (Ψ u0 v)) (u0, v) ≔ u0 v ↦ match u0 [
      | left. a0 ↦ match (iso (left. a0) .fro v) [ ]
      | right. b0 ↦
          eq.ap (Br sum A.2 B.2 (right. b0) (right. b1)) T
            (x ↦ (right. b0, x)) (right. (iso (right. b0) .fro v)) v
            (iso (right. b0) .to_fro v)] in
      eq.iscontr_retract (Σ B.0 (b0 ↦ B.2 b0 b1)) T Φ
        (w ↦ Ψ (w .fst) (w .snd)) (w ↦ r (w .fst) (w .snd)) (𝕤B.2 .trl b1)]
| .id.p ↦ u0 u1 ↦
    let 𝕤code : isStrongFibrant (sum_code A.0 A.1 A.2 B.0 B.1 B.2 u0 u1)
      ≔ match u0, u1 [
    | left. a0, left. a1 ↦ 𝕤A.2 .id a0 a1
    | left. _, right. _ ↦ 𝕤∅
    | right. _, left. _ ↦ 𝕤∅
    | right. b0, right. b1 ↦ 𝕤B.2 .id b0 b1] in
    𝕤eqv (sum_code A.0 A.1 A.2 B.0 B.1 B.2 u0 u1) (Br sum A.2 B.2 u0 u1)
      (id_sum_iso A.0 A.1 A.2 B.0 B.1 B.2 u0 u1) 𝕤code]

{` The natural numbers `}

def 𝕤_ℕ_code (n0 n1 : ℕ) : isStrongFibrant (ℕ_code n0 n1) ≔ match n0, n1 [
| zero., zero. ↦ 𝕤⊤
| zero., suc. n1 ↦ 𝕤∅
| suc. n0, zero. ↦ 𝕤∅
| suc. n0, suc. n1 ↦ 𝕤_ℕ_code n0 n1]

{` Since ℕ has no parameters, its endpoints are variables, so we can match
directly on a bridge in ℕ: by induction on the bridge, every based bridge is
strictly equal to reflexivity. This gives contractibility of the based bridge
spaces without passing through the codes. `}
def ℕ_singl_r (n0 n1 : ℕ) (m : Br ℕ n0 n1)
  : eq (Σ ℕ (n ↦ Br ℕ n0 n)) (n1, m) (n0, rel n0)
  ≔ match m [
| zero. ⤇ rfl.
| suc. k ⤇
    eq.ap (Σ ℕ (n ↦ Br ℕ k.0 n)) (Σ ℕ (n ↦ Br ℕ (suc. k.0) n))
      (w ↦ (suc. (w .fst), suc. (w .snd))) (k.1, k.2) (k.0, rel k.0)
      (ℕ_singl_r k.0 k.1 k.2)]

def ℕ_singl_l (n0 n1 : ℕ) (m : Br ℕ n0 n1)
  : eq (Σ ℕ (n ↦ Br ℕ n n1)) (n0, m) (n1, rel n1)
  ≔ match m [
| zero. ⤇ rfl.
| suc. k ⤇
    eq.ap (Σ ℕ (n ↦ Br ℕ n k.1)) (Σ ℕ (n ↦ Br ℕ n (suc. k.1)))
      (w ↦ (suc. (w .fst), suc. (w .snd))) (k.0, k.2) (k.1, rel k.1)
      (ℕ_singl_l k.0 k.1 k.2)]

def 𝕤ℕ : isStrongFibrant ℕ ≔ [
| .trr.p ↦ n0 ↦ ((n0, rel n0), w ↦ ℕ_singl_r n0 (w .fst) (w .snd))
| .trl.p ↦ n1 ↦ ((n1, rel n1), w ↦ ℕ_singl_l (w .fst) n1 (w .snd))
| .id.p ↦ n0 n1 ↦
    𝕤eqv (ℕ_code n0 n1) (Br ℕ n0 n1) (id_ℕ_iso n0 n1) (𝕤_ℕ_code n0 n1)]

{` TO-DO: W-types, M-Types (soon)`}
