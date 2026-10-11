{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "isstrongfibrant"
import "strongfibrant_types"

{` Strict equality types are strongly fibrant `}
def 𝕤eq (A : SFib) (x y : A .t) : isStrongFibrant (eq (A .t) x y)
  ≔ 𝕤eqv (Br (A .t) x y) (eq (A .t) x y) (sbridge_eqv_eq A x y)
      (rel A .f .id x y)

def eq𝕤 (A : SFib) (x y : A .t) : SFib ≔ (eq (A .t) x y, 𝕤eq A x y)

{` Strong analogue of isBisim in homotopy.ny. 
  Could be defined without strong fibrancy. `}
def isSBisim (A B : SFib) (R : A .t → B .t → SFib) : Type ≔ codata [
| x .contrr : (a : A .t) → eq.iscontr (Σ (B .t) (b ↦ R a b .t))
| x .contrl : (b : B .t) → eq.iscontr (Σ (A .t) (a ↦ R a b .t))
| x .id.p
  : (a0 : A.0 .t) (b0 : B.0 .t) (r0 : R.0 a0 b0 .t) (a1 : A.1 .t)
    (b1 : B.1 .t) (r1 : R.1 a1 b1 .t)
    → isSBisim (Idd𝕤 A.0 A.1 A.2 a0 a1) (Idd𝕤 B.0 B.1 B.2 b0 b1)
        (a2 b2 ↦ Idd𝕤 (R.0 a0 b0) (R.1 a1 b1) (R.2 a2 b2) r0 r1) ]

{` Strong analogue of isbisim_eqv in homotopy.ny. 
  Could be proved without strong fibrancy. `}
def isSBisim_eqv (A B : SFib) (R S : A .t → B .t → SFib)
  (e : (a : A .t) (b : B .t) → R a b .t ≅ S a b .t) (re : isSBisim A B R)
  : isSBisim A B S
  ≔ [
| .contrr ↦ a ↦
    eq.iscontr_retract (Σ (B .t) (b ↦ R a b .t)) (Σ (B .t) (b ↦ S a b .t))
      (u ↦ (u .fst, e a (u .fst) .to (u .snd)))
      (v ↦ (v .fst, e a (v .fst) .fro (v .snd)))
      (v ↦
       eq.ap (S a (v .fst) .t) (Σ (B .t) (b ↦ S a b .t)) (z ↦ (v .fst, z))
         (e a (v .fst) .to (e a (v .fst) .fro (v .snd))) (v .snd)
         (e a (v .fst) .to_fro (v .snd))) (re .contrr a)
| .contrl ↦ b ↦
    eq.iscontr_retract (Σ (A .t) (a ↦ R a b .t)) (Σ (A .t) (a ↦ S a b .t))
      (u ↦ (u .fst, e (u .fst) b .to (u .snd)))
      (v ↦ (v .fst, e (v .fst) b .fro (v .snd)))
      (v ↦
       eq.ap (S (v .fst) b .t) (Σ (A .t) (a ↦ S a b .t)) (z ↦ (v .fst, z))
         (e (v .fst) b .to (e (v .fst) b .fro (v .snd))) (v .snd)
         (e (v .fst) b .to_fro (v .snd))) (re .contrl b)
| .id.p ↦ a0 b0 s0 a1 b1 s1 ↦
    let r0 ≔ e.0 a0 b0 .fro s0 in
    let r1 ≔ e.1 a1 b1 .fro s1 in
    isSBisim_eqv (Idd𝕤 A.0 A.1 A.2 a0 a1) (Idd𝕤 B.0 B.1 B.2 b0 b1)
      (a2 b2 ↦ Idd𝕤 (R.0 a0 b0) (R.1 a1 b1) (R.2 a2 b2) r0 r1)
      (a2 b2 ↦ Idd𝕤 (S.0 a0 b0) (S.1 a1 b1) (S.2 a2 b2) s0 s1)
      (a2 b2 ↦
       Id_eqv (R.0 a0 b0 .t) (R.1 a1 b1 .t) (R.2 a2 b2 .t) (S.0 a0 b0 .t)
         (S.1 a1 b1 .t) (S.2 a2 b2 .t) (e.0 a0 b0) (e.1 a1 b1) (e.2 a2 b2)
         s0 s1) (re.2 .id a0 b0 r0 a1 b1 r1)]

{` If the transport of u2 along p0 and p1 equals c2, 
then the square with sides p0, p1, u2, c2 is filled over X2. `}
def Br_eq_of_eq (X0 X1 : Type) (X2 : Br Type X0 X1) (u0 c0 : X0)
  (p0 : eq X0 u0 c0) (u1 c1 : X1) (p1 : eq X1 u1 c1) (u2 : X2 u0 u1)
  (c2 : X2 c0 c1)
  (h : eq (X2 c0 c1) (eq.trr2 X0 X1 (x y ↦ X2 x y) u0 c0 p0 u1 c1 p1 u2) c2)
  : Br eq X2 u2 c2 p0 p1
  ≔ match p0, p1 [ rfl., rfl. ↦ match h [ rfl. ↦ rfl. ] ]

{` If X0 and X1 are contractible, and the fiber of X2 over their centers is
contractible, then the two contractions are related by a bridge over X2. `}
def Br_iscontr (X0 X1 : Type) (X2 : Br Type X0 X1) (c0 : eq.iscontr X0)
  (c1 : eq.iscontr X1) (k : eq.iscontr (X2 (c0 .center) (c1 .center)))
  : Br eq.iscontr X2 c0 c1
  ≔ (
  center ≔ k .center,
  contract ≔ u ⤇
    Br_eq_of_eq X0 X1 X2 u.0 (c0 .center) (c0 .contract u.0) u.1
      (c1 .center) (c1 .contract u.1) u.2 (k .center)
      (k .contract
         (eq.trr2 X0 X1 (x y ↦ X2 x y) u.0 (c0 .center) (c0 .contract u.0)
            u.1 (c1 .center) (c1 .contract u.1) u.2)))

{` Strong analogue of pre_univalence `}
def spre_univalence (A B : SFib) (G : Br Type (A .t) (B .t))
  (𝕤G : (a : A .t) (b : B .t) → isStrongFibrant (G a b))
  (re : isSBisim A B (x y ↦ (G x y, 𝕤G x y)))
  : Br isStrongFibrant G (A .f) (B .f)
  ≔ [
| .trr.1 ↦ a ↦ re .contrr a
| .trl.1 ↦ b ↦ re .contrl b
| .id.1 ↦ a b ↦ 𝕤G a b
| .trr.p ↦ {a0} {b0} r0 ↦
    let ca ≔ A.2 .f .trr a0 .center in
    let cb ≔ B.2 .f .trr b0 .center in
    Br_iscontr (Σ (A.1 .t) (a1 ↦ A.2 .t a0 a1))
      (Σ (B.1 .t) (b1 ↦ B.2 .t b0 b1))
      (Σ⁽ᵖ⁾ G.1 {a1 ↦ A.2 .t a0 a1} {b1 ↦ B.2 .t b0 b1}
         (x ⤇ sym G.2 r0 x.2)) (A.2 .f .trr a0) (B.2 .f .trr b0)
      (eq.iscontr_retract
         (Σ (G.1 (ca .fst) (cb .fst)) (g1 ↦ G.2 (ca .snd) (cb .snd) r0 g1))
         (Σ⁽ᵖ⁾ G.1 {a1 ↦ A.2 .t a0 a1} {b1 ↦ B.2 .t b0 b1}
            (x ⤇ sym G.2 r0 x.2) ca cb) (u ↦ (u .fst, sym (u .snd)))
         (v ↦ (v .fst, sym (v .snd))) (v ↦ rfl.)
         (𝕤G.2 (ca .snd) (cb .snd) .trr r0))
| .trl.p ↦ {a1} {b1} r1 ↦
    let ca ≔ A.2 .f .trl a1 .center in
    let cb ≔ B.2 .f .trl b1 .center in
    Br_iscontr (Σ (A.0 .t) (a0 ↦ A.2 .t a0 a1))
      (Σ (B.0 .t) (b0 ↦ B.2 .t b0 b1))
      (Σ⁽ᵖ⁾ G.0 {a0 ↦ A.2 .t a0 a1} {b0 ↦ B.2 .t b0 b1}
         (x ⤇ sym G.2 x.2 r1)) (A.2 .f .trl a1) (B.2 .f .trl b1)
      (eq.iscontr_retract
         (Σ (G.0 (ca .fst) (cb .fst)) (g0 ↦ G.2 (ca .snd) (cb .snd) g0 r1))
         (Σ⁽ᵖ⁾ G.0 {a0 ↦ A.2 .t a0 a1} {b0 ↦ B.2 .t b0 b1}
            (x ⤇ sym G.2 x.2 r1) ca cb) (u ↦ (u .fst, sym (u .snd)))
         (v ↦ (v .fst, sym (v .snd))) (v ↦ rfl.)
         (𝕤G.2 (ca .snd) (cb .snd) .trl r1))
| .id.p ↦ {a0} {b0} r0 {a1} {b1} r1 ↦
    let s
      : (a2 : A.2 .t a0 a1) (b2 : B.2 .t b0 b1)
        → G.2 a2 b2 r0 r1 ≅ sym G.2 r0 r1 a2 b2
      ≔ a2 b2 ↦
        sym_eqv (A.0 .t) (A.1 .t) (A.2 .t) (B.0 .t) (B.1 .t) (B.2 .t) G.0
          G.1 G.2 a0 a1 a2 b0 b1 b2 r0 r1 in
    let 𝕤sG
      : (a2 : A.2 .t a0 a1) (b2 : B.2 .t b0 b1)
        → isStrongFibrant (sym G.2 r0 r1 a2 b2)
      ≔ a2 b2 ↦
        𝕤eqv (G.2 a2 b2 r0 r1) (sym G.2 r0 r1 a2 b2) (s a2 b2)
          (𝕤G.2 a2 b2 .id r0 r1) in
    spre_univalence (Idd𝕤 A.0 A.1 A.2 a0 a1) (Idd𝕤 B.0 B.1 B.2 b0 b1)
      (sym G.2 r0 r1) 𝕤sG
      (isSBisim_eqv (Idd𝕤 A.0 A.1 A.2 a0 a1) (Idd𝕤 B.0 B.1 B.2 b0 b1)
         (a2 b2 ↦ (G.2 a2 b2 r0 r1, 𝕤G.2 a2 b2 .id r0 r1))
         (a2 b2 ↦ (sym G.2 r0 r1 a2 b2, 𝕤sG a2 b2)) s
         (re.2 .id a0 b0 r0 a1 b1 r1))]

def sunivalence (A B : SFib) (R : A .t → B .t → SFib) (re : isSBisim A B R)
  : Br SFib A B
  ≔
  let Rt : A .t → B .t → Type ≔ x y ↦ R x y .t in
  let Rf : (a : A .t) (b : B .t) → isStrongFibrant (Rt a b)
    ≔ x y ↦ R x y .f in
  (Gel (A .t) (B .t) Rt,
   spre_univalence A B (Gel (A .t) (B .t) Rt)
     (a b ↦ 𝕤Gel (A .t) (B .t) Rt Rf a b)
     (isSBisim_eqv A B (x y ↦ R x y)
        (a b ↦ (Gel (A .t) (B .t) Rt a b, 𝕤Gel (A .t) (B .t) Rt Rf a b))
        (a b ↦ Gel_iso (A .t) (B .t) Rt a b) re))

def Id_eq_rfl (A0 A1 : Type) (A2 : Br Type A0 A1) (a00 a01 : A0)
  (a02 : eq A0 a00 a01) (a10 a11 : A1) (a12 : eq A1 a10 a11)
  (a20 : A2 a00 a10) (a21 : A2 a01 a11)
  : eq (A2 a00 a10) a20
      (eq.trl2 A0 A1 (a0 a1 ↦ A2 a0 a1) a00 a01 a02 a10 a11 a12 a21)
    ≅ Br eq A2 a20 a21 a02 a12
  ≔ (
  to ≔ a22 ↦ match a02, a12, a22 [ rfl., rfl., rfl. ↦ rfl. ],
  fro ≔ [ rfl. ⤇ rfl. ],
  fro_to ≔ a22 ↦ match a02, a12, a22 [ rfl., rfl., rfl. ↦ rfl. ],
  to_fro ≔ [ rfl. ⤇ rfl. ],
  to_fro_to ≔ a22 ↦ match a02, a12, a22 [ rfl., rfl., rfl. ↦ rfl. ])

def based_contr (X : Type) (x y : X) (r : eq X x y)
  : eq (Σ X (z ↦ eq X x z)) (y, r) (x, rfl.)
  ≔ match r [ rfl. ↦ rfl. ]

def ap_singl (X Y : Type) (g : X → Y) (x y : X) (p : eq X x y)
  : eq (Σ X (z ↦ eq Y (g z) (g y))) (y, rfl.) (x, eq.ap X Y g x y p)
  ≔ match p [ rfl. ↦ rfl. ]

def fro_contr (A B : Type) (e : A ≅ B) (a : A) (b : B)
  (r : eq A (e .fro b) a)
  : eq (Σ B (b' ↦ eq A (e .fro b') a)) (b, r) (e .to a, e .fro_to a)
  ≔ match r [
| rfl. ↦
    eq.cat (Σ B (b' ↦ eq A (e .fro b') (e .fro b))) (b, rfl.)
      (e .to (e .fro b),
       eq.ap B A (e .fro) (e .to (e .fro b)) b (e .to_fro b))
      (e .to (e .fro b), e .fro_to (e .fro b))
      (ap_singl B A (e .fro) (e .to (e .fro b)) b (e .to_fro b))
      (eq.ap (eq A (e .fro (e .to (e .fro b))) (e .fro b))
         (Σ B (b' ↦ eq A (e .fro b') (e .fro b)))
         (q ↦ (e .to (e .fro b), q))
         (eq.ap B A (e .fro) (e .to (e .fro b)) b (e .to_fro b))
         (e .fro_to (e .fro b)) (fro_to_fro A B e b))]

{` An isomorphism gives a strong bisimulation. 
  Could be proved without strong fibrancy. `}
def isSBisim_of_iso (A B : SFib) (e : A .t ≅ B .t)
  : isSBisim A B (a b ↦ eq𝕤 A (e .fro b) a)
  ≔ [
| .contrr ↦ a ↦ (
    (e .to a, e .fro_to a),
    u ↦ fro_contr (A .t) (B .t) e a (u .fst) (u .snd))
| .contrl ↦ b ↦ (
    (e .fro b, rfl.),
    u ↦ based_contr (A .t) (e .fro b) (u .fst) (u .snd))
| .id.p ↦ a0 b0 r0 a1 b1 r1 ↦ match r0, r1 [
  | rfl., rfl. ↦
      isSBisim_eqv (Idd𝕤 A.0 A.1 A.2 (e.0 .fro b0) (e.1 .fro b1))
        (Idd𝕤 B.0 B.1 B.2 b0 b1)
        (a2 b2 ↦
         eq𝕤 (Idd𝕤 A.0 A.1 A.2 (e.0 .fro b0) (e.1 .fro b1))
           (Id_eqv (A.0 .t) (A.1 .t) (A.2 .t) (B.0 .t) (B.1 .t) (B.2 .t)
                e.0 e.1 e.2 b0 b1
            .fro b2) a2)
        (a2 b2 ↦
         Idd𝕤 (eq𝕤 A.0 (e.0 .fro b0) (e.0 .fro b0))
           (eq𝕤 A.1 (e.1 .fro b1) (e.1 .fro b1))
           (rel eq𝕤 A.2 (e.2 .fro b2) a2) rfl. rfl.)
        (a2 b2 ↦
         Id_eq_rfl (A.0 .t) (A.1 .t) (A.2 .t) (e.0 .fro b0) (e.0 .fro b0)
           rfl. (e.1 .fro b1) (e.1 .fro b1) rfl. (e.2 .fro b2) a2)
        (isSBisim_of_iso (Idd𝕤 A.0 A.1 A.2 (e.0 .fro b0) (e.1 .fro b1))
           (Idd𝕤 B.0 B.1 B.2 b0 b1)
           (Id_eqv (A.0 .t) (A.1 .t) (A.2 .t) (B.0 .t) (B.1 .t) (B.2 .t)
              e.0 e.1 e.2 b0 b1))]]

{` The negation automorphism of Bool gives a bridge in SFib that differs from
rel Bool𝕤. If SFib were strongly fibrant, this bridge would become a nontrivial
strict loop. Hence, if strict equality on SFib satisfies UIP, then SFib is not
strongly fibrant. `}
def Bool : Type ≔ ⊤ ⊔ ⊤

def true : Bool ≔ left. ()

def false : Bool ≔ right. ()

def 𝕤Bool : isStrongFibrant Bool ≔ 𝕤sum ⊤ ⊤ 𝕤⊤ 𝕤⊤

def Bool𝕤 : SFib ≔ (Bool, 𝕤Bool)

def neg : Bool → Bool ≔ [ left. _ ↦ right. () | right. _ ↦ left. () ]

def neg_neg (b : Bool) : eq Bool (neg (neg b)) b ≔ match b [
| left. _ ↦ rfl.
| right. _ ↦ rfl.]

def neg_iso : Bool ≅ Bool
  ≔ adjointify Bool Bool neg neg neg_neg neg_neg

def neg_bridge : Br SFib Bool𝕤 Bool𝕤
  ≔ sunivalence Bool𝕤 Bool𝕤 (a b ↦ eq𝕤 Bool𝕤 (neg_iso .fro b) a)
      (isSBisim_of_iso Bool𝕤 Bool𝕤 neg_iso)

{` Transporting true along a bridge distinguishes the two bridges: rel Bool𝕤
sends it to true and neg_bridge to false, both by rfl. Used in rel_neq_neg. `}
def trr_true (p : Br SFib Bool𝕤 Bool𝕤) : Bool ≔ p .f .trr true .center .fst

def trr_true_rel : eq Bool (trr_true (rel Bool𝕤)) true ≔ rfl.

def trr_true_neg : eq Bool (trr_true neg_bridge) false ≔ rfl.

def isTrue : Bool → Type ≔ [ left. _ ↦ ⊤ | right. _ ↦ ∅ ]

def true_neq_false (e : eq Bool true false) : ∅
  ≔ eq.trr Bool isTrue true false e ()

def rel_neq_neg (e : eq (Br SFib Bool𝕤 Bool𝕤) (rel Bool𝕤) neg_bridge) : ∅
  ≔ true_neq_false
      (eq.ap (Br SFib Bool𝕤 Bool𝕤) Bool trr_true (rel Bool𝕤) neg_bridge e)

def sfib_contr (s : isStrongFibrant SFib) (A : SFib)
  : eq.iscontr (Σ SFib (B ↦ Br SFib A B))
  ≔ rel s .trr A

def strict_univalence (s : isStrongFibrant SFib) (A B : SFib)
  : Br SFib A B ≅ eq SFib A B
  ≔ sbridge_eqv_eq (SFib, s) A B

def neg_loop (s : isStrongFibrant SFib) : eq SFib Bool𝕤 Bool𝕤
  ≔ sbridge_to_eq (SFib, s) Bool𝕤 Bool𝕤 neg_bridge

def neg_loop_to_Br (s : isStrongFibrant SFib)
  : eq (Br SFib Bool𝕤 Bool𝕤) (eq.to_Br SFib Bool𝕤 Bool𝕤 (neg_loop s))
      neg_bridge
  ≔ sbridge_fro_to (SFib, s) Bool𝕤 Bool𝕤 neg_bridge

def neg_loop_nontrivial (s : isStrongFibrant SFib)
  (k : eq (eq SFib Bool𝕤 Bool𝕤) (neg_loop s) rfl.)
  : ∅
  ≔ rel_neq_neg
      (eq.cat (Br SFib Bool𝕤 Bool𝕤) (rel Bool𝕤)
         (eq.to_Br SFib Bool𝕤 Bool𝕤 (neg_loop s)) neg_bridge
         (eq.inv (Br SFib Bool𝕤 Bool𝕤)
            (eq.to_Br SFib Bool𝕤 Bool𝕤 (neg_loop s)) (rel Bool𝕤)
            (eq.ap (eq SFib Bool𝕤 Bool𝕤) (Br SFib Bool𝕤 Bool𝕤)
               (eq.to_Br SFib Bool𝕤 Bool𝕤) (neg_loop s) rfl. k))
         (neg_loop_to_Br s))

def UIP_SFib : Type
  ≔ (A B : SFib) (p q : eq SFib A B) → eq (eq SFib A B) p q

def uip_not_sfib (u : UIP_SFib) (s : isStrongFibrant SFib) : ∅
  ≔ neg_loop_nontrivial s (u Bool𝕤 Bool𝕤 (neg_loop s) rfl.)
