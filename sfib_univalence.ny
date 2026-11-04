{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "isstrongfibrant"
import "sfib_types"
import "sfib_eq_lemmas"

{` Strict equality types are strongly fibrant `}
def 𝕤eq (A : SFib) (x y : A .t) : isStrongFibrant (eq (A .t) x y)
  ≔ 𝕤eqv (Br (A .t) x y) (eq (A .t) x y) (sbridge_eqv_eq A x y)
      (rel A .f .id x y)

def eq𝕤 (A : SFib) (x y : A .t) : SFib ≔ (eq (A .t) x y, 𝕤eq A x y)

{` Strong analogue of isBisim in bisim.ny: lifts are unique up to eq. `}
def isBisim (A B : Type) (R : A → B → Type) : Type ≔ codata [
| x .contrr : (a : A) → eq.iscontr (Σ B (b ↦ R a b))
| x .contrl : (b : B) → eq.iscontr (Σ A (a ↦ R a b))
| x .id.p
  : (a0 : A.0) (b0 : B.0) (r0 : R.0 a0 b0) (a1 : A.1) (b1 : B.1)
    (r1 : R.1 a1 b1)
    → isBisim (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ R.2 a2 b2 r0 r1) ]

{` Strong analogue of isBisim_eqv_overid in bisim.ny. `}
def isBisim_eqv (A B : Type) (R S : A → B → Type)
  (e : (a : A) (b : B) → R a b ≅ S a b) (re : isBisim A B R)
  : isBisim A B S
  ≔ [
| .contrr ↦ a ↦
    eq.iscontr_retract (Σ B (b ↦ R a b)) (Σ B (b ↦ S a b))
      (u ↦ (u .fst, e a (u .fst) .to (u .snd)))
      (v ↦ (v .fst, e a (v .fst) .fro (v .snd)))
      (v ↦
       eq.ap (S a (v .fst)) (Σ B (b ↦ S a b)) (z ↦ (v .fst, z))
         (e a (v .fst) .to (e a (v .fst) .fro (v .snd))) (v .snd)
         (e a (v .fst) .to_fro (v .snd))) (re .contrr a)
| .contrl ↦ b ↦
    eq.iscontr_retract (Σ A (a ↦ R a b)) (Σ A (a ↦ S a b))
      (u ↦ (u .fst, e (u .fst) b .to (u .snd)))
      (v ↦ (v .fst, e (v .fst) b .fro (v .snd)))
      (v ↦
       eq.ap (S (v .fst) b) (Σ A (a ↦ S a b)) (z ↦ (v .fst, z))
         (e (v .fst) b .to (e (v .fst) b .fro (v .snd))) (v .snd)
         (e (v .fst) b .to_fro (v .snd))) (re .contrl b)
| .id.p ↦ a0 b0 s0 a1 b1 s1 ↦
    let r0 ≔ e.0 a0 b0 .fro s0 in
    let r1 ≔ e.1 a1 b1 .fro s1 in
    isBisim_eqv (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ R.2 a2 b2 r0 r1)
      (a2 b2 ↦ S.2 a2 b2 s0 s1)
      (a2 b2 ↦
       Id_eqv (R.0 a0 b0) (R.1 a1 b1) (R.2 a2 b2) (S.0 a0 b0) (S.1 a1 b1)
         (S.2 a2 b2) (e.0 a0 b0) (e.1 a1 b1) (e.2 a2 b2) s0 s1)
      (re.2 .id a0 b0 r0 a1 b1 r1)]

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
  (re : isBisim (A .t) (B .t) (x y ↦ G x y))
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
      (isBisim_eqv (A.2 .t a0 a1) (B.2 .t b0 b1) (a2 b2 ↦ G.2 a2 b2 r0 r1)
         (a2 b2 ↦ sym G.2 r0 r1 a2 b2) s (re.2 .id a0 b0 r0 a1 b1 r1))]

def sunivalence (A B : SFib) (R : A .t → B .t → SFib)
  (re : isBisim (A .t) (B .t) (x y ↦ R x y .t))
  : Br SFib A B
  ≔
  let Rt : A .t → B .t → Type ≔ x y ↦ R x y .t in
  let Rf : (a : A .t) (b : B .t) → isStrongFibrant (Rt a b)
    ≔ x y ↦ R x y .f in
  (Gel (A .t) (B .t) Rt,
   spre_univalence A B (Gel (A .t) (B .t) Rt)
     (a b ↦ 𝕤Gel (A .t) (B .t) Rt Rf a b)
     (isBisim_eqv (A .t) (B .t) Rt (a b ↦ Gel (A .t) (B .t) Rt a b)
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

{` Strong analogue of isBisim_≅ in bisim.ny. `}
def isBisim_of_iso (A B : Type) (e : A ≅ B)
  : isBisim A B (a b ↦ eq A (e .fro b) a)
  ≔ [
| .contrr ↦ a ↦ (
    (e .to a, e .fro_to a),
    u ↦ fro_contr A B e a (u .fst) (u .snd))
| .contrl ↦ b ↦ (
    (e .fro b, rfl.),
    u ↦ based_contr A (e .fro b) (u .fst) (u .snd))
| .id.p ↦ a0 b0 r0 a1 b1 r1 ↦ match r0, r1 [
  | rfl., rfl. ↦
      isBisim_eqv (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
        (a2 b2 ↦
         eq (A.2 (e.0 .fro b0) (e.1 .fro b1))
           (Id_eqv A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1 .fro b2) a2)
        (a2 b2 ↦ Br eq A.2 (e.2 .fro b2) a2 rfl. rfl.)
        (a2 b2 ↦
         Id_eq_rfl A.0 A.1 A.2 (e.0 .fro b0) (e.0 .fro b0) rfl.
           (e.1 .fro b1) (e.1 .fro b1) rfl. (e.2 .fro b2) a2)
        (isBisim_of_iso (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
           (Id_eqv A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1))]]
