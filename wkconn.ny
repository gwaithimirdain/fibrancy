{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-discrete-coreflector") -*- `}

import "bookhott"
import "isfibrant"
import "hott_bookhott"
import "fibrant_types"

def hasConn (A : Type) : Type ≔ sig (
  lconn : (a₀ a₁ : A) → (a₂ : Br A a₀ a₁)
          → Br (Br A) (rel a₀) a₂ (rel a₀) a₂,
  rconn : (a₀ a₁ : A) → (a₂ : Br A a₀ a₁)
          → Br (Br A) a₂ (rel a₁) a₂ (rel a₁),
  lconn_rel : (a : A)
              → Br (Br (Br A) (rel a) (rel a) (rel a) (rel a))
                  (rel (rel a)) (lconn a a (rel a)),
  rconn_rel : (a : A)
              → Br (Br (Br A) (rel a) (rel a) (rel a) (rel a))
                  (rel (rel a)) (rconn a a (rel a)) )

def hasconn_totBr (A : Type) (c : hasConn A)
  : hasConn (Σ (A × A) (u ↦ Br A (u .0) (u .1)))
  ≔ (
  lconn ≔ u0 u1 u2 ↦ (
    (c .lconn (u0 .0 .0) (u1 .0 .0) (u2 .0 .0),
     c .lconn (u0 .0 .1) (u1 .0 .1) (u2 .0 .1)),
    (rel c .lconn (u0 .1) (u1 .1) (sym (u2 .1)))⁽³¹²⁾),
  rconn ≔ u0 u1 u2 ↦ (
    (c .rconn (u0 .0 .0) (u1 .0 .0) (u2 .0 .0),
     c .rconn (u0 .0 .1) (u1 .0 .1) (u2 .0 .1)),
    (rel c .rconn (u0 .1) (u1 .1) (sym (u2 .1)))⁽³¹²⁾),
  lconn_rel ≔ u ↦ (
    (c .lconn_rel (u .0 .0), c .lconn_rel (u .0 .1)),
    (rel c .lconn_rel (u .1))⁽⁴¹²³⁾),
  rconn_rel ≔ u ↦ (
    (c .rconn_rel (u .0 .0), c .rconn_rel (u .0 .1)),
    (rel c .rconn_rel (u .1))⁽⁴¹²³⁾))

def hasconn_Σfib (A : Type) (B : A → Type) (cA : hasConn A)
  (fB : (x : A) → isFibrant (B x))
  : hasConn (Σ A B)
  ≔ (
  lconn ≔ u0 u1 u2 ↦ (
    cA .lconn (u0 .0) (u1 .0) (u2 .0),
    let u0_1_ppish
      ≔ fB⁽ᵖᵖᵖ⁾ (cA .lconn_rel (u0 .0))
          .id.1 (u0 .1)⁽ᵖᵖ⁾ (u0 .1)⁽ᵖᵖ⁾
          .id.1 (u0 .1)⁽ᵖᵖ⁾ (u0 .1)⁽ᵖᵖ⁾
          .trr (u0 .1)⁽ᵖᵖ⁾ in
    let u2_0_conn ≔ (cA .lconn (u0 .0) (u1 .0) (u2 .0)) in
    let u2_2_ish
      ≔ fB⁽ᵖᵖ⁾ (sym u2_0_conn)
          .id.1 (rel (u0 .1)) (u2 .1)
          .trr (rel (u0 .1)) in
    let u2_1_conn_ish
      ≔ sym
          (fB⁽ᵖᵖ⁾ u2_0_conn
           .id.2 (rel (u0 .1)) (u2 .1)
           .liftr (rel (u0 .1))) in
    fB⁽ᵖᵖᵖ⁾ (rel cA .lconn (rel (u0 .0)) (u2 .0) u2_0_conn)
      .id.1 (u0 .1)⁽ᵖᵖ⁾ u2_1_conn_ish
      .id.1 (u0 .1)⁽ᵖᵖ⁾ u2_1_conn_ish
      .trr u0_1_ppish),
  rconn ≔ u0 u1 u2 ↦ (
    cA .rconn (u0 .0) (u1 .0) (u2 .0),
    let u0_1_ppish
      ≔ fB⁽ᵖᵖᵖ⁾ (cA .rconn_rel (u1 .0))
          .id.1 (u1 .1)⁽ᵖᵖ⁾ (u1 .1)⁽ᵖᵖ⁾
          .id.1 (u1 .1)⁽ᵖᵖ⁾ (u1 .1)⁽ᵖᵖ⁾
          .trr (u1 .1)⁽ᵖᵖ⁾ in
    let u2_0_conn ≔ (cA .rconn (u0 .0) (u1 .0) (u2 .0)) in
    let u2_2_ish
      ≔ fB⁽ᵖᵖ⁾ (u2_0_conn) .id.2 (u2 .1) (rel (u1 .1)) .trl (rel (u1 .1))
      in
    let u2_1_conn_ish
      ≔ sym
          (fB⁽ᵖᵖ⁾ u2_0_conn
           .id.2 (u2 .1) (rel (u1 .1))
           .liftl (rel (u1 .1))) in
    fB⁽ᵖᵖᵖ⁾ (rel cA .rconn (u2 .0) (rel (u1 .0)) u2_0_conn)
      .id.1 u2_1_conn_ish (u1 .1)⁽ᵖᵖ⁾
      .id.1 u2_1_conn_ish (u1 .1)⁽ᵖᵖ⁾
      .trl u0_1_ppish),
  lconn_rel ≔ u ↦ (
    cA .lconn_rel (u .0),
    let K ≔ cA .lconn_rel (u .0) in
    let L ≔ cA .lconn (u .0) (u .0) (rel (u .0)) in
    let b2 ≔ (u .1)⁽ᵖᵖ⁾ in
    let b3 ≔ (u .1)⁽ᵖᵖᵖ⁾ in
    let u0_1_ppish ≔ fB⁽ᵖᵖᵖ⁾ K .id.1 b2 b2 .id.1 b2 b2 .trr b2 in
    {` The cube filled by u0_1_ppish, over K. `}
    let u0_1_ppish_lift ≔ fB⁽ᵖᵖᵖ⁾ K .id.1 b2 b2 .id.1 b2 b2 .liftr b2 in
    let u2_1_conn_ish
      ≔ sym (fB⁽ᵖᵖ⁾ L .id.2 (rel (u .1)) (rel (u .1)) .liftr (rel (u .1)))
      in
    {` The cube filled by the lconn case at u2 = rel u, over M. `}
    let M ≔ rel cA .lconn (rel (u .0)) (rel (u .0)) L in
    let lconn_lift
      ≔ fB⁽ᵖᵖᵖ⁾ M
          .id.1 b2 u2_1_conn_ish
          .id.1 b2 u2_1_conn_ish
          .liftr u0_1_ppish in
    {` A cube over K relating u2_1_conn_ish to reflexivities, filled in the first direction. `}
    let conn_ish_fill
      ≔ (fB⁽ᵖᵖᵖ⁾ K⁽²³¹⁾ .id.1 b2 b2 .id.1 b2 (sym u2_1_conn_ish) .liftr b2)⁽³¹²⁾
      in
    {` Transporting across the 4-cube lconn⁽ᵖᵖ⁾ K yields a cube over rel L from u0_1_ppish to the lconn value at rel u. `}
    let path
      ≔ fB⁽ᵖᵖᵖᵖ⁾ (sym (cA⁽ᵖᵖ⁾ .lconn (u .0)⁽ᵖᵖ⁾ (u .0)⁽ᵖᵖ⁾ K))
          .id.1 b3 (sym conn_ish_fill)
          .id.1 b3 (sym conn_ish_fill)
          .id.1 (rel u0_1_ppish) lconn_lift
          .trr (rel u0_1_ppish) in
    {` Transporting across rel K composes that with u0_1_ppish_lift. `}
    fB⁽ᵖᵖᵖᵖ⁾ (rel K)
      .id.1 b3 b3
      .id.1 b3 b3
      .id.1 b3 path
      .trr u0_1_ppish_lift),
  rconn_rel ≔ u ↦ (
    cA .rconn_rel (u .0),
    let K ≔ cA .rconn_rel (u .0) in
    let R ≔ cA .rconn (u .0) (u .0) (rel (u .0)) in
    let b2 ≔ (u .1)⁽ᵖᵖ⁾ in
    let b3 ≔ (u .1)⁽ᵖᵖᵖ⁾ in
    let u0_1_ppish ≔ fB⁽ᵖᵖᵖ⁾ K .id.1 b2 b2 .id.1 b2 b2 .trr b2 in
    let u0_1_ppish_lift ≔ fB⁽ᵖᵖᵖ⁾ K .id.1 b2 b2 .id.1 b2 b2 .liftr b2 in
    let u2_1_conn_ish
      ≔ sym (fB⁽ᵖᵖ⁾ R .id.2 (rel (u .1)) (rel (u .1)) .liftl (rel (u .1)))
      in
    let M ≔ rel cA .rconn (rel (u .0)) (rel (u .0)) R in
    let rconn_lift
      ≔ fB⁽ᵖᵖᵖ⁾ M
          .id.1 u2_1_conn_ish b2
          .id.1 u2_1_conn_ish b2
          .liftl u0_1_ppish in
    let conn_ish_fill
      ≔ (fB⁽ᵖᵖᵖ⁾ K⁽²³¹⁾ .id.1 b2 b2 .id.1 b2 (sym u2_1_conn_ish) .liftl b2)⁽³¹²⁾
      in
    let path
      ≔ fB⁽ᵖᵖᵖᵖ⁾ (sym (cA⁽ᵖᵖ⁾ .rconn (u .0)⁽ᵖᵖ⁾ (u .0)⁽ᵖᵖ⁾ K))
          .id.1 (sym conn_ish_fill) b3
          .id.1 (sym conn_ish_fill) b3
          .id.1 (rel u0_1_ppish) rconn_lift
          .trl (rel u0_1_ppish) in
    fB⁽ᵖᵖᵖᵖ⁾ (rel K)
      .id.1 b3 b3
      .id.1 b3 b3
      .id.1 b3 path
      .trr u0_1_ppish_lift))

{` Transport in a family over bridges along an equality of bridges. `}
def eq_tr_Br (B : Type) (P : (y0 y1 : B) → Br B y0 y1 → Type) (x0 x1 : B)
  (x2 : Br B x0 x1) (y0 y1 : B) (y2 : Br B y0 y1) (e0 : eq B x0 y0)
  (e1 : eq B x1 y1) (e2 : Br eq (Br B) x2 y2 e0 e1) (p : P x0 x1 x2)
  : P y0 y1 y2
  ≔ match e2 [ rfl. ⤇ p ]

{` Transport along a reflexivity bridge of an equality, in a family that also depends on an element of P over that reflexivity. `}
def eq_tr_Br_rel (B : Type) (P : (y0 y1 : B) → Br B y0 y1 → Type)
  (Q : (y : B) → P y y (rel y) → Type) (x y : B) (e : eq B x y)
  (p : P x x (rel x)) (q : Q x p)
  : Q y (eq_tr_Br B P x x (rel x) y y (rel y) e e (rel e) p)
  ≔ match e [ rfl. ↦ q ]

def hasconn_eqv (A B : Type) (e : A ≅ B) (cA : hasConn A) : hasConn B ≔
  let Pl
    ≔ (y0 y1 : B) (y2 : Br B y0 y1) ↦ Br (Br B) (rel y0) y2 (rel y0) y2 in
  let Pr
    ≔ (y0 y1 : B) (y2 : Br B y0 y1) ↦ Br (Br B) y2 (rel y1) y2 (rel y1) in
  let Q
    ≔ (y : B) (z : Br (Br B) (rel y) (rel y) (rel y) (rel y)) ↦
      Br (Br (Br B) (rel y) (rel y) (rel y) (rel y)) (rel (rel y)) z in
  (lconn ≔ b0 b1 b2 ↦
     eq_tr_Br B Pl (e .to (e .fro b0)) (e .to (e .fro b1))
       (rel (e .to) (rel (e .fro) b2)) b0 b1 b2 (e .to_fro b0)
       (e .to_fro b1) (rel (e .to_fro) b2)
       ((e .to)⁽ᵖᵖ⁾ (cA .lconn (e .fro b0) (e .fro b1) (rel (e .fro) b2))),
   rconn ≔ b0 b1 b2 ↦
     eq_tr_Br B Pr (e .to (e .fro b0)) (e .to (e .fro b1))
       (rel (e .to) (rel (e .fro) b2)) b0 b1 b2 (e .to_fro b0)
       (e .to_fro b1) (rel (e .to_fro) b2)
       ((e .to)⁽ᵖᵖ⁾ (cA .rconn (e .fro b0) (e .fro b1) (rel (e .fro) b2))),
   lconn_rel ≔ b ↦
     eq_tr_Br_rel B Pl Q (e .to (e .fro b)) b (e .to_fro b)
       ((e .to)⁽ᵖᵖ⁾ (cA .lconn (e .fro b) (e .fro b) (rel (e .fro b))))
       ((e .to)⁽ᵖᵖᵖ⁾ (cA .lconn_rel (e .fro b))),
   rconn_rel ≔ b ↦
     eq_tr_Br_rel B Pr Q (e .to (e .fro b)) b (e .to_fro b)
       ((e .to)⁽ᵖᵖ⁾ (cA .rconn (e .fro b) (e .fro b) (rel (e .fro b))))
       ((e .to)⁽ᵖᵖᵖ⁾ (cA .rconn_rel (e .fro b))))
