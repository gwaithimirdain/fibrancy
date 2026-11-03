{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "bookhott"
import "fibrant_types"

{` Lemmas about the Martin-Löf identity type eq of bookhott.ny, used by the
sfib_* files. Nothing here mentions bridges; funext (fibrant_types.ny) is
used only in eq.iscontr_Π and eq.iscontr_ΣΠ. `}

{` Contractibility with respect to the Martin-Lof identity type. `}
def eq.iscontr (A : Type) : Type ≔ sig (
  center : A,
  contract : (a : A) → eq A a center )

{` The identity equivalence. `}
def eqv_idmap (A : Type) : A ≅ A ≔ (
  to ≔ x ↦ x,
  fro ≔ x ↦ x,
  fro_to ≔ _ ↦ rfl.,
  to_fro ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def eq.ap_cat_inv (X Y : Type) (f : X → Y) (x y : X) (e : eq X x y)
  : eq (eq Y (f x) (f x))
      (eq.ap X Y f x x (eq.cat X x y x e (eq.inv X x y e))) rfl.
  ≔ match e [ rfl. ↦ rfl. ]

{` Inverting an equality twice is the identity. `}
def eq_inv_inv (X : Type) (x y : X) (p : eq X x y)
  : eq (eq X x y) (eq.inv X y x (eq.inv X x y p)) p
  ≔ match p [ rfl. ↦ rfl. ]

{` Inversion is an equivalence eq X x y ≅ eq X y x. `}
def eq_inv_eqv (X : Type) (x y : X) : eq X x y ≅ eq X y x
  ≔ adjointify (eq X x y) (eq X y x) (eq.inv X x y) (eq.inv X y x)
      (eq_inv_inv X x y) (eq_inv_inv X y x)

{` Transport along two equalities is injective. `}
def eq.trr2_inj (A B : Type) (P : A → B → Type) (a0 a1 : A)
  (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p q : P a0 b0)
  (e : eq (P a1 b1) (eq.trr2 A B P a0 a1 a2 b0 b1 b2 p)
         (eq.trr2 A B P a0 a1 a2 b0 b1 b2 q))
  : eq (P a0 b0) p q
  ≔ match a2, b2 [ rfl., rfl. ↦ e ]

{` Transporting the value of a dependent function along an equality of the base
gives its value at the target. `}
def eq.trr_apd (X : Type) (P : X → Type) (k : (x : X) → P x) (x y : X)
  (e : eq X x y)
  : eq (P y) (eq.trr X P x y e (k x)) (k y)
  ≔ match e [ rfl. ↦ rfl. ]

{` A dependent equality into a contractible fiber: any element is equal, over
any equality of the base, to the center. `}
def eqd_contr (X : Type) (F : X → Type) (x c : X) (e : eq X x c) (y : F x)
  (k : eq.iscontr (F c))
  : eqd X F x c e y (k .center)
  ≔ match e [ rfl. ↦ k .contract y ]

{` A dependent equality into a strict proposition. `}
def eqd_prop (X : Type) (F : X → Type) (x c : X) (e : eq X x c) (y : F x)
  (z : F c) (h : (u v : F c) → eq (F c) u v)
  : eqd X F x c e y z
  ≔ match e [ rfl. ↦ h y z ]

{` Equalities in a Σ-type over a family of strict propositions come from
equalities in the base. `}
def Σ_prop_eq (V : Type) (Q : V → Type)
  (hQ : (v : V) (x y : Q v) → eq (Q v) x y) (v w : V) (e : eq V v w)
  (x : Q v) (y : Q w)
  : eq (Σ V Q) (v, x) (w, y)
  ≔ ap2d V Q (Σ V Q) (v x ↦ (v, x)) v w e x y
      (eqd_prop V Q v w e x y (hQ w))

{` Contractibility passes to retracts. `}
def eq.iscontr_retract (X Y : Type) (Φ : X → Y) (Ψ : Y → X)
  (r : (y : Y) → eq Y (Φ (Ψ y)) y) (c : eq.iscontr X)
  : eq.iscontr Y
  ≔ (
  center ≔ Φ (c .center),
  contract ≔ y ↦
    eq.cat Y y (Φ (Ψ y)) (Φ (c .center)) (eq.inv Y (Φ (Ψ y)) y (r y))
      (eq.ap X Y Φ (Ψ y) (c .center) (c .contract (Ψ y))))

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

{` A Π-type of contractible types is contractible. `}
def eq.iscontr_Π (X : Type) (Y : X → Type) (c : (x : X) → eq.iscontr (Y x))
  : eq.iscontr ((x : X) → Y x)
  ≔ (
  center ≔ x ↦ c x .center,
  contract ≔ f ↦ funext X Y f (x ↦ c x .center) (x ↦ c x .contract (f x)))

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

{` Transport along the first projection of an equality in a total space recovers
the second component. `}
def ap_fst_trr (Q : Type) (F : Q → Type) (w u : Σ Q F) (s : eq (Σ Q F) w u)
  : eq (F (u .fst))
      (eq.trr Q F (w .fst) (u .fst) (eq.ap (Σ Q F) Q (v ↦ v .fst) w u s)
         (w .snd)) (u .snd)
  ≔ match s [ rfl. ↦ rfl. ]

{` The path from the center to any point, routed through the center's own
contraction. `}
def contr_singl (Q : Type) (F : Q → Type) (c : eq.iscontr (Σ Q F))
  (u : Σ Q F)
  : eq (Σ Q F) (c .center) u
  ≔ eq.cat (Σ Q F) (c .center) (c .center) u (c .contract (c .center))
      (eq.inv (Σ Q F) u (c .center) (c .contract u))

{` In a contractible total space, a point of a fiber gives a path from the base
of the center. `}
def fiber_to_eq (Q : Type) (F : Q → Type) (c : eq.iscontr (Σ Q F)) (b : Q)
  (r : F b)
  : eq Q (c .center .fst) b
  ≔ eq.ap (Σ Q F) Q (v ↦ v .fst) (c .center) (b, r)
      (contr_singl Q F c (b, r))

{` Conversely, a path from the base of the center gives a point of the fiber, by
transport. `}
def eq_to_fiber (Q : Type) (F : Q → Type) (c : eq.iscontr (Σ Q F)) (b : Q)
  (e : eq Q (c .center .fst) b)
  : F b
  ≔ eq.trr Q F (c .center .fst) b e (c .center .snd)

{` Round trip on fibers. `}
def fiber_fro_to (Q : Type) (F : Q → Type) (c : eq.iscontr (Σ Q F)) (b : Q)
  (r : F b)
  : eq (F b) (eq_to_fiber Q F c b (fiber_to_eq Q F c b r)) r
  ≔ ap_fst_trr Q F (c .center) (b, r) (contr_singl Q F c (b, r))

{` Round trip on paths. `}
def fiber_to_fro (Q : Type) (F : Q → Type) (c : eq.iscontr (Σ Q F)) (b : Q)
  (e : eq Q (c .center .fst) b)
  : eq (eq Q (c .center .fst) b)
      (fiber_to_eq Q F c b (eq_to_fiber Q F c b e)) e
  ≔ match e [
| rfl. ↦
    eq.ap_cat_inv (Σ Q F) Q (v ↦ v .fst) (c .center) (c .center)
      (c .contract (c .center))]

{` The fibers of a contractible total space are the based path spaces at the
center. `}
def fiber_eqv (Q : Type) (F : Q → Type) (c : eq.iscontr (Σ Q F)) (b : Q)
  : F b ≅ eq Q (c .center .fst) b
  ≔ adjointify (F b) (eq Q (c .center .fst) b) (fiber_to_eq Q F c b)
      (eq_to_fiber Q F c b) (fiber_fro_to Q F c b) (fiber_to_fro Q F c b)

{` A correspondence whose fibers in both directions have contractible total
spaces is an equivalence (level 0 of a strong bisimulation). `}
def corr_to_eqv (P Q : Type) (R : P → Q → Type)
  (cr : (p : P) → eq.iscontr (Σ Q (q ↦ R p q)))
  (cl : (q : Q) → eq.iscontr (Σ P (p ↦ R p q)))
  : P ≅ Q
  ≔ adjointify P Q (p ↦ cr p .center .fst) (q ↦ cl q .center .fst)
      (p ↦
       eq.inv P p (cl (cr p .center .fst) .center .fst)
         (eq.ap (Σ P (p' ↦ R p' (cr p .center .fst))) P (v ↦ v .fst)
            (p, cr p .center .snd) (cl (cr p .center .fst) .center)
            (cl (cr p .center .fst) .contract (p, cr p .center .snd))))
      (q ↦
       eq.inv Q q (cr (cl q .center .fst) .center .fst)
         (eq.ap (Σ Q (q' ↦ R (cl q .center .fst) q')) Q (v ↦ v .fst)
            (q, cl q .center .snd) (cr (cl q .center .fst) .center)
            (cr (cl q .center .fst) .contract (q, cl q .center .snd))))

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
