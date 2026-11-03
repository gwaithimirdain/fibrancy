{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "isstrongfibrant"
import "sfib_types"
import "sfib_axioms"
import "sfib_eq_lemmas"

{` The Type part of a bridge in SFib out of A. `}
def Br_base (A : SFib) : Type ≔ Σ Type (Y ↦ Br Type (A .t) Y)

{` The strong-fibrancy part of a bridge in SFib out of A. `}
def Br_fib (A : SFib) (v : Br_base A) : Type
  ≔ Σ (isStrongFibrant (v .fst)) (f ↦ Br isStrongFibrant (v .snd) (A .f) f)

{` Reassembling base and fibrancy parts into a bridge in SFib. `}
def reassoc (A : SFib) (w : Σ (Br_base A) (Br_fib A))
  : Σ SFib (B ↦ Br SFib A B)
  ≔ ((w .fst .fst, w .snd .fst), (w .fst .snd, w .snd .snd))

{` Bridges in a pointwise strict proposition are strictly unique. `}
def prop_Br (P₀ P₁ : Type) (P₂ : Br Type P₀ P₁)
  (h₀ : (p q : P₀) → eq P₀ p q) (h₁ : (p q : P₁) → eq P₁ p q)
  (h₂ : (p₀ q₀ : P₀) (p₁ q₁ : P₁) (p₂ : P₂ p₀ p₁) (q₂ : P₂ q₀ q₁)
        → Br eq P₂ p₂ q₂ (h₀ p₀ q₀) (h₁ p₁ q₁)) (p₀ : P₀) (p₁ : P₁)
  (x y : P₂ p₀ p₁)
  : eq (P₂ p₀ p₁) x y
  ≔
  let ℓ₀ ≔ h₀ p₀ p₀ in
  let ℓ₁ ≔ h₁ p₁ p₁ in
  let tr : P₂ p₀ p₁ → P₂ p₀ p₁
    ≔ z ↦ eq.trr2 P₀ P₁ (u v ↦ P₂ u v) p₀ p₀ ℓ₀ p₁ p₁ ℓ₁ z in
  let ie : (z w : P₂ p₀ p₁) → eq (P₂ p₀ p₁) (tr z) w
    ≔ z w ↦ Id_eq P₀ P₁ P₂ p₀ p₁ z p₀ p₁ w ℓ₀ ℓ₁ (h₂ p₀ p₀ p₁ p₁ z w) in
  eq.trr2_inj P₀ P₁ (u v ↦ P₂ u v) p₀ p₀ ℓ₀ p₁ p₁ ℓ₁ x y
    (eq.cat (P₂ p₀ p₁) (tr x) y (tr y) (ie x y)
       (eq.inv (P₂ p₀ p₁) (tr y) y (ie y y)))

{` The strong-fibrancy part is a strict proposition: sfib_prop for the
fibrancy of B, and prop_Br applied to the degeneracy rel sfib_prop for the
bridge of fibrancies. `}
def Br_fib_prop (A : SFib) (v : Br_base A) (x y : Br_fib A v)
  : eq (Br_fib A v) x y
  ≔ ap2d (isStrongFibrant (v .fst))
      (f ↦ Br isStrongFibrant (v .snd) (A .f) f) (Br_fib A v)
      (f g ↦ (f, g)) (x .fst) (y .fst)
      (sfib_prop (v .fst) (x .fst) (y .fst)) (x .snd) (y .snd)
      (eqd_prop (isStrongFibrant (v .fst))
         (f ↦ Br isStrongFibrant (v .snd) (A .f) f) (x .fst) (y .fst)
         (sfib_prop (v .fst) (x .fst) (y .fst)) (x .snd) (y .snd)
         (prop_Br (isStrongFibrant (A .t)) (isStrongFibrant (v .fst))
            (Br isStrongFibrant (v .snd)) (sfib_prop (A .t))
            (sfib_prop (v .fst))
            (p₀ q₀ p₁ q₁ p₂ q₂ ↦ rel sfib_prop (v .snd) p₂ q₂) (A .f)
            (y .fst)))

{` The Type part of a bridge out of A is strictly equal to (A .t, rel (A .t)):
bisimulation, equivalence induction, Gel_η. `}
def Br_base_eq (A : SFib) (Bt : Type) (X : Br Type (A .t) Bt)
  (Bf : isStrongFibrant Bt) (Xf : Br isStrongFibrant X (A .f) Bf)
  : eq (Br_base A) (Bt, X) (A .t, rel (A .t))
  ≔ eqv_ind (A .t)
      (Y e ↦
       (Z : Br Type (A .t) Y) →
       ((a : A .t) (y : Y) → Z a y ≅ eq Y (e .to a) y)
       → eq (Br_base A) (Y, Z) (A .t, rel (A .t)))
      (Z h ↦
       eq.ap (Br Type (A .t) (A .t)) (Br_base A) (W ↦ (A .t, W)) Z
         (rel (A .t))
         (Br_eq_of_pointwise_eqv (A .t) (A .t) Z (rel (A .t))
            (a b ↦
             comp_eqv (Z a b) (eq (A .t) a b) (Br (A .t) a b) (h a b)
               (inverse_eqv (Br (A .t) a b) (eq (A .t) a b)
                  (sbridge_eqv_eq A a b))))) Bt
      (corr_to_eqv (A .t) Bt (a b ↦ X a b) (a ↦ Xf .trr a) (b ↦ Xf .trl b))
      X (a b ↦ fiber_eqv Bt (b' ↦ X a b') (Xf .trr a) b)

{` Level 0: bridges out of A are contractible, with center (A, rel A) and the
axioms only in the contraction. `}
def H₀ (A : SFib) : eq.iscontr (Σ SFib (B ↦ Br SFib A B)) ≔ (
  center ≔ (A, rel A),
  contract ≔ u ↦
    eq.ap (Σ (Br_base A) (Br_fib A)) (Σ SFib (B ↦ Br SFib A B)) (reassoc A)
      ((u .fst .t, u .snd .t), (u .fst .f, u .snd .f))
      ((A .t, rel (A .t)), (A .f, rel (A .f)))
      (Σ_prop_eq (Br_base A) (Br_fib A) (Br_fib_prop A)
         (u .fst .t, u .snd .t) (A .t, rel (A .t))
         (Br_base_eq A (u .fst .t) (u .snd .t) (u .fst .f) (u .snd .f))
         (u .fst .f, u .snd .f) (A .f, rel (A .f))))

{` The Type part of a bridge in SFib into B. `}
def Br_basel (B : SFib) : Type ≔ Σ Type (Y ↦ Br Type Y (B .t))

{` The strong-fibrancy part of a bridge in SFib into B. `}
def Br_fibl (B : SFib) (v : Br_basel B) : Type
  ≔ Σ (isStrongFibrant (v .fst)) (f ↦ Br isStrongFibrant (v .snd) f (B .f))

{` Reassembling base and fibrancy parts into a bridge into B. `}
def reassocl (B : SFib) (w : Σ (Br_basel B) (Br_fibl B))
  : Σ SFib (A ↦ Br SFib A B)
  ≔ ((w .fst .fst, w .snd .fst), (w .fst .snd, w .snd .snd))

{` Mirror image of Br_fib_prop. `}
def Br_fibl_prop (B : SFib) (v : Br_basel B) (x y : Br_fibl B v)
  : eq (Br_fibl B v) x y
  ≔ ap2d (isStrongFibrant (v .fst))
      (f ↦ Br isStrongFibrant (v .snd) f (B .f)) (Br_fibl B v)
      (f g ↦ (f, g)) (x .fst) (y .fst)
      (sfib_prop (v .fst) (x .fst) (y .fst)) (x .snd) (y .snd)
      (eqd_prop (isStrongFibrant (v .fst))
         (f ↦ Br isStrongFibrant (v .snd) f (B .f)) (x .fst) (y .fst)
         (sfib_prop (v .fst) (x .fst) (y .fst)) (x .snd) (y .snd)
         (prop_Br (isStrongFibrant (v .fst)) (isStrongFibrant (B .t))
            (Br isStrongFibrant (v .snd)) (sfib_prop (v .fst))
            (sfib_prop (B .t))
            (p₀ q₀ p₁ q₁ p₂ q₂ ↦ rel sfib_prop (v .snd) p₂ q₂) (y .fst)
            (B .f)))

{` Mirror image of Br_base_eq, inducting on B .t ≅ At. `}
def Br_basel_eq (B : SFib) (At : Type) (X : Br Type At (B .t))
  (Af : isStrongFibrant At) (Xf : Br isStrongFibrant X Af (B .f))
  : eq (Br_basel B) (At, X) (B .t, rel (B .t))
  ≔ eqv_ind (B .t)
      (Y e ↦
       (Z : Br Type Y (B .t)) →
       ((y : Y) (b : B .t) → Z y b ≅ eq Y (e .to b) y)
       → eq (Br_basel B) (Y, Z) (B .t, rel (B .t)))
      (Z h ↦
       eq.ap (Br Type (B .t) (B .t)) (Br_basel B) (W ↦ (B .t, W)) Z
         (rel (B .t))
         (Br_eq_of_pointwise_eqv (B .t) (B .t) Z (rel (B .t))
            (y b ↦
             comp_eqv (Z y b) (eq (B .t) b y) (Br (B .t) y b) (h y b)
               (comp_eqv (eq (B .t) b y) (eq (B .t) y b) (Br (B .t) y b)
                  (eq_inv_eqv (B .t) b y)
                  (inverse_eqv (Br (B .t) y b) (eq (B .t) y b)
                     (sbridge_eqv_eq B y b)))))) At
      (inverse_eqv At (B .t)
         (corr_to_eqv At (B .t) (a b ↦ X a b) (a ↦ Xf .trr a)
            (b ↦ Xf .trl b))) X
      (y b ↦ fiber_eqv At (a ↦ X a b) (Xf .trl b) y)

{` Level 0 in the other direction, for .trl.p. `}
def H₀l (B : SFib) : eq.iscontr (Σ SFib (A ↦ Br SFib A B)) ≔ (
  center ≔ (B, rel B),
  contract ≔ u ↦
    eq.ap (Σ (Br_basel B) (Br_fibl B)) (Σ SFib (A ↦ Br SFib A B))
      (reassocl B) ((u .fst .t, u .snd .t), (u .fst .f, u .snd .f))
      ((B .t, rel (B .t)), (B .f, rel (B .f)))
      (Σ_prop_eq (Br_basel B) (Br_fibl B) (Br_fibl_prop B)
         (u .fst .t, u .snd .t) (B .t, rel (B .t))
         (Br_basel_eq B (u .fst .t) (u .snd .t) (u .fst .f) (u .snd .f))
         (u .fst .f, u .snd .f) (B .f, rel (B .f))))

{` Converse of Br_iscontr: a bridge of contractions makes every fiber of the
bridge contractible. `}
def iscontr_of_Br (X0 X1 : Type) (X2 : Br Type X0 X1) (c0 : eq.iscontr X0)
  (c1 : eq.iscontr X1) (c2 : Br eq.iscontr X2 c0 c1) (u0 : X0) (u1 : X1)
  : eq.iscontr (X2 u0 u1)
  ≔
  let e0 ≔ c0 .contract u0 in
  let e1 ≔ c1 .contract u1 in
  let tr
    ≔ eq.trr2 X0 X1 (x y ↦ X2 x y) u0 (c0 .center) e0 u1 (c1 .center) e1 in
  let k
    ≔ eq.trl2 X0 X1 (x y ↦ X2 x y) u0 (c0 .center) e0 u1 (c1 .center) e1
        (c2 .center) in
  (center ≔ k,
   contract ≔ u2 ↦
     eq.trr2_inj X0 X1 (x y ↦ X2 x y) u0 (c0 .center) e0 u1 (c1 .center) e1
       u2 k
       (eq.cat (X2 (c0 .center) (c1 .center)) (tr u2) (c2 .center) (tr k)
          (Id_eq X0 X1 X2 u0 u1 u2 (c0 .center) (c1 .center) (c2 .center)
             e0 e1 (c2 .contract u2))
          (eq.inv (X2 (c0 .center) (c1 .center)) (tr k) (c2 .center)
             (eqv_trr2 X0 X1 (x y ↦ X2 x y) u0 (c0 .center) e0 u1
                  (c1 .center) e1
              .to_fro (c2 .center)))))

{` Cube shapes ∂ and fillers T: T zero. is SFib, T (suc. …) is the type of
bridges in T over the given boundary. `}
def ∂ : Type ≔ data [
| zero. : ∂
| suc. : (y₀ y₁ : ∂) → Br ∂ y₀ y₁ → T y₀ → T y₁ → ∂ ]

and T (y : ∂) : Type ≔ match y [
| zero. ↦ SFib
| suc. y₀ y₁ y₂ x₀ x₁ ↦ Br T y₂ x₀ x₁]

{` The type whose contractibility is the .trr.p field of isStrongFibrant (T y).
`}
def ΣBrT (y₀ y₁ : ∂) (y₂ : Br ∂ y₀ y₁) (x₀ : T y₀) : Type
  ≔ Σ (T y₁) (x₁ ↦ Br T y₂ x₀ x₁)

{` The same for .trl.p. `}
def ΣBrTl (y₀ y₁ : ∂) (y₂ : Br ∂ y₀ y₁) (x₁ : T y₁) : Type
  ≔ Σ (T y₀) (x₀ ↦ Br T y₂ x₀ x₁)

{` Contractibility at every shape, by induction on the bridge y₂: zero. is H₀,
suc. is iscontr_of_Br applied to rel H_all plus sym. `}
def H_all (y₀ y₁ : ∂) (y₂ : Br ∂ y₀ y₁) (x₀ : T y₀)
  : eq.iscontr (ΣBrT y₀ y₁ y₂ x₀)
  ≔ match y₂ [
| zero. ⤇ H₀ x₀
| suc. y0 y1 y2 x0 x1 ⤇
    eq.iscontr_retract
      (rel ΣBrT y2.0 y2.1 (sym y2.2) x₀ (x0.1, x0.2) (x1.1, x1.2))
      (ΣBrT (suc. y0.0 y1.0 y2.0 x0.0 x1.0) (suc. y0.1 y1.1 y2.1 x0.1 x1.1)
         (suc. y0 y1 y2 x0 x1) x₀) (v ↦ (v .fst, sym (v .snd)))
      (u ↦ (u .fst, sym (u .snd))) (u ↦ rfl.)
      (iscontr_of_Br (ΣBrT y0.0 y0.1 y0.2 x0.0) (ΣBrT y1.0 y1.1 y1.2 x1.0)
         (rel ΣBrT y2.0 y2.1 (sym y2.2) x₀) (H_all y0.0 y0.1 y0.2 x0.0)
         (H_all y1.0 y1.1 y1.2 x1.0) (rel H_all y2.0 y2.1 (sym y2.2) x₀)
         (x0.1, x0.2) (x1.1, x1.2))]

{` Mirror image of H_all. `}
def H_all_l (y₀ y₁ : ∂) (y₂ : Br ∂ y₀ y₁) (x₁ : T y₁)
  : eq.iscontr (ΣBrTl y₀ y₁ y₂ x₁)
  ≔ match y₂ [
| zero. ⤇ H₀l x₁
| suc. y0 y1 y2 x0 x1 ⤇
    eq.iscontr_retract
      (rel ΣBrTl y2.0 y2.1 (sym y2.2) x₁ (x0.0, x0.2) (x1.0, x1.2))
      (ΣBrTl (suc. y0.0 y1.0 y2.0 x0.0 x1.0)
         (suc. y0.1 y1.1 y2.1 x0.1 x1.1) (suc. y0 y1 y2 x0 x1) x₁)
      (v ↦ (v .fst, sym (v .snd))) (u ↦ (u .fst, sym (u .snd))) (u ↦ rfl.)
      (iscontr_of_Br (ΣBrTl y0.0 y0.1 y0.2 x0.1)
         (ΣBrTl y1.0 y1.1 y1.2 x1.1) (rel ΣBrTl y2.0 y2.1 (sym y2.2) x₁)
         (H_all_l y0.0 y0.1 y0.2 x0.1) (H_all_l y1.0 y1.1 y1.2 x1.1)
         (rel H_all_l y2.0 y2.1 (sym y2.2) x₁) (x0.0, x0.2) (x1.0, x1.2))]

{` Every T y is strongly fibrant, by corecursion; the only corecursive call is
in .id.p. `}
def 𝕤T (y : ∂) : isStrongFibrant (T y) ≔ [
| .trr.p ↦ x₀ ↦ H_all y.0 y.1 y.2 x₀
| .trl.p ↦ x₁ ↦ H_all_l y.0 y.1 y.2 x₁
| .id.p ↦ x₀ x₁ ↦ 𝕤T (suc. y.0 y.1 y.2 x₀ x₁)]

{` The universe of strongly fibrant types is strongly fibrant. `}
def 𝕤SFib : isStrongFibrant SFib ≔ 𝕤T zero.

{` SFib as an element of SFib. `}
def SFib𝕤 : SFib ≔ (SFib, 𝕤SFib)

{` Bridges out of A in SFib are contractible. `}
def sfib_contr (A : SFib) : eq.iscontr (Σ SFib (B ↦ Br SFib A B))
  ≔ rel 𝕤SFib .trr A

{` Bridges in SFib are strict equalities: the two univalences coincide. `}
def SFib_univalence (A B : SFib) : Br SFib A B ≅ eq SFib A B
  ≔ sbridge_eqv_eq SFib𝕤 A B
