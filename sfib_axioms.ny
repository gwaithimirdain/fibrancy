{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "bookhott"
import "fibrant_types"
import "isstrongfibrant"
import "sfib_eq_lemmas"

{` The four axioms of the outer layer used for isStrongFibrant SFib:
ua_contract, Gel_η, sfib_prop below, and funext from fibrant_types.ny. `}

{` Univalence as based path induction: equivalences out of A are contractible
onto the identity. `}
axiom ua_contract (A B : Type) (e : A ≅ B)
  : eq (Σ Type (X ↦ A ≅ X)) (B, e) (A, eqv_idmap A)

{` A bridge in Type is strictly equal to the Gel of its pointwise types. `}
axiom Gel_η (A B : Type) (X : Br Type A B)
  : eq (Br Type A B) X (Gel A B (a b ↦ X a b))

{` Proofs of strong fibrancy are strictly equal (coinductive extensionality).
Used in Br_fib_prop: the strong-fibrancy part of a bridge in SFib is a strict
proposition, so H₀ only has to identify the Type part. `}
axiom sfib_prop (A : Type) (s t : isStrongFibrant A)
  : eq (isStrongFibrant A) s t

{` The usual univalence map, from ua_contract. `}
def ua (A B : Type) (e : A ≅ B) : eq Type A B
  ≔ eq.inv Type B A
      (eq.ap (Σ Type (X ↦ A ≅ X)) Type (u ↦ u .fst) (B, e) (A, eqv_idmap A)
         (ua_contract A B e))

{` Equivalence induction: to prove something about all A ≅ B it suffices to
prove it for the identity. `}
def eqv_ind (A : Type) (Q : (B : Type) → A ≅ B → Type)
  (q : Q A (eqv_idmap A)) (B : Type) (e : A ≅ B)
  : Q B e
  ≔ eq.trr (Σ Type (X ↦ A ≅ X)) (u ↦ Q (u .fst) (u .snd)) (A, eqv_idmap A)
      (B, e)
      (eq.inv (Σ Type (X ↦ A ≅ X)) (B, e) (A, eqv_idmap A)
         (ua_contract A B e)) q

{` Bridges in Type with pointwise equivalent types are strictly equal (Gel_η,
funext, ua). `}
def Br_eq_of_pointwise_eqv (P Q : Type) (X Y : Br Type P Q)
  (h : (p : P) (q : Q) → X p q ≅ Y p q)
  : eq (Br Type P Q) X Y
  ≔ eq.cat3 (Br Type P Q) X (Gel P Q (p q ↦ X p q)) (Gel P Q (p q ↦ Y p q))
      Y (Gel_η P Q X)
      (eq.ap (P → Q → Type) (Br Type P Q) (Gel P Q) (p q ↦ X p q)
         (p q ↦ Y p q)
         (funext P (_ ↦ Q → Type) (p q ↦ X p q) (p q ↦ Y p q)
            (p ↦
             funext Q (_ ↦ Type) (q ↦ X p q) (q ↦ Y p q)
               (q ↦ ua (X p q) (Y p q) (h p q)))))
      (eq.inv (Br Type P Q) Y (Gel P Q (p q ↦ Y p q)) (Gel_η P Q Y))
