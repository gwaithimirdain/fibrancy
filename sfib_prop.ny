{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "bookhott"
import "hott_bookhott"
import "isstrongfibrant"
import "sfib_axioms"

{` Transport along two equalities is injective. `}
def eq.trr2_inj (A B : Type) (P : A → B → Type) (a0 a1 : A)
  (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p q : P a0 b0)
  (e : eq (P a1 b1) (eq.trr2 A B P a0 a1 a2 b0 b1 b2 p)
         (eq.trr2 A B P a0 a1 a2 b0 b1 b2 q))
  : eq (P a0 b0) p q
  ≔ match a2, b2 [ rfl., rfl. ↦ e ]

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

{` A family is a strict proposition at every bridge level. `}
def Br_sProp (P : Type) : Type ≔ codata [
| x .prop : (p q : P) → eq P p q
| x .id.p : (p₀ : P.0) → (p₁ : P.1) → Br_sProp (P.2 p₀ p₁) ]

{` A pointwise strict proposition is one at every level, by a single corecursion
through prop_Br. `}
def Br_sProp_of_prop (P : Type) (h : (p q : P) → eq P p q) : Br_sProp P ≔ [
| .prop ↦ p q ↦ h p q
| .id.p ↦ p₀ p₁ ↦
    Br_sProp_of_prop (P.2 p₀ p₁)
      (x y ↦
       prop_Br P.0 P.1 P.2 h.0 h.1 (q₀ r₀ q₁ r₁ q₂ r₂ ↦ h.2 q₂ r₂) p₀ p₁ x
         y)]

{` Strong fibrancy is a strict proposition at every level; its .id .prop says
bridges of strong fibrancy are strictly unique. `}
def Br_sProp_sfib (A : Type) : Br_sProp (isStrongFibrant A)
  ≔ Br_sProp_of_prop (isStrongFibrant A) (sfib_prop A)
