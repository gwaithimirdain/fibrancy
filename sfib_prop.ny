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
def prop_Br (A₀ A₁ : Type) (A₂ : Br Type A₀ A₁) (P₀ : A₀ → Type)
  (P₁ : A₁ → Type) (P₂ : Br ((X ↦ X → Type) : Type → Type) A₂ P₀ P₁)
  (h₀ : (a : A₀) (p q : P₀ a) → eq (P₀ a) p q)
  (h₁ : (a : A₁) (p q : P₁ a) → eq (P₁ a) p q)
  (h₂ : (a₀ : A₀) (a₁ : A₁) (a₂ : A₂ a₀ a₁) (p₀ q₀ : P₀ a₀) (p₁ q₁ : P₁ a₁)
        (p₂ : P₂ a₂ p₀ p₁) (q₂ : P₂ a₂ q₀ q₁)
        → Br eq (P₂ a₂) p₂ q₂ (h₀ a₀ p₀ q₀) (h₁ a₁ p₁ q₁)) (a₀ : A₀)
  (a₁ : A₁) (a₂ : A₂ a₀ a₁) (p₀ : P₀ a₀) (p₁ : P₁ a₁) (x y : P₂ a₂ p₀ p₁)
  : eq (P₂ a₂ p₀ p₁) x y
  ≔
  let ℓ₀ ≔ h₀ a₀ p₀ p₀ in
  let ℓ₁ ≔ h₁ a₁ p₁ p₁ in
  let tr : P₂ a₂ p₀ p₁ → P₂ a₂ p₀ p₁
    ≔ z ↦ eq.trr2 (P₀ a₀) (P₁ a₁) (u v ↦ P₂ a₂ u v) p₀ p₀ ℓ₀ p₁ p₁ ℓ₁ z in
  let ie : (z w : P₂ a₂ p₀ p₁) → eq (P₂ a₂ p₀ p₁) (tr z) w
    ≔ z w ↦
      Id_eq (P₀ a₀) (P₁ a₁) (P₂ a₂) p₀ p₁ z p₀ p₁ w ℓ₀ ℓ₁
        (h₂ a₀ a₁ a₂ p₀ p₀ p₁ p₁ z w) in
  eq.trr2_inj (P₀ a₀) (P₁ a₁) (u v ↦ P₂ a₂ u v) p₀ p₀ ℓ₀ p₁ p₁ ℓ₁ x y
    (eq.cat (P₂ a₂ p₀ p₁) (tr x) y (tr y) (ie x y)
       (eq.inv (P₂ a₂ p₀ p₁) (tr y) y (ie y y)))

{` A family is a strict proposition at every bridge level. `}
def Br_sPropᵈ (A : Type) (P : A → Type) : Type ≔ codata [
| x .prop : (a : A) (p q : P a) → eq (P a) p q
| x .id.p
  : (a₀ : A.0) → (a₁ : A.1) → (p₀ : P.0 a₀) → (p₁ : P.1 a₁)
    → Br_sPropᵈ (A.2 a₀ a₁) (a₂ ↦ P.2 a₂ p₀ p₁) ]

{` A pointwise strict proposition is one at every level, by a single corecursion
through prop_Br. `}
def Br_sPropᵈ_of_prop (A : Type) (P : A → Type)
  (h : (a : A) (p q : P a) → eq (P a) p q)
  : Br_sPropᵈ A P
  ≔ [
| .prop ↦ a p q ↦ h a p q
| .id.p ↦ a₀ a₁ p₀ p₁ ↦
    Br_sPropᵈ_of_prop (A.2 a₀ a₁) (a₂ ↦ P.2 a₂ p₀ p₁)
      (a₂ x y ↦
       prop_Br A.0 A.1 A.2 P.0 P.1 P.2 h.0 h.1
         (b₀ b₁ b₂ q₀ r₀ q₁ r₁ q₂ r₂ ↦ h.2 b₂ q₂ r₂) a₀ a₁ a₂ p₀ p₁ x y)]

{` Strong fibrancy is a strict proposition at every level; its .id .prop says
bridges of strong fibrancy are strictly unique. `}
def Br_sPropᵈ_sfib : Br_sPropᵈ Type isStrongFibrant
  ≔ Br_sPropᵈ_of_prop Type isStrongFibrant sfib_prop
