{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "bookhott"
import "fibrant_types"
import "isstrongfibrant"
import "sfib_types"
import "sfib_universe"
import "sfib_univalence"

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

def neg_iso : Bool ≅ Bool ≔ adjointify Bool Bool neg neg neg_neg neg_neg

def neg_bridge : Br SFib Bool𝕤 Bool𝕤
  ≔ sunivalence Bool𝕤 Bool𝕤 (a b ↦ eq𝕤 Bool𝕤 (neg_iso .fro b) a)
      (isBisim_of_iso Bool Bool neg_iso)

def trr_true (p : Br SFib Bool𝕤 Bool𝕤) : Bool ≔ p .f .trr true .center .fst

def isTrue : Bool → Type ≔ [ left. _ ↦ ⊤ | right. _ ↦ ∅ ]

def true_neq_false (e : eq Bool true false) : ∅
  ≔ eq.trr Bool isTrue true false e ()

def rel_neq_neg (e : eq (Br SFib Bool𝕤 Bool𝕤) (rel Bool𝕤) neg_bridge) : ∅
  ≔ true_neq_false
      (eq.ap (Br SFib Bool𝕤 Bool𝕤) Bool trr_true (rel Bool𝕤) neg_bridge e)

{` SFib is strongly fibrant (sfib_universe.ny), so its bridges are strict
equalities, and neg_bridge becomes a nontrivial strict loop. Hence strict
equality on SFib does not satisfy UIP. `}
def neg_loop : eq SFib Bool𝕤 Bool𝕤
  ≔ sbridge_to_eq SFib𝕤 Bool𝕤 Bool𝕤 neg_bridge

def neg_loop_to_Br
  : eq (Br SFib Bool𝕤 Bool𝕤) (eq.to_Br SFib Bool𝕤 Bool𝕤 neg_loop)
      neg_bridge
  ≔ sbridge_fro_to SFib𝕤 Bool𝕤 Bool𝕤 neg_bridge

def neg_loop_nontrivial (k : eq (eq SFib Bool𝕤 Bool𝕤) neg_loop rfl.) : ∅
  ≔ rel_neq_neg
      (eq.cat (Br SFib Bool𝕤 Bool𝕤) (rel Bool𝕤)
         (eq.to_Br SFib Bool𝕤 Bool𝕤 neg_loop) neg_bridge
         (eq.inv (Br SFib Bool𝕤 Bool𝕤) (eq.to_Br SFib Bool𝕤 Bool𝕤 neg_loop)
            (rel Bool𝕤)
            (eq.ap (eq SFib Bool𝕤 Bool𝕤) (Br SFib Bool𝕤 Bool𝕤)
               (eq.to_Br SFib Bool𝕤 Bool𝕤) neg_loop rfl. k)) neg_loop_to_Br)

def UIP_SFib : Type
  ≔ (A B : SFib) (p q : eq SFib A B) → eq (eq SFib A B) p q

def SFib_not_UIP (u : UIP_SFib) : ∅
  ≔ neg_loop_nontrivial (u Bool𝕤 Bool𝕤 neg_loop rfl.)
