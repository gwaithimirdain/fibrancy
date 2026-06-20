{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"
import "univalence"

{` Stuff that should go elsewhere `}

def Gel_iso′ (A B : Type) (R : A → B → Type) (a : A) (b : B)
  : Gel A B R a b ≅ R a b
  ≔ (
  to ≔ g ↦ g .0,
  fro ≔ r ↦ (r,),
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def Gel2 (A00 A01 : Type) (A02 : Br Type A00 A01) (A10 A11 : Type)
  (A12 : Br Type A10 A11) (A20 : Br Type A00 A10) (A21 : Br Type A01 A11)
  (A22 : (a00 : A00) (a01 : A01) (a02 : A02 a00 a01) (a10 : A10)
         (a11 : A11) (a12 : A12 a10 a11) (a20 : A20 a00 a10)
         (a21 : A21 a01 a11)
         → Type)
  : Type⁽ᵖᵖ⁾ A02 A12 A20 A21
  ≔ sig (
  a .ungel : A22 a.00 a.01 a.02 a.10 a.11 a.12 a.20 a.21 )

def Gel2_iso′ (A00 A01 : Type) (A02 : Br Type A00 A01) (A10 A11 : Type)
  (A12 : Br Type A10 A11) (A20 : Br Type A00 A10) (A21 : Br Type A01 A11)
  (A22 : (a00 : A00) (a01 : A01) (a02 : A02 a00 a01) (a10 : A10)
         (a11 : A11) (a12 : A12 a10 a11) (a20 : A20 a00 a10)
         (a21 : A21 a01 a11)
         → Type) (a00 : A00) (a01 : A01) (a02 : A02 a00 a01) (a10 : A10)
  (a11 : A11) (a12 : A12 a10 a11) (a20 : A20 a00 a10) (a21 : A21 a01 a11)
  : Gel2 A00 A01 A02 A10 A11 A12 A20 A21 A22 a02 a12 a20 a21
    ≅ A22 a00 a01 a02 a10 a11 a12 a20 a21
  ≔ (
  to ≔ x ↦ x .ungel,
  fro ≔ y ↦ (y,),
  fro_to ≔ x ↦ rfl.,
  to_fro ≔ x ↦ rfl.,
  to_fro_to ≔ x ↦ rfl.)

def BR (A0 : Type) (A1 : Type) (A2 : Br Type A0 A1) : Type ≔ sig (
  a0 : A0,
  a1 : A1,
  a2 : A2 a0 a1 )

def id_Π_iso′ (A0 : Type) (A1 : Type) (A2 : Br Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type)
  (B2 : {a0 : A0} {a1 : A1} (a2 : A2 a0 a1) →⁽ᵖ⁾ Br Type (B0 a0) (B1 a1))
  (f0 : (a0 : A0) → B0 a0) (f1 : (a1 : A1) → B1 a1)
  : ((a : BR A0 A1 A2) → B2 (a .2) (f0 (a .0)) (f1 (a .1)))
    ≅ ({a0 : A0} {a1 : A1} (a2 : A2 a0 a1) →⁽ᵖ⁾ B2 a2 (f0 a0) (f1 a1))
  ≔ (
  to ≔ f ↦ a ⤇ f (a.0, a.1, a.2),
  fro ≔ g ↦ a ↦ g (a .2),
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def eqv_idmap (A : Type) : A ≅ A ≔ (
  to ≔ x ↦ x,
  fro ≔ x ↦ x,
  fro_to ≔ x ↦ rfl.,
  to_fro ≔ x ↦ rfl.,
  to_fro_to ≔ x ↦ rfl.)

{` Not sure what to call this `}
def B̂ (B0 : Type) (B1 : Type) (B2 : Br Type B0 B1) (C0 : B0 → Type)
  (C1 : B1 → Type)
  : Type
  ≔ sig (
  b0 : B0,
  b1 : B1,
  b2 : B2 b0 b1,
  c0 : C0 b0,
  c1 : C1 b1 )

{` A kind of very surjective map from A to (B → Type), with pointwise isomorphisms as the witnesses of equality instead of bridges. `}

def vsurj≅ (A B : Type) (f : A → B → Type) : Type ≔ codata [
| s .surj : (P : B → Type) → A
| s .surjeq : (P : B → Type) (b : B) → f (s .surj P) b ≅ P b
| s .id.p
  : (a0 : A.0) (a1 : A.1)
    → vsurj≅ (A.2 a0 a1) (B̂ B.0 B.1 B.2 (f.0 a0) (f.1 a1))
        (a2 v ↦ f.2 a2 {v .0} {v .1} (v .2) (v .3) (v .4)) ]

{` This should be just as easy to build into Narya for Gel as the ordinary vsurj_gel.  And this version seems more likely to encode everything we need: the pointwise isomorphisms surjeq ensure that the action of surj is actually a Gel. `}

def vsurj≅_gel (A0 A1 : Type)
  : vsurj≅ (Br Type A0 A1) (A0 × A1) (A2 a ↦ A2 (a .0) (a .1))
  ≔ [
| .surj ↦ P ↦ Gel A0 A1 (a0 a1 ↦ P (a0, a1))
| .surjeq ↦ P a ↦ Gel_iso′ A0 A1 (a0 a1 ↦ P (a0, a1)) (a .0) (a .1)
| .id.p ↦ A20 A21 ↦ [
  | .surj ↦ P ↦
      Gel2 A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 A20 A21
        (a00 a01 a02 a10 a11 a12 a20 a21 ↦
         P ((a00, a10), (a01, a11), (a02, a12), a20, a21))
  | .surjeq ↦ P u ↦
      Gel2_iso′ A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 A20 A21
        (a00 a01 a02 a10 a11 a12 a20 a21 ↦
         P ((a00, a10), (a01, a11), (a02, a12), a20, a21)) (u .0 .0)
        (u .1 .0) (u .2 .0) (u .0 .1) (u .1 .1) (u .2 .1) (u .3) (u .4)
  | .id.p ↦ A220 A221 ↦ ¿ʔ]]

{` However, transferring this to the previous notion of very-surjective would require lifting back along a Gel. `}

def vsurj (A B : Type) (f : A → B) : Type ≔ codata [
| s .surj : B → A
| s .surjeq : (b : B) → Br B (f (s .surj b)) b
| s .id.p
  : (a0 : A.0) (a1 : A.1)
    → vsurj (A.2 a0 a1) (B.2 (f.0 a0) (f.1 a1)) (a2 ↦ f.2 a2) ]

axiom vsurj_eqv (A0 B0 : Type) (f0 : A0 → B0) (A1 B1 : Type) (f1 : A1 → B1)
  (eA : A0 ≅ A1) (eB : B0 ≅ B1)
  (ef : (x : A0) → eq.eq B1 (eB .to (f0 x)) (f1 (eA .to x)))
  (s0 : vsurj A0 B0 f0)
  : vsurj A1 B1 f1

def vsurj_of_vsurj≅ (A B : Type) (f : A → B → Type) (s : vsurj≅ A B f)
  : vsurj A (B → Type) f
  ≔ [
| .surj ↦ s .surj
| .surjeq ↦ P ↦ b ⤇
    Gel (f (s .surj P) b.0) (P b.1)
      (c0 p1 ↦ Br P b.2 (s .surjeq P b.0 .to c0) p1)
| .id.p ↦ a0 a1 ↦
    vsurj_eqv (A.2 a0 a1)
      ((b : BR B.0 B.1 B.2) → Br Type (f.0 a0 (b .0)) (f.1 a1 (b .1)))
      (a2 b ↦ f.2 a2 (b .2)) (A.2 a0 a1)
      ({𝑥₀ : B.0} {𝑥₁ : B.1} (𝑥₂ : B.2 𝑥₀ 𝑥₁)
       →⁽ᵖ⁾ Type⁽ᵖ⁾ (f.0 a0 𝑥₀) (f.1 a1 𝑥₁)) (a2 ↦ f.2 a2)
      (eqv_idmap (A.2 a0 a1))
      (id_Π_iso′ B.0 B.1 B.2 (_ ↦ Type) (_ ↦ Type) (_ ⤇ Br Type) (f.0 a0)
         (f.1 a1)) (a2 ↦ rfl.)
      ¿vsurj_of_vsurj≅ (A.2 a0 a1) (B̂ B.0 B.1 B.2 (f.0 a0) (f.1 a1))
       (a2 v ↦ f.2 a2 (v .2) (v .3) (v .4)) (s .id a0 a1) ʔ]

{` And defining a displayed version of this seems to require transporting across isomorphisms already.  If we hypothesize such a transport for Bᵈ, then when we apply it in a degenerated context, we get eqv_idmaps in the base where we don't want them.  Supposing that transporting along idmap is the identity might help with that, but probably sends us down a rabbit hole.  Or we could try a higher coinductive notion of equivalence-invariance that would fix the endpoints in the .id destructor, but then we have an isomorphism in Br Type and we want an isomorphism in Type. `}

def ≅invar (B : Type) (R : (B → Type) → Type) : Type ≔ codata [
| i .tr : (P Q : B → Type) → ((b : B) → P b ≅ Q b) → R P → R Q
| i .id.p
  : (P0 : B.0 → Type) (P1 : B.1 → Type) (r0 : R.0 P0) (r1 : R.1 P1)
    → ≅invar (BR B.0 B.1 B.2) (P ↦ R.2 {P0} {P1} (b ⤇ ¿P (b.0, b.1, b.2)ʔ) r0 r1) ]

def vsurj≅ᵈ (A B : Type) (f : A → B → Type) (Aᵈ : A → Type)
  (Bᵈ : (B → Type) → Type) (fᵈ : (a : A) → Aᵈ a → Bᵈ (f a))
  (Bᵈ≅ : (P Q : B → Type) → ((b : B) → P b ≅ Q b) → Bᵈ P → Bᵈ Q)
  (Bᵈ≅id : (P : B → Type) (bᵈ : Bᵈ P)
           → eq (Bᵈ P) (Bᵈ≅ P P (b ↦ eqv_idmap (P b)) bᵈ) bᵈ)
  : Type
  ≔ codata [
| t .surj : (a : A) → Bᵈ (f a) → Aᵈ a
| t .surjeq : (a : A) (b : Bᵈ (f a)) → eq (Bᵈ (f a)) (fᵈ a (t .surj a b)) b
| t .id.p
  : (a0 : A.0) (aᵈ0 : Aᵈ.0 a0) (a1 : A.1) (aᵈ1 : Aᵈ.1 a1)
    → vsurj≅ᵈ (A.2 a0 a1) (B̂ B.0 B.1 B.2 (f.0 a0) (f.1 a1))
        (a2 v ↦ f.2 a2 {v .0} {v .1} (v .2) (v .3) (v .4))
        (a2 ↦ Aᵈ.2 a2 aᵈ0 aᵈ1)
        (P ↦
         Bᵈ.2 {f.0 a0} {f.1 a1}
           (b ⤇
            Gel (f.0 a0 b.0) (f.1 a1 b.1)
              (c0 c1 ↦ P (b.0, b.1, b.2, c0, c1))) (fᵈ.0 a0 aᵈ0)
           (fᵈ.1 a1 aᵈ1))
        (a2 aᵈ2 ↦
         ¿Bᵈ≅.2 (f.2 a2) {f.0 a0} {f.1 a1} (b ⤇ Gel (f.0 a0 b.0) (f.1 a1 b.1) (c0 c1 ↦ f.2 a2 b.2 c0 c1)) {b0 ↦ eqv_idmap (f.0 a0 b0)} {b1 ↦ eqv_idmap (f.1 a1 b1)} ? ! (fᵈ.2 a2 aᵈ2)ʔ)
        (P Q H bᵈ2 ↦
         ¿Bᵈ≅.2 {f.0 a0} {f.1 a1} (b ⤇ Gel (f.0 a0 b.0) (f.1 a1 b.1) (c0 c1 ↦ P (b.0, b.1, b.2, c0, c1))) {f.0 a0} {f.1 a1}
  (b ⤇ Gel (f.0 a0 b.0) (f.1 a1 b.1) (c0 c1 ↦ Q (b.0, b.1, b.2, c0, c1))) {b0 ↦ eqv_idmap (f.0 a0 b0)} {b1 ↦ eqv_idmap (f.1 a1 b1)} ? {fᵈ.0 a0 aᵈ0} {fᵈ.1 a1 aᵈ1} bᵈ2 ʔ)
        ¿ʔ ]
