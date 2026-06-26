{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"
import "univalence"

{` Stuff that should go elsewhere `}

def mapΣ (A B : Type) (f : A → B) (Aᵈ : A → Type) (Bᵈ : B → Type)
  (fᵈ : (x : A) → Aᵈ x → Bᵈ (f x))
  : Σ A Aᵈ → Σ B Bᵈ
  ≔ u ↦ (f (u .fst), fᵈ (u .fst) (u .snd))

def BR (A0 : Type) (A1 : Type) (A2 : Br Type A0 A1) : Type ≔ sig (
  a0 : A0,
  a1 : A1,
  a2 : A2 a0 a1 )

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

{` Types equipped with a notion of "isomorphism" `}

def has≅ (A : Type) : Type ≔ codata [
| x .iso.p : A.0 → A.1 → Type
| x .id.p : (a0 : A.0) (a1 : A.1) → has≅ (A.2 a0 a1) ]

{` Bridges work. `}
def has≅_Br (A : Type) : has≅ A ≔ [
| .iso.p ↦ a0 a1 ↦ A.2 a0 a1
| .id.p ↦ a0 a1 ↦ has≅_Br (A.2 a0 a1)]

{` But in addition, we can pull back any notion of isomorphism across a function. `}

def has≅_fun (A B : Type) (e : B → A) (iA : has≅ A) : has≅ B ≔ [
| .iso.p ↦ b0 b1 ↦ iA.2 .iso (e.0 b0) (e.1 b1)
| .id.p ↦ b0 b1 ↦
    has≅_fun (A.2 (e.0 b0) (e.1 b1)) (B.2 b0 b1) (b2 ↦ e.2 b2)
      (iA.2 .id (e.0 b0) (e.1 b1))]

{` Families have a pointwise notion of isomorphism (obtained coinductively by pulling back along instantiation).  Note that this is the minimum level of generality necessary to deduce [has≅ Type].  It doesn't seem possible to prove that a general function-type [B → C] inherits isomorphisms from [C], because in the coinductive step [B] gets degenerated and the functions become dependent. `}

def has≅_fam (B : Type) : has≅ (B → Type) ≔ [
| .iso.p ↦ R0 R1 ↦ (b0 : B.0) (b1 : B.1) (b2 : B.2 b0 b1) ⇒ R0 b0 ≅ R1 b1
| .id.p ↦ R0 R1 ↦
    has≅_fun (B̂ B.0 B.1 B.2 R0 R1 → Type)
      ({𝑥₀ : B.0} {𝑥₁ : B.1} (𝑥₂ : B.2 𝑥₀ 𝑥₁) →⁽ᵖ⁾ Type⁽ᵖ⁾ (R0 𝑥₀) (R1 𝑥₁))
      (R2 u ↦ R2 (u .2) (u .3) (u .4)) (has≅_fam (B̂ B.0 B.1 B.2 R0 R1))]

def has≅_Type : has≅ Type
  ≔ has≅_fun (⊤ → Type) Type (X ↦ _ ↦ X) (has≅_fam ⊤)

def has≅× (A : Type) (iA : has≅ A) (B : Type) (iB : has≅ B) : has≅ (A × B)
  ≔ [
| .iso.p ↦ u0 u1 ↦ iA.2 .iso (u0 .0) (u1 .0) × iB.2 .iso (u0 .1) (u1 .1)
| .id.p ↦ u0 u1 ↦
    has≅_fun (A.2 (u0 .fst) (u1 .fst) × B.2 (u0 .snd) (u1 .snd))
      (prod⁽ᵖ⁾ A.2 B.2 u0 u1) (u ↦ (u .0, u .1))
      (has≅× (A.2 (u0 .0) (u1 .0)) (iA.2 .id (u0 .0) (u1 .0))
         (B.2 (u0 .1) (u1 .1)) (iB.2 .id (u0 .1) (u1 .1)))]

{` Family isomorphisms imply bridges, by gelling `}

def Br_of_≅fam (B0 B1 : Type) (B2 : Br Type B0 B1) (P0 : B0 → Type)
  (P1 : B1 → Type) (e : rel has≅_fam B2 .iso P0 P1) (b0 : B0) (b1 : B1)
  (b2 : B2 b0 b1)
  : Br Type (P0 b0) (P1 b1)
  ≔ Gel (P0 b0) (P1 b1) (p0 p1 ↦ Br (P1 b1) (e b0 b1 b2 .to p0) p1)

{` A dependent notion of "isomorphism over isomorphism" `}

def has≅ᵈ (A : Type) (iA : has≅ A) (Aᵈ : A → Type) : Type ≔ codata [
| x .iso.p
  : (a0 : A.0) (a1 : A.1) (a2 : iA.2 .iso a0 a1) → Aᵈ.0 a0 → Aᵈ.1 a1 → Type
| x .id.p
  : (a0 : A.0) (a1 : A.1) (aᵈ0 : Aᵈ.0 a0) (aᵈ1 : Aᵈ.1 a1)
    → has≅ᵈ (A.2 a0 a1) (iA.2 .id a0 a1) (a2 ↦ Aᵈ.2 a2 aᵈ0 aᵈ1) ]

def has≅_Σ (A : Type) (iA : has≅ A) (Aᵈ : A → Type) (iAᵈ : has≅ᵈ A iA Aᵈ)
  : has≅ (Σ A Aᵈ)
  ≔ [
| .iso.p ↦ u0 u1 ↦
    Σ (iA.2 .iso (u0 .0) (u1 .0))
      (a2 ↦ iAᵈ.2 .iso (u0 .0) (u1 .0) a2 (u0 .1) (u1 .1))
| .id.p ↦ u0 u1 ↦
    has≅_fun
      (Σ (A.2 (u0 .fst) (u1 .fst)) (a2 ↦ Aᵈ.2 a2 (u0 .snd) (u1 .snd)))
      (Σ⁽ᵖ⁾ A.2 Aᵈ.2 u0 u1) (u2 ↦ (u2 .0, u2 .1))
      (has≅_Σ (A.2 (u0 .0) (u1 .0)) (iA.2 .id (u0 .0) (u1 .0))
         (a2 ↦ Aᵈ.2 a2 (u0 .1) (u1 .1))
         (iAᵈ.2 .id (u0 .0) (u1 .0) (u0 .1) (u1 .1)))]

{` Very-surjectivity up to such specified "isomorphisms". `}

def vsurj (A B : Type) (iB : has≅ B) (f : A → B) : Type ≔ codata [
| s .surj : B → A
| s .surjeq.p
  : (b0 : B.0) (b1 : B.1) (b2 : iB.2 .iso b0 b1)
    → iB.2 .iso (f.0 (s.0 .surj b0)) b1
| s .id.p
  : (a0 : A.0) (a1 : A.1)
    → vsurj (A.2 a0 a1) (B.2 (f.0 a0) (f.1 a1)) (iB .id (f.0 a0) (f.1 a1))
        (a2 ↦ f.2 a2) ]

{` This allows us to state that instantiation is very surjective "up to pointwise isomorphisms" rather than just up to bridges.  This should be just as easy to build into Narya as the bridge-based version, if not easier. `}

def vsurj_gel (A0 A1 : Type)
  : vsurj (Br Type A0 A1) (A0 × A1 → Type) (has≅_fam (A0 × A1))
      (A2 ↦ a ↦ A2 (a .0) (a .1))
  ≔ [
| .surj ↦ A2 ↦ Gel A0 A1 (a0 a1 ↦ A2 (a0, a1))
| .surjeq.p ↦ A20 A21 A22 a0 a1 a2 ↦
    comp_eqv (Gel A0.0 A1.0 (a0′ a1′ ↦ A20 (a0′, a1′)) (a0 .fst) (a0 .snd))
      (A20 a0) (A21 a1)
      (Gel_iso′ A0.0 A1.0 (a0 a1 ↦ A20 (a0, a1)) (a0 .0) (a0 .1))
      (A22 a0 a1 a2)
| .id.p ↦ A20 A21 ↦ [
  | .surj ↦ A22 ↦
      Gel2 A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 A20 A21
        (a00 a01 a02 a10 a11 a12 a20 a21 ↦
         A22 {(a00, a10)} {(a01, a11)} (a02, a12) a20 a21)
  | .surjeq.p ↦ A220 A221 A222 u0 u1 u2 ↦
      comp_eqv
        (Gel2 A0.00 A0.10 A0.20 A1.00 A1.10 A1.20 A20.0 A21.0
           (a00 a01 a02 a10 a11 a12 a20 a21 ↦
            A220 {(a00, a10)} {(a01, a11)} (a02, a12) a20 a21)
           (u0 .b2 .fst) (u0 .b2 .snd) (u0 .c0) (u0 .c1))
        (A220 (u0 .2) (u0 .3) (u0 .4)) (A221 (u1 .2) (u1 .3) (u1 .4))
        (Gel2_iso′ A0.00 A0.10 A0.20 A1.00 A1.10 A1.20 A20.0 A21.0
           (a00 a01 a02 a10 a11 a12 a20 a21 ↦
            A220 {(a00, a10)} {(a01, a11)} (a02, a12) a20 a21) (u0 .0 .0)
           (u0 .1 .0) (u0 .2 .0) (u0 .0 .1) (u0 .1 .1) (u0 .2 .1) (u0 .3)
           (u0 .4)) (A222 u0 u1 u2)
  | .id.p ↦ ¿ʔ]]

{` However, let's assume it as an axiom now, to see whether we can do without its infinite computational behavior.  (This shadows the previous definition, with a warning.) `}
axiom vsurj_gel (A0 A1 : Type)
  : vsurj (Br Type A0 A1) (A0 × A1 → Type) (has≅_fam (A0 × A1))
      (A2 ↦ a ↦ A2 (a .0) (a .1))

def vsurjᵈ (A B : Type) (iB : has≅ B) (f : A → B) (s : vsurj A B iB f)
  (Aᵈ : A → Type) (Bᵈ : B → Type) (iBᵈ : has≅ᵈ B iB Bᵈ)
  (fᵈ : (a : A) → Aᵈ a → Bᵈ (f a))
  : Type
  ≔ codata [
| t .surj : (b : B) → Bᵈ b → Aᵈ (s .surj b)
| t .surjeq.p
  : (b0 : B.0) (b1 : B.1) (b2 : iB.2 .iso b0 b1) (bᵈ0 : Bᵈ.0 b0)
    (bᵈ1 : Bᵈ.1 b1) (bᵈ2 : iBᵈ.2 .iso b0 b1 b2 bᵈ0 bᵈ1)
    → iBᵈ.2 .iso (f.0 (s.0 .surj b0)) b1 (s.2 .surjeq b0 b1 b2)
        (fᵈ.0 (s.0 .surj b0) (t.0 .surj b0 bᵈ0)) bᵈ1
| t .id.p
  : (a0 : A.0) (a1 : A.1) (aᵈ0 : Aᵈ.0 a0) (aᵈ1 : Aᵈ.1 a1)
    → vsurjᵈ (A.2 a0 a1) (B.2 (f.0 a0) (f.1 a1)) (iB .id (f.0 a0) (f.1 a1))
        (a2 ↦ f.2 a2) (s .id a0 a1) (a2 ↦ Aᵈ.2 a2 aᵈ0 aᵈ1)
        (b2 ↦ Bᵈ.2 b2 (fᵈ.0 a0 aᵈ0) (fᵈ.1 a1 aᵈ1))
        (iBᵈ .id (f.0 a0) (f.1 a1) (fᵈ.0 a0 aᵈ0) (fᵈ.1 a1 aᵈ1))
        (a2 aᵈ2 ↦ fᵈ.2 a2 aᵈ2) ]

def vsurj_Σ (A B : Type) (iB : has≅ B) (f : A → B) (s : vsurj A B iB f)
  (Aᵈ : A → Type) (Bᵈ : B → Type) (iBᵈ : has≅ᵈ B iB Bᵈ)
  (fᵈ : (a : A) → Aᵈ a → Bᵈ (f a)) (sᵈ : vsurjᵈ A B iB f s Aᵈ Bᵈ iBᵈ fᵈ)
  : vsurj (Σ A Aᵈ) (Σ B Bᵈ) (has≅_Σ B iB Bᵈ iBᵈ) (mapΣ A B f Aᵈ Bᵈ fᵈ)
  ≔ [
| .surj ↦ v ↦ (s .surj (v .0), sᵈ .surj (v .0) (v .1))
| .surjeq.p ↦ v0 v1 v2 ↦ (
    s .surjeq (v0 .0) (v1 .0) (v2 .0),
    sᵈ .surjeq (v0 .0) (v1 .0) (v2 .0) (v0 .1) (v1 .1) (v2 .1))
| .id.p ↦ u0 u1 ↦ ¿ʔ] ` transfer across iso
