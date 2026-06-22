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
| x .iso : A → A → Type
| x .id.p : (a0 : A.0) (a1 : A.1) → has≅ (A.2 a0 a1) ]

{` Bridges work. `}
def has≅_Br (A : Type) : has≅ A ≔ [
| .iso ↦ a0 a1 ↦ Br A a0 a1
| .id.p ↦ a0 a1 ↦ has≅_Br (A.2 a0 a1)]

{` But in addition, we can pull back any notion of isomorphism across a function. `}

def has≅_fun (A B : Type) (e : B → A) (iA : has≅ A) : has≅ B ≔ [
| .iso ↦ b0 b1 ↦ iA .iso (e b0) (e b1)
| .id.p ↦ b0 b1 ↦
    has≅_fun (A.2 (e.0 b0) (e.1 b1)) (B.2 b0 b1) (b2 ↦ e.2 b2)
      (iA.2 .id (e.0 b0) (e.1 b1))]

{` Families have a pointwise notion of isomorphism (obtained coinductively by pulling back along instantiation).  Note that this is the minimum level of generality necessary to deduce [has≅ Type].  It doesn't seem possible to prove that a general function-type [B → C] inherits isomorphisms from [C], because in the coinductive step [B] gets degenerated and the functions become dependent. `}

def has≅_fam (B : Type) : has≅ (B → Type) ≔ [
| .iso ↦ R0 R1 ↦ (b : B) → R0 b ≅ R1 b
| .id.p ↦ R0 R1 ↦
    has≅_fun (B̂ B.0 B.1 B.2 R0 R1 → Type)
      ({𝑥₀ : B.0} {𝑥₁ : B.1} (𝑥₂ : B.2 𝑥₀ 𝑥₁) →⁽ᵖ⁾ Type⁽ᵖ⁾ (R0 𝑥₀) (R1 𝑥₁))
      (R2 u ↦ R2 (u .2) (u .3) (u .4)) (has≅_fam (B̂ B.0 B.1 B.2 R0 R1))]

def has≅_Type : has≅ Type
  ≔ has≅_fun (⊤ → Type) Type (X ↦ _ ↦ X) (has≅_fam ⊤)

def has≅× (A : Type) (iA : has≅ A) (B : Type) (iB : has≅ B) : has≅ (A × B)
  ≔ [
| .iso ↦ u0 u1 ↦ iA .iso (u0 .0) (u1 .0) × iB .iso (u0 .1) (u1 .1)
| .id.p ↦ u0 u1 ↦
    has≅_fun (A.2 (u0 .fst) (u1 .fst) × B.2 (u0 .snd) (u1 .snd))
      (prod⁽ᵖ⁾ A.2 B.2 u0 u1) (u ↦ (u .0, u .1))
      (has≅× (A.2 (u0 .0) (u1 .0)) (iA.2 .id (u0 .0) (u1 .0))
         (B.2 (u0 .1) (u1 .1)) (iB.2 .id (u0 .1) (u1 .1)))]

{` A dependent notion of "isomorphism over isomorphism" `}

def has≅ᵈ (A : Type) (iA : has≅ A) (Aᵈ : A → Type) : Type ≔ codata [
| x .iso : (a0 a1 : A) (a2 : iA .iso a0 a1) → Aᵈ a0 → Aᵈ a1 → Type
| x .id.p
  : (a0 : A.0) (a1 : A.1) (aᵈ0 : Aᵈ.0 a0) (aᵈ1 : Aᵈ.1 a1)
    → has≅ᵈ (A.2 a0 a1) (iA.2 .id a0 a1) (a2 ↦ Aᵈ.2 a2 aᵈ0 aᵈ1) ]

def has≅_Σ (A : Type) (iA : has≅ A) (Aᵈ : A → Type) (iAᵈ : has≅ᵈ A iA Aᵈ)
  : has≅ (Σ A Aᵈ)
  ≔ [
| .iso ↦ u0 u1 ↦
    Σ (iA .iso (u0 .0) (u1 .0))
      (a2 ↦ iAᵈ .iso (u0 .0) (u1 .0) a2 (u0 .1) (u1 .1))
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
| s .surjeq : (b : B) → iB .iso (f (s .surj b)) b
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
| .surjeq ↦ A2 a ↦ Gel_iso′ A0 A1 (a0 a1 ↦ A2 (a0, a1)) (a .0) (a .1)
| .id.p ↦ A20 A21 ↦ [
  | .surj ↦ A22 ↦
      Gel2 A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 A20 A21
        (a00 a01 a02 a10 a11 a12 a20 a21 ↦
         A22 {(a00, a10)} {(a01, a11)} (a02, a12) a20 a21)
  | .surjeq ↦ A22 ↦ u ↦
      Gel2_iso′ A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 A20 A21
        (a00 a01 a02 a10 a11 a12 a20 a21 ↦
         A22 {(a00, a10)} {(a01, a11)} (a02, a12) a20 a21) (u .0 .0)
        (u .1 .0) (u .2 .0) (u .0 .1) (u .1 .1) (u .2 .1) (u .3) (u .4)
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
| t .surjeq
  : (b : B) (bᵈ : Bᵈ b)
    → iBᵈ .iso (f (s .surj b)) b (s .surjeq b)
        (fᵈ (s .surj b) (t .surj b bᵈ)) bᵈ
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
| .surjeq ↦ v ↦ (s .surjeq (v .0), sᵈ .surjeq (v .0) (v .1))
| .id.p ↦ u0 u1 ↦ ¿ʔ] ` transfer across iso

{` We define isFibrant to have "dependent isomorphisms" that say that the fibrancy structure is preserved by transfer across isomorphisms in the base.  `}

def has≅_isfib (B : Type)
  : has≅ᵈ (B → Type) (has≅_fam B) (P ↦ (b : B) → isFibrant (P b))
  ≔ [
| .iso ↦
  R0 R1 R2 R0f R1f ↦
  {` Since a single witness of fibrancy is a coinductive structure, likewise the notion of a single isomorphism between fibrancy witnesses is coinductive. `}
  codata [
  | R2f .trr.p
    : (b0 : B.0) (b1 : B.1) (b2 : B.2 b0 b1) (r0 : R1.0 b0)
      → eq (R0.1 b1) (R2.1 b1 .fro (R1f.2 b2 .trr r0))
          (R0f.2 b2 .trr (R2.0 b0 .fro r0))
  | R2f .liftr.p
    : (b0 : B.0) (b1 : B.1) (b2 : B.2 b0 b1) (r0 : R1.0 b0)
      → eqd (R0.1 b1) (r1 ↦ R0.2 b2 (R2.0 b0 .fro r0) r1)
          (R2.1 b1 .fro (R1f.2 b2 .trr r0))
          (R0f.2 b2 .trr (R2.0 b0 .fro r0)) (R2f .trr b0 b1 b2 r0)
          (Id_eqv (R0.0 b0) (R0.1 b1) (R0.2 b2) (R1.0 b0) (R1.1 b1)
               (R1.2 b2) (R2.0 b0) (R2.1 b1) (R2.2 b2) r0
               (R1f.2 b2 .trr r0)
           .fro (R1f.2 b2 .liftr r0)) (R0f.2 b2 .liftr (R2.0 b0 .fro r0))
  | R2f .trl.p
    : (b0 : B.0) (b1 : B.1) (b2 : B.2 b0 b1) (r1 : R1.1 b1)
      → eq (R0.0 b0) (R2.0 b0 .fro (R1f.2 b2 .trl r1))
          (R0f.2 b2 .trl (R2.1 b1 .fro r1))
  | R2f .liftl.p
    : (b0 : B.0) (b1 : B.1) (b2 : B.2 b0 b1) (r1 : R1.1 b1)
      → eqd (R0.0 b0) (r0 ↦ R0.2 b2 r0 (R2.1 b1 .fro r1))
          (R2.0 b0 .fro (R1f.2 b2 .trl r1))
          (R0f.2 b2 .trl (R2.1 b1 .fro r1)) (R2f .trl b0 b1 b2 r1)
          (Id_eqv (R0.0 b0) (R0.1 b1) (R0.2 b2) (R1.0 b0) (R1.1 b1)
               (R1.2 b2) (R2.0 b0) (R2.1 b1) (R2.2 b2) (R1f.2 b2 .trl r1)
               r1
           .fro (R1f.2 b2 .liftl r1)) (R0f.2 b2 .liftl (R2.1 b1 .fro r1))
  | R2f .id.p
    : has≅_isfib (B̂ B.0 B.1 B.2 R1.0 R1.1)
    .iso
      (u ↦
       (R0.2 (u .b2) (R2.0 (u .b0) .fro (u .c0))
          (R2.1 (u .b1) .fro (u .c1)))) (u ↦ (R1.2 (u .2) (u .3) (u .4)))
      (u ↦
       (Id_eqv (R0.0 (u .0)) (R0.1 (u .1)) (R0.2 (u .2)) (R1.0 (u .0))
          (R1.1 (u .1)) (R1.2 (u .2)) (R2.0 (u .0)) (R2.1 (u .1))
          (R2.2 (u .2)) (u .3) (u .4)))
      (u ↦
       R0f.2 (u .2) .id (R2.0 (u .0) .fro (u .3)) (R2.1 (u .1) .fro (u .4)))
      (u ↦ R1f.2 (u .2) .id (u .3) (u .4)) ]
{` This piece would require generalizing the statement from isFibrant to a wider class of coinductive predicates. `}
| .id.p ↦ ¿ʔ]

{` Using this, we can prove the first cases of the previous "vsurjd_lemma" *without* using any computational properties of vsurj_gel, only its type. `}

def vsurjᵈ_gel_isfib (A0 A1 : Type) (A0f : isFibrant A0)
  (A1f : isFibrant A1)
  : vsurjᵈ (Br Type A0 A1) (A0 × A1 → Type) (has≅_fam (A0 × A1))
      (A2 ↦ a ↦ A2 (a .0) (a .1)) (vsurj_gel A0 A1)
      (A2 ↦ (a0 : A0) (a1 : A1) → isFibrant (A2 a0 a1))
      (A2 ↦ (a : A0 × A1) → isFibrant (A2 (a .0, a .1)))
      (has≅_isfib (A0 × A1)) (A2 A2f a ↦ A2f (a .0) (a .1))
  ≔ [
| .surj ↦ A2 A2f a0 a1 ↦
    𝕗eqv (A2 (a0, a1)) (vsurj_gel A0 A1 .surj A2 a0 a1)
      (inverse_eqv (vsurj_gel A0 A1 .surj A2 a0 a1) (A2 (a0, a1))
         (vsurj_gel A0 A1 .surjeq A2 (a0, a1))) (A2f (a0, a1))
| .surjeq ↦ A2 A2f ↦ [
  | .trr.p ↦ a0 a1 a2 a02 ↦
      eq.ap (A2.0 a0) (vsurj_gel A0.1 A1.1 .surj A2.1 (a1 .fst) (a1 .snd))
        (a02′ ↦
         vsurj_gel A0.1 A1.1 .surjeq A2.1 a1 .fro (A2f.2 a2 .trr a02′)) a02
        (vsurj_gel A0.0 A1.0
         .surjeq A2.0 a0
         .to (vsurj_gel A0.0 A1.0 .surjeq A2.0 a0 .fro a02))
        (eq.inv (A2.0 a0)
           (vsurj_gel A0.0 A1.0
            .surjeq A2.0 a0
            .to (vsurj_gel A0.0 A1.0 .surjeq A2.0 a0 .fro a02)) a02
           (vsurj_gel A0.0 A1.0 .surjeq A2.0 a0 .to_fro a02))
  {` The rest of these are messy path algebra, but should be possible. `}
  | .liftr.p ↦ ¿ʔ
  | .trl.p ↦ ¿ʔ
  | .liftl.p ↦ ¿ʔ
  {` To prove this, we probably want to pull out some more general corecursive lemma about proving isomorphism of fibrancy witnesses. `}
  | .id.p ↦ ¿ʔ]
{` Again, this case requires generalizing from isFibrant to a wider class of coinductive predicates. `}
| .id.p ↦ ¿ʔ]
