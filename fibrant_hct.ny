{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-discrete-coreflector") -*- `}

import "bookhott"
import "isfibrant"
import "hott_bookhott"
import "fibrant_types"

{` A generic recursive higher coinductive type with one higher field, one lower field, and one recursive lower field.  Note that the "spec" consisting of Γ, A, B, C, τ are modal, so they will not get degenerated in bridges. `}

def ℍ (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ) (x : Γ)
  : Type
  ≔ codata [
| s .fst.p : A x.0 x.1 x.2
| s .snd : B x
| s .thd.p : (c : C x.0 x.1 x.2) → ℍ Γ A B C τ (τ x.0 x.1 x.2 c) ]

{` eq-extensionality axiom `}

def eq_ℍ (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ) (x0 x1 : Γ)
  (x2 : eq Γ x0 x1) (u0 : ℍ Γ A B C τ x0) (u1 : ℍ Γ A B C τ x1)
  : Type
  ≔ codata [
| e .fst.p
  : match x2.2 [ rfl. ⤇ eq (A x0.0 x0.1 x0.2) (u0.2 .fst) (u1.2 .fst) ]
| e .snd : match x2 [ rfl. ↦ eq (B x0) (u0 .snd) (u1 .snd) ]
| e .thd.p
  : match x2.2 [
    | rfl. ⤇
        (c : C x0.0 x0.1 x0.2)
        → eq (ℍ Γ A B C τ (τ x0.0 x0.1 x0.2 c)) (u0.2 .thd c) (u1.2 .thd c)] ]

axiom ℍ_ext (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ) (x : Γ)
  (u0 u1 : ℍ Γ A B C τ x) (u2 : eq_ℍ Γ A B C τ x x rfl. u0 u1)
  : eqd Γ (ℍ Γ A B C τ) x x rfl. u0 u1

{` We also need a similar eq-extensionality principle for its bridges. `}

def eq_ℍᵖ (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ) (x00 x01 : Γ)
  (x02 : Br Γ x00 x01) (x10 x11 : Γ) (x12 : Br Γ x10 x11)
  (x20 : eq Γ x00 x10) (x21 : eq Γ x01 x11)
  (x22 : eq2d Γ Γ (x0 x1 ↦ Br Γ x0 x1) x00 x10 x20 x01 x11 x21 x02 x12)
  (u00 : ℍ Γ A B C τ x00) (u01 : ℍ Γ A B C τ x01)
  (u02 : Br (ℍ Γ A B C τ) x02 u00 u01) (u10 : ℍ Γ A B C τ x10)
  (u11 : ℍ Γ A B C τ x11) (u12 : Br (ℍ Γ A B C τ) x12 u10 u11)
  (u20 : eqd Γ (ℍ Γ A B C τ) x00 x10 x20 u00 u10)
  (u21 : eqd Γ (ℍ Γ A B C τ) x01 x11 x21 u01 u11)
  : Type
  ≔ codata [
| e .fst.p
  : match x20.2, x21.2, x22.2, u20.2, u21.2 [
    | rfl., rfl., rfl., rfl., rfl. ⤇
        eq (Br A x02.0 x02.1 (sym x02.2) (u00.2 .fst) (u01.2 .fst))
          (u02 .fst.2) (u12 .fst.2)]
| e .fst1
  : match x20, x21, x22 [
    | rfl., rfl., rfl. ↦ eq (A x00 x01 x02) (u02 .fst.1) (u12 .fst.1)]
| e .snd
  : match x20, x21, x22, u20, u21 [
    | rfl., rfl., rfl., rfl., rfl. ↦
        eq (Br B x02 (u00 .snd) (u01 .snd)) (u02 .snd) (u12 .snd)]
| e .thd.p
  : match x20.2, x21.2, x22.2, u20.2, u21.2 [
    | rfl., rfl., rfl., rfl., rfl. ⤇
        (c0 : C x00.0 x00.1 x00.2) (c1 : C x01.0 x01.1 x01.2)
        (c2 : Br C x02.0 x02.1 (sym x02.2) c0 c1)
        → eq
            (ℍ⁽ᵖ⁾ Γ A B C τ (rel τ x02.0 x02.1 (sym x02.2) c2)
               (u00.2 .thd c0) (u01.2 .thd c1)) (u02 .thd.2 c2)
            (u12 .thd.2 c2)]
| e .thd1
  : match x20, x21, x22 [
    | rfl., rfl., rfl. ↦
        (c : C x00 x01 x02)
        → eq (ℍ Γ A B C τ (τ x00 x01 x02 c)) (u02 .thd.1 c) (u12 .thd.1 c)] ]

axiom ℍᵖ_ext (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ) (x0 x1 : Γ)
  (x2 : Br Γ x0 x1) (u0 : ℍ Γ A B C τ x0) (u1 : ℍ Γ A B C τ x1)
  (u20 u21 : ℍ⁽ᵖ⁾ Γ A B C τ x2 u0 u1)
  (u22 : eq_ℍᵖ Γ A B C τ x0 x1 x2 x0 x1 x2 rfl. rfl. rfl. u0 u1 u20 u0 u1
           u21 rfl. rfl.)
  : eq (ℍ⁽ᵖ⁾ Γ A B C τ x2 u0 u1) u20 u21

{` The bridge type of a √ will be another √.  Here we define the spec Γ, A, and B for that. `}

def Γhat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ)
  : Type
  ≔ sig (
  x0 : Γ,
  x1 : Γ,
  x2 : Br Γ x0 x1,
  u0 : ℍ Γ A B C τ x0,
  u1 : ℍ Γ A B C τ x1 )

def Ahat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ)
  (y0 y1 : Γhat Γ A B C τ) (y2 : Br (Γhat Γ A B C τ) y0 y1)
  : Type
  ≔ Br A (y0 .x2) (y1 .x2) (sym (y2 .x2)) (y2 .u0 .fst) (y2 .u1 .fst)

def Bhat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ)
  (y : Γhat Γ A B C τ)
  : Type
  ≔ (A (y .x0) (y .x1) (y .x2) × Br B (y .x2) (y .u0 .snd) (y .u1 .snd))
    × ((c : C (y .x0) (y .x1) (y .x2))
       → ℍ Γ A B C τ (τ (y .x0) (y .x1) (y .x2) c))

{`
sig (
  a : A (y .x0) (y .x1) (y .x2),
  b : Br B (y .x2) (y .u0 .snd) (y .u1 .snd),
  c : (c : C (y .x0) (y .x1) (y .x2))
      → ℍ Γ A B C τ (τ (y .x0) (y .x1) (y .x2) c) )
 `}

def Chat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ)
  (y0 y1 : Γhat Γ A B C τ) (y2 : Br (Γhat Γ A B C τ) y0 y1)
  : Type
  ≔ Σ (C (y0 .x0) (y1 .x0) (y2 .x0) × C (y0 .x1) (y1 .x1) (y2 .x1))
      (c ↦ Br C (y0 .x2) (y1 .x2) (sym (y2 .x2)) (c .fst) (c .snd))

{`
sig (
  c0 : C (y0 .x0) (y1 .x0) (y2 .x0),
  c1 : C (y0 .x1) (y1 .x1) (y2 .x1),
  c2 : Br C (y0 .x2) (y1 .x2) (sym (y2 .x2)) c0 c1 )
 `}

def τhat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ)
  (y0 y1 : Γhat Γ A B C τ) (y2 : Br (Γhat Γ A B C τ) y0 y1)
  : Chat Γ A B C τ y0 y1 y2 → Γhat Γ A B C τ
  ≔ c ↦ (
  x0 ≔ τ (y0 .x0) (y1 .x0) (y2 .x0) (c .fst .fst),
  x1 ≔ τ (y0 .x1) (y1 .x1) (y2 .x1) (c .fst .snd),
  x2 ≔ rel τ (y0 .x2) (y1 .x2) (sym (y2 .x2)) (c .snd),
  u0 ≔ y2 .u0 .thd (c .fst .fst),
  u1 ≔ y2 .u1 .thd (c .fst .snd))

{` Now the isomorphism between Br ℍ and the other ℍ.  `}

def id_ℍ_iso_to (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ) (x0 x1 : Γ)
  (x2 : Br Γ x0 x1) (u0 : ℍ Γ A B C τ x0) (u1 : ℍ Γ A B C τ x1)
  : ℍ (Γhat Γ A B C τ) (Ahat Γ A B C τ) (Bhat Γ A B C τ) (Chat Γ A B C τ)
      (τhat Γ A B C τ) (x0, x1, x2, u0, u1)
    → Br (ℍ Γ A B C τ) x2 u0 u1
  ≔ v ↦ [
| .fst.p ⤇ v.2 .fst
| .fst.1 ⤇ v .snd .fst .fst
| .snd ⤇ v .snd .fst .snd
| .thd.p ⤇ c ⤇
    id_ℍ_iso_to Γ A B C τ (τ x0.0 x0.1 x0.2 c.0) (τ x1.0 x1.1 x1.2 c.1)
      (rel τ x2.0 x2.1 (sym x2.2) c.2) (u0.2 .thd c.0) (u1.2 .thd c.1)
      (v.2 .thd ((c.0, c.1), c.2))
| .thd.1 ⤇ v .snd .snd]

def id_ℍ_iso_fro (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ) (x0 x1 : Γ)
  (x2 : Br Γ x0 x1) (u0 : ℍ Γ A B C τ x0) (u1 : ℍ Γ A B C τ x1)
  : Br (ℍ Γ A B C τ) x2 u0 u1
    → ℍ (Γhat Γ A B C τ) (Ahat Γ A B C τ) (Bhat Γ A B C τ) (Chat Γ A B C τ)
        (τhat Γ A B C τ) (x0, x1, x2, u0, u1)
  ≔ u2 ↦ [
| .fst.p ↦ u2 .fst.2
| .snd ↦ ((u2 .fst.1, u2 .snd), u2 .thd.1)
| .thd.p ↦ c ↦
    let t
      ≔ τhat Γ A B C τ (x0.0, x1.0, x2.0, u0.0, u1.0)
          (x0.1, x1.1, x2.1, u0.1, u1.1) (x0.2, x1.2, x2.2, u0.2, u1.2) c
      in
    id_ℍ_iso_fro Γ A B C τ (t .x0) (t .x1) (t .x2) (t .u0) (t .u1)
      (u2 .thd.2 (c .snd))]

def id_ℍ_iso_fro_to (Γ :♭| Type)
  (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type) (B :♭| Γ → Type)
  (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ) (x0 x1 : Γ)
  (x2 : Br Γ x0 x1) (u0 : ℍ Γ A B C τ x0) (u1 : ℍ Γ A B C τ x1)
  (v : ℍ (Γhat Γ A B C τ) (Ahat Γ A B C τ) (Bhat Γ A B C τ)
         (Chat Γ A B C τ) (τhat Γ A B C τ) (x0, x1, x2, u0, u1))
  : eq.eq
      (ℍ (Γhat Γ A B C τ) (Ahat Γ A B C τ) (Bhat Γ A B C τ)
         (Chat Γ A B C τ) (τhat Γ A B C τ) (x0, x1, x2, u0, u1))
      (id_ℍ_iso_fro Γ A B C τ x0 x1 x2 u0 u1
         (id_ℍ_iso_to Γ A B C τ x0 x1 x2 u0 u1 v)) v
  ≔ ℍ_ext (Γhat Γ A B C τ) (Ahat Γ A B C τ) (Bhat Γ A B C τ)
      (Chat Γ A B C τ) (τhat Γ A B C τ) (x0, x1, x2, u0, u1)
      (id_ℍ_iso_fro Γ A B C τ x0 x1 x2 u0 u1
         (id_ℍ_iso_to Γ A B C τ x0 x1 x2 u0 u1 v)) v
      [ .fst.p ↦ rfl.
      | .snd ↦ rfl.
      | .thd.p ↦ c ↦
          id_ℍ_iso_fro_to Γ A B C τ (τ x0.0 x0.1 x0.2 (c .fst .fst))
            (τ x1.0 x1.1 x1.2 (c .fst .snd))
            (rel τ x2.0 x2.1 (sym x2.2) (c .snd)) (u0.2 .thd (c .fst .fst))
            (u1.2 .thd (c .fst .snd)) (v.2 .thd c)]

def id_ℍ_iso_to_fro (Γ :♭| Type)
  (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type) (B :♭| Γ → Type)
  (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ) (x0 x1 : Γ)
  (x2 : Br Γ x0 x1) (u0 : ℍ Γ A B C τ x0) (u1 : ℍ Γ A B C τ x1)
  (u2 : ℍ⁽ᵖ⁾ Γ A B C τ x2 u0 u1)
  : eq.eq (ℍ⁽ᵖ⁾ Γ A B C τ x2 u0 u1)
      (id_ℍ_iso_to Γ A B C τ x0 x1 x2 u0 u1
         (id_ℍ_iso_fro Γ A B C τ x0 x1 x2 u0 u1 u2)) u2
  ≔ ℍᵖ_ext Γ A B C τ x0 x1 x2 u0 u1
      (id_ℍ_iso_to Γ A B C τ x0 x1 x2 u0 u1
         (id_ℍ_iso_fro Γ A B C τ x0 x1 x2 u0 u1 u2)) u2
      [ .fst.p ↦ rfl.
      | .fst1 ↦ rfl.
      | .snd ↦ rfl.
      | .thd.p ↦ c0 c1 c2 ↦
          id_ℍ_iso_to_fro Γ A B C τ (τ x0.0 x0.1 x0.2 c0)
            (τ x1.0 x1.1 x1.2 c1) (rel τ x2.0 x2.1 (sym x2.2) c2)
            (u0.2 .thd c0) (u1.2 .thd c1) (sym u2.2 .thd.1 c2)
      | .thd1 ↦ c ↦ rfl.]

def id_ℍ_iso (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ) (x0 x1 : Γ)
  (x2 : Br Γ x0 x1) (u0 : ℍ Γ A B C τ x0) (u1 : ℍ Γ A B C τ x1)
  : ℍ (Γhat Γ A B C τ) (Ahat Γ A B C τ) (Bhat Γ A B C τ) (Chat Γ A B C τ)
      (τhat Γ A B C τ) (x0, x1, x2, u0, u1)
    ≅ Br (ℍ Γ A B C τ) x2 u0 u1
  ≔ adjointify
      (ℍ (Γhat Γ A B C τ) (Ahat Γ A B C τ) (Bhat Γ A B C τ)
         (Chat Γ A B C τ) (τhat Γ A B C τ) (x0, x1, x2, u0, u1))
      (ℍ⁽ᵖ⁾ Γ A B C τ x2 u0 u1) (id_ℍ_iso_to Γ A B C τ x0 x1 x2 u0 u1)
      (id_ℍ_iso_fro Γ A B C τ x0 x1 x2 u0 u1)
      (id_ℍ_iso_fro_to Γ A B C τ x0 x1 x2 u0 u1)
      (id_ℍ_iso_to_fro Γ A B C τ x0 x1 x2 u0 u1)

{` Finally, we can prove that ℍs are fibrant.  Note that the parameter type Γ is also required to be fibrant (although it would suffice to have connections). `}

def 𝕗ℍ (Γ :♭| Type) (𝕗Γ :♭| isFibrant Γ)
  (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (𝕗A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → isFibrant (A x₀ x₁ x₂))
  (B :♭| Γ → Type) (𝕗B :♭| (x : Γ) → isFibrant (B x))
  (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (𝕗C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → isFibrant (C x₀ x₁ x₂))
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ) (x : Γ)
  : isFibrant (ℍ Γ A B C τ x)
  ≔ [
| .trr.p ↦ u0 ↦ [
  | .fst.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .trr (u0.2 .fst)
  | .snd ↦ rel 𝕗B x.2 .trr (u0 .snd)
  | .thd.p ↦
      rel 𝕗Π (Br C x.20 x.21 (sym x.22))
          {c ↦ ℍ Γ A B C τ (τ x.00 x.01 x.02 c)}
          {c ↦ ℍ Γ A B C τ (τ x.10 x.11 x.12 c)}
          (c ⤇ Br ℍ Γ A B C τ (rel τ x.20 x.21 (sym x.22) c.2))
          (rel 𝕗C x.20 x.21 (sym x.22))
          {c ↦ 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (τ x.00 x.01 x.02 c)}
          {c ↦ 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (τ x.10 x.11 x.12 c)}
          (c ⤇
           rel 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (rel τ x.20 x.21 (sym x.22) c.2))
        .trr (u0.2 .thd)]
| .trl.p ↦ u1 ↦ [
  | .fst.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .trl (u1.2 .fst)
  | .snd ↦ rel 𝕗B x.2 .trl (u1 .snd)
  | .thd.p ↦
      rel 𝕗Π (Br C x.20 x.21 (sym x.22))
          {c ↦ ℍ Γ A B C τ (τ x.00 x.01 x.02 c)}
          {c ↦ ℍ Γ A B C τ (τ x.10 x.11 x.12 c)}
          (c ⤇ Br ℍ Γ A B C τ (rel τ x.20 x.21 (sym x.22) c.2))
          (rel 𝕗C x.20 x.21 (sym x.22))
          {c ↦ 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (τ x.00 x.01 x.02 c)}
          {c ↦ 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (τ x.10 x.11 x.12 c)}
          (c ⤇
           rel 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (rel τ x.20 x.21 (sym x.22) c.2))
        .trl (u1.2 .thd)]
| .liftr.p ↦ u0 ↦ [
  | .fst.p ⤇ rel 𝕗A x.20 x.21 (sym x.22) .liftr (u0.2 .fst)
  | .fst.1 ⤇
      rel 𝕗A (rel x.0) x.2 (coconn (Γ, 𝕗Γ) x.0 x.1 x.2) .trr (rel u0 .fst)
  | .snd ⤇ rel 𝕗B x.2 .liftr (u0 .snd)
  | .thd.p ↦
      rel 𝕗Π (Br C x.20 x.21 (sym x.22))
          {c ↦ ℍ Γ A B C τ (τ x.00 x.01 x.02 c)}
          {c ↦ ℍ Γ A B C τ (τ x.10 x.11 x.12 c)}
          (c ⤇ Br ℍ Γ A B C τ (rel τ x.20 x.21 (sym x.22) c.2))
          (rel 𝕗C x.20 x.21 (sym x.22))
          {c ↦ 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (τ x.00 x.01 x.02 c)}
          {c ↦ 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (τ x.10 x.11 x.12 c)}
          (c ⤇
           rel 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (rel τ x.20 x.21 (sym x.22) c.2))
        .liftr (u0.2 .thd)
  | .thd.1 ↦ c ↦
      rel 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ
          (rel τ (rel x.0) x.2 (coconn (Γ, 𝕗Γ) x.0 x.1 x.2)
             (rel 𝕗C (rel x.0) x.2 (coconn (Γ, 𝕗Γ) x.0 x.1 x.2) .liftl c))
        .trr
          (rel u0
           .thd.1
             (rel 𝕗C (rel x.0) x.2 (coconn (Γ, 𝕗Γ) x.0 x.1 x.2) .trl c))]
| .liftl.p ↦ u1 ↦ [
  | .fst.p ⤇ rel 𝕗A x.20 x.21 (sym x.22) .liftl (u1.2 .fst)
  | .fst.1 ⤇
      rel 𝕗A x.2 (rel x.1) (conn (Γ, 𝕗Γ) x.0 x.1 x.2) .trl (rel u1 .fst)
  | .snd ⤇ rel 𝕗B x.2 .liftl (u1 .snd)
  | .thd.p ↦
      rel 𝕗Π (Br C x.20 x.21 (sym x.22))
          {c ↦ ℍ Γ A B C τ (τ x.00 x.01 x.02 c)}
          {c ↦ ℍ Γ A B C τ (τ x.10 x.11 x.12 c)}
          (c ⤇ Br ℍ Γ A B C τ (rel τ x.20 x.21 (sym x.22) c.2))
          (rel 𝕗C x.20 x.21 (sym x.22))
          {c ↦ 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (τ x.00 x.01 x.02 c)}
          {c ↦ 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (τ x.10 x.11 x.12 c)}
          (c ⤇
           rel 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (rel τ x.20 x.21 (sym x.22) c.2))
        .liftl (u1.2 .thd)
  | .thd.1 ↦ c ↦
      rel 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ
          (rel τ x.2 (rel x.1) (conn (Γ, 𝕗Γ) x.0 x.1 x.2)
             (rel 𝕗C x.2 (rel x.1) (conn (Γ, 𝕗Γ) x.0 x.1 x.2) .liftr c))
        .trl
          (rel u1
           .thd.1 (rel 𝕗C x.2 (rel x.1) (conn (Γ, 𝕗Γ) x.0 x.1 x.2) .trr c))]
| .id.p ↦ u0 u1 ↦
    𝕗eqv
      (ℍ (Γhat Γ A B C τ) (Ahat Γ A B C τ) (Bhat Γ A B C τ)
         (Chat Γ A B C τ) (τhat Γ A B C τ) (x.0, x.1, x.2, u0, u1))
      (ℍ⁽ᵖ⁾ Γ A B C τ x.2 u0 u1) (id_ℍ_iso Γ A B C τ x.0 x.1 x.2 u0 u1)
      (𝕗ℍ (Γhat Γ A B C τ) (𝕗Γhat Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ) (Ahat Γ A B C τ)
         (y0 y1 y2 ↦
          rel 𝕗A (y0 .2) (y1 .2) (sym (y2 .2))
          .id (y2 .u0 .fst) (y2 .u1 .fst)) (Bhat Γ A B C τ)
         (y ↦
          𝕗prod
            (A (y .x0) (y .x1) (y .x2)
             × Br B (y .x2) (y .u0 .snd) (y .u1 .snd))
            ((c : C (y .x0) (y .x1) (y .x2))
             → ℍ Γ A B C τ (τ (y .x0) (y .x1) (y .x2) c))
            (𝕗prod (A (y .x0) (y .x1) (y .x2))
               (Br B (y .x2) (y .u0 .snd) (y .u1 .snd))
               (𝕗A (y .0) (y .1) (y .2))
               (rel 𝕗B (y .2) .id (y .u0 .snd) (y .u1 .snd)))
            (𝕗Π (C (y .x0) (y .x1) (y .x2))
               (c ↦ ℍ Γ A B C τ (τ (y .x0) (y .x1) (y .x2) c))
               (𝕗C (y .x0) (y .x1) (y .x2))
               (c ↦ 𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (τ (y .x0) (y .x1) (y .x2) c))))
         (Chat Γ A B C τ)
         (y0 y1 y2 ↦
          𝕗Σ (C (y0 .x0) (y1 .x0) (y2 .x0) × C (y0 .x1) (y1 .x1) (y2 .x1))
            (c ↦ Br C (y0 .x2) (y1 .x2) (sym (y2 .x2)) (c .fst) (c .snd))
            (𝕗prod (C (y0 .x0) (y1 .x0) (y2 .x0))
               (C (y0 .x1) (y1 .x1) (y2 .x1))
               (𝕗C (y0 .x0) (y1 .x0) (y2 .x0))
               (𝕗C (y0 .x1) (y1 .x1) (y2 .x1)))
            (c ↦
             rel 𝕗C (y0 .x2) (y1 .x2) (sym (y2 .x2)) .id (c .fst) (c .snd)))
         (τhat Γ A B C τ) (x.0, x.1, x.2, u0, u1))]

{` Since Γhat involves ℍ, we have to prove mutually that Γhat is also fibrant.  I haven't thought about generator tricks to ensure this is productive. `}

and 𝕗Γhat (Γ :♭| Type) (𝕗Γ :♭| isFibrant Γ)
  (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (𝕗A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → isFibrant (A x₀ x₁ x₂))
  (B :♭| Γ → Type) (𝕗B :♭| (x : Γ) → isFibrant (B x))
  (C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (𝕗C :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → isFibrant (C x₀ x₁ x₂))
  (τ :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ)
  : isFibrant (Γhat Γ A B C τ)
  ≔ 𝕗eqv
      (Σ (Γ × Γ)
         (x ↦
          Br Γ (x .0) (x .1) × (ℍ Γ A B C τ (x .0) × ℍ Γ A B C τ (x .1))))
      (Γhat Γ A B C τ)
      (to ≔ x ↦ (x .0 .0, x .0 .1, x .1 .0, x .1 .1 .0, x .1 .1 .1),
       fro ≔ x ↦ ((x .0, x .1), (x .2, (x .3, x .4))),
       fro_to ≔ _ ↦ rfl.,
       to_fro ≔ _ ↦ rfl.,
       to_fro_to ≔ _ ↦ rfl.)
      (𝕗Σ (Γ × Γ)
         (x ↦
          Br Γ (x .fst) (x .snd)
          × (ℍ Γ A B C τ (x .fst) × ℍ Γ A B C τ (x .snd)))
         (𝕗prod Γ Γ 𝕗Γ 𝕗Γ)
         (x ↦
          𝕗prod (Br Γ (x .fst) (x .snd))
            (ℍ Γ A B C τ (x .fst) × ℍ Γ A B C τ (x .snd))
            (rel 𝕗Γ .id (x .0) (x .1))
            (𝕗prod (ℍ Γ A B C τ (x .fst)) (ℍ Γ A B C τ (x .snd))
               (𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (x .0))
               (𝕗ℍ Γ 𝕗Γ A 𝕗A B 𝕗B C 𝕗C τ (x .1)))))
