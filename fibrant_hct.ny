{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-discrete-coreflector") -*- `}

import "bookhott"
import "isfibrant"
import "hott_bookhott"
import "fibrant_types"
import "condfib"

{` A generic recursive higher coinductive type with one higher field, one lower field, and one recursive lower field.  Note that the "spec" consisting of Γ, A, B, C, τ are modal, so they will not get degenerated in bridges. `}

def ℍspec : Type ≔ sig (
  Γ : Type,
  A : (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type,
  B : Γ → Type,
  C : (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type,
  τ : (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → C x₀ x₁ x₂ → Γ )

def ℍ (S :♭| ℍspec) (x : S .Γ) : Type ≔ codata [
| s .fst.p : S .A x.0 x.1 x.2
| s .snd : S .B x
| s .thd.p : (c : S .C x.0 x.1 x.2) → ℍ S (S .τ x.0 x.1 x.2 c) ]

{` eq-extensionality axiom `}

def eq_ℍ (S :♭| ℍspec) (x0 x1 : S .Γ) (x2 : eq (S .Γ) x0 x1) (u0 : ℍ S x0)
  (u1 : ℍ S x1)
  : Type
  ≔ codata [
| e .fst.p
  : match x2.2 [ rfl. ⤇ eq (S .A x0.0 x0.1 x0.2) (u0.2 .fst) (u1.2 .fst) ]
| e .snd : match x2 [ rfl. ↦ eq (S .B x0) (u0 .snd) (u1 .snd) ]
| e .thd.p
  : match x2.2 [
    | rfl. ⤇
        (c : S .C x0.0 x0.1 x0.2)
        → eq (ℍ S (S .τ x0.0 x0.1 x0.2 c)) (u0.2 .thd c) (u1.2 .thd c)] ]

axiom ℍ_ext (S :♭| ℍspec) (x : S .Γ) (u0 u1 : ℍ S x)
  (u2 : eq_ℍ S x x rfl. u0 u1)
  : eqd (S .Γ) (ℍ S) x x rfl. u0 u1

{` We also need a similar eq-extensionality principle for its bridges. `}

def eq_ℍᵖ (S :♭| ℍspec) (x00 x01 : S .Γ) (x02 : Br (S .Γ) x00 x01)
  (x10 x11 : S .Γ) (x12 : Br (S .Γ) x10 x11) (x20 : eq (S .Γ) x00 x10)
  (x21 : eq (S .Γ) x01 x11)
  (x22 : eq2d (S .Γ) (S .Γ) (x0 x1 ↦ Br (S .Γ) x0 x1) x00 x10 x20 x01 x11
           x21 x02 x12) (u00 : ℍ S x00) (u01 : ℍ S x01)
  (u02 : Br (ℍ S) x02 u00 u01) (u10 : ℍ S x10) (u11 : ℍ S x11)
  (u12 : Br (ℍ S) x12 u10 u11) (u20 : eqd (S .Γ) (ℍ S) x00 x10 x20 u00 u10)
  (u21 : eqd (S .Γ) (ℍ S) x01 x11 x21 u01 u11)
  : Type
  ≔ codata [
| e .fst.p
  : match x20.2, x21.2, x22.2, u20.2, u21.2 [
    | rfl., rfl., rfl., rfl., rfl. ⤇
        eq (Br (S .A) x02.0 x02.1 (sym x02.2) (u00.2 .fst) (u01.2 .fst))
          (u02 .fst.2) (u12 .fst.2)]
| e .fst1
  : match x20, x21, x22 [
    | rfl., rfl., rfl. ↦ eq (S .A x00 x01 x02) (u02 .fst.1) (u12 .fst.1)]
| e .snd
  : match x20, x21, x22, u20, u21 [
    | rfl., rfl., rfl., rfl., rfl. ↦
        eq (Br (S .B) x02 (u00 .snd) (u01 .snd)) (u02 .snd) (u12 .snd)]
| e .thd.p
  : match x20.2, x21.2, x22.2, u20.2, u21.2 [
    | rfl., rfl., rfl., rfl., rfl. ⤇
        (c0 : S .C x00.0 x00.1 x00.2) (c1 : S .C x01.0 x01.1 x01.2)
        (c2 : Br (S .C) x02.0 x02.1 (sym x02.2) c0 c1)
        → eq
            (ℍ⁽ᵖ⁾ S (rel (S .τ) x02.0 x02.1 (sym x02.2) c2) (u00.2 .thd c0)
               (u01.2 .thd c1)) (u02 .thd.2 c2) (u12 .thd.2 c2)]
| e .thd1
  : match x20, x21, x22 [
    | rfl., rfl., rfl. ↦
        (c : S .C x00 x01 x02)
        → eq (ℍ S (S .τ x00 x01 x02 c)) (u02 .thd.1 c) (u12 .thd.1 c)] ]

axiom ℍᵖ_ext (S :♭| ℍspec) (x0 x1 : S .Γ) (x2 : Br (S .Γ) x0 x1)
  (u0 : ℍ S x0) (u1 : ℍ S x1) (u20 u21 : ℍ⁽ᵖ⁾ S x2 u0 u1)
  (u22 : eq_ℍᵖ S x0 x1 x2 x0 x1 x2 rfl. rfl. rfl. u0 u1 u20 u0 u1 u21 rfl.
           rfl.)
  : eq (ℍ⁽ᵖ⁾ S x2 u0 u1) u20 u21

{` The bridge type of an ℍ will be another ℍ.  Here we define the spec for that. `}

def Shat (S :♭| ℍspec) : ℍspec ≔ (
  Γ ≔ sig (
    x0 : S .Γ,
    x1 : S .Γ,
    x2 : Br (S .Γ) x0 x1,
    u0 : ℍ S x0,
    u1 : ℍ S x1 ),
  A ≔ y0 y1 y2 ↦
    Br (S .A) (y0 .x2) (y1 .x2) (sym (y2 .x2)) (y2 .u0 .fst) (y2 .u1 .fst),
  B ≔ y ↦
    (S .A (y .x0) (y .x1) (y .x2)
     × Br (S .B) (y .x2) (y .u0 .snd) (y .u1 .snd))
    × ((c : S .C (y .x0) (y .x1) (y .x2))
       → ℍ S (S .τ (y .x0) (y .x1) (y .x2) c)),
  C ≔ y0 y1 y2 ↦
    Σ (S .C (y0 .x0) (y1 .x0) (y2 .x0) × S .C (y0 .x1) (y1 .x1) (y2 .x1))
      (c ↦ Br (S .C) (y0 .x2) (y1 .x2) (sym (y2 .x2)) (c .fst) (c .snd)),
  τ ≔ y0 y1 y2 c ↦ (
    x0 ≔ S .τ (y0 .x0) (y1 .x0) (y2 .x0) (c .fst .fst),
    x1 ≔ S .τ (y0 .x1) (y1 .x1) (y2 .x1) (c .fst .snd),
    x2 ≔ rel (S .τ) (y0 .x2) (y1 .x2) (sym (y2 .x2)) (c .snd),
    u0 ≔ y2 .u0 .thd (c .fst .fst),
    u1 ≔ y2 .u1 .thd (c .fst .snd)))

{` Now the isomorphism between Br ℍ and the other ℍ.  `}

def id_ℍ_iso_to (S :♭| ℍspec) (x0 x1 : S .Γ) (x2 : Br (S .Γ) x0 x1)
  (u0 : ℍ S x0) (u1 : ℍ S x1)
  : ℍ (Shat S) (x0, x1, x2, u0, u1) → Br (ℍ S) x2 u0 u1
  ≔ v ↦ [
| .fst.p ⤇ v.2 .fst
| .fst.1 ⤇ v .snd .fst .fst
| .snd ⤇ v .snd .fst .snd
| .thd.p ⤇ c ⤇
    id_ℍ_iso_to S (S .τ x0.0 x0.1 x0.2 c.0) (S .τ x1.0 x1.1 x1.2 c.1)
      (rel (S .τ) x2.0 x2.1 (sym x2.2) c.2) (u0.2 .thd c.0) (u1.2 .thd c.1)
      (v.2 .thd ((c.0, c.1), c.2))
| .thd.1 ⤇ v .snd .snd]

def id_ℍ_iso_fro (S :♭| ℍspec) (x0 x1 : S .Γ) (x2 : Br (S .Γ) x0 x1)
  (u0 : ℍ S x0) (u1 : ℍ S x1)
  : Br (ℍ S) x2 u0 u1 → ℍ (Shat S) (x0, x1, x2, u0, u1)
  ≔ u2 ↦ [
| .fst.p ↦ u2 .fst.2
| .snd ↦ ((u2 .fst.1, u2 .snd), u2 .thd.1)
| .thd.p ↦ c ↦
    let t
      ≔ Shat S
          .τ (x0.0, x1.0, x2.0, u0.0, u1.0) (x0.1, x1.1, x2.1, u0.1, u1.1)
            (x0.2, x1.2, x2.2, u0.2, u1.2) c in
    id_ℍ_iso_fro S (t .x0) (t .x1) (t .x2) (t .u0) (t .u1)
      (u2 .thd.2 (c .snd))]

def id_ℍ_iso_fro_to (S :♭| ℍspec) (x0 x1 : S .Γ) (x2 : Br (S .Γ) x0 x1)
  (u0 : ℍ S x0) (u1 : ℍ S x1) (v : ℍ (Shat S) (x0, x1, x2, u0, u1))
  : eq.eq (ℍ (Shat S) (x0, x1, x2, u0, u1))
      (id_ℍ_iso_fro S x0 x1 x2 u0 u1 (id_ℍ_iso_to S x0 x1 x2 u0 u1 v)) v
  ≔ ℍ_ext (Shat S) (x0, x1, x2, u0, u1)
      (id_ℍ_iso_fro S x0 x1 x2 u0 u1 (id_ℍ_iso_to S x0 x1 x2 u0 u1 v)) v
      [ .fst.p ↦ rfl.
      | .snd ↦ rfl.
      | .thd.p ↦ c ↦
          id_ℍ_iso_fro_to S (S .τ x0.0 x0.1 x0.2 (c .fst .fst))
            (S .τ x1.0 x1.1 x1.2 (c .fst .snd))
            (rel (S .τ) x2.0 x2.1 (sym x2.2) (c .snd))
            (u0.2 .thd (c .fst .fst)) (u1.2 .thd (c .fst .snd))
            (v.2 .thd c)]

def id_ℍ_iso_to_fro (S :♭| ℍspec) (x0 x1 : S .Γ) (x2 : Br (S .Γ) x0 x1)
  (u0 : ℍ S x0) (u1 : ℍ S x1) (u2 : ℍ⁽ᵖ⁾ S x2 u0 u1)
  : eq.eq (ℍ⁽ᵖ⁾ S x2 u0 u1)
      (id_ℍ_iso_to S x0 x1 x2 u0 u1 (id_ℍ_iso_fro S x0 x1 x2 u0 u1 u2)) u2
  ≔ ℍᵖ_ext S x0 x1 x2 u0 u1
      (id_ℍ_iso_to S x0 x1 x2 u0 u1 (id_ℍ_iso_fro S x0 x1 x2 u0 u1 u2)) u2
      [ .fst.p ↦ rfl.
      | .fst1 ↦ rfl.
      | .snd ↦ rfl.
      | .thd.p ↦ c0 c1 c2 ↦
          id_ℍ_iso_to_fro S (S .τ x0.0 x0.1 x0.2 c0)
            (S .τ x1.0 x1.1 x1.2 c1) (rel (S .τ) x2.0 x2.1 (sym x2.2) c2)
            (u0.2 .thd c0) (u1.2 .thd c1) (sym u2.2 .thd.1 c2)
      | .thd1 ↦ c ↦ rfl.]

def id_ℍ_iso (S :♭| ℍspec) (x0 x1 : S .Γ) (x2 : Br (S .Γ) x0 x1)
  (u0 : ℍ S x0) (u1 : ℍ S x1)
  : ℍ (Shat S) (x0, x1, x2, u0, u1) ≅ Br (ℍ S) x2 u0 u1
  ≔ adjointify (ℍ (Shat S) (x0, x1, x2, u0, u1)) (ℍ⁽ᵖ⁾ S x2 u0 u1)
      (id_ℍ_iso_to S x0 x1 x2 u0 u1) (id_ℍ_iso_fro S x0 x1 x2 u0 u1)
      (id_ℍ_iso_fro_to S x0 x1 x2 u0 u1) (id_ℍ_iso_to_fro S x0 x1 x2 u0 u1)

{` Finally, we can prove that ℍs are fibrant.  Note that the parameter type Γ is also required to be fibrant (although it should suffice to have connections). `}

def 𝕗ℍspec (S : ℍspec) : Type ≔ sig (
  Γ : condFib (S .Γ),
  A : (x₀ x₁ : S .Γ) (x₂ : Br (S .Γ) x₀ x₁) → isFibrant (S .A x₀ x₁ x₂),
  B : (x : S .Γ) → isFibrant (S .B x),
  C : (x₀ x₁ : S .Γ) (x₂ : Br (S .Γ) x₀ x₁) → isFibrant (S .C x₀ x₁ x₂) )

def 𝕗ℍ (S :♭| ℍspec) (𝕗S :♭| 𝕗ℍspec S) (x : S .Γ) : isFibrant (ℍ S x) ≔ [
| .trr.p ↦ u0 ↦ [
  | .fst.p ↦ rel (𝕗S .A) x.20 x.21 (sym x.22) .trr (u0.2 .fst)
  | .snd ↦ rel (𝕗S .B) x.2 .trr (u0 .snd)
  | .thd.p ↦
      rel 𝕗Π (Br (S .C) x.20 x.21 (sym x.22))
          {c ↦ ℍ S (S .τ x.00 x.01 x.02 c)}
          {c ↦ ℍ S (S .τ x.10 x.11 x.12 c)}
          (c ⤇ Br ℍ S (rel (S .τ) x.20 x.21 (sym x.22) c.2))
          (rel (𝕗S .C) x.20 x.21 (sym x.22))
          {c ↦ 𝕗ℍ S 𝕗S (S .τ x.00 x.01 x.02 c)}
          {c ↦ 𝕗ℍ S 𝕗S (S .τ x.10 x.11 x.12 c)}
          (c ⤇ rel 𝕗ℍ S 𝕗S (rel (S .τ) x.20 x.21 (sym x.22) c.2))
        .trr (u0.2 .thd)]
| .trl.p ↦ u1 ↦ [
  | .fst.p ↦ rel (𝕗S .A) x.20 x.21 (sym x.22) .trl (u1.2 .fst)
  | .snd ↦ rel (𝕗S .B) x.2 .trl (u1 .snd)
  | .thd.p ↦
      rel 𝕗Π (Br (S .C) x.20 x.21 (sym x.22))
          {c ↦ ℍ S (S .τ x.00 x.01 x.02 c)}
          {c ↦ ℍ S (S .τ x.10 x.11 x.12 c)}
          (c ⤇ Br ℍ S (rel (S .τ) x.20 x.21 (sym x.22) c.2))
          (rel (𝕗S .C) x.20 x.21 (sym x.22))
          {c ↦ 𝕗ℍ S 𝕗S (S .τ x.00 x.01 x.02 c)}
          {c ↦ 𝕗ℍ S 𝕗S (S .τ x.10 x.11 x.12 c)}
          (c ⤇ rel 𝕗ℍ S 𝕗S (rel (S .τ) x.20 x.21 (sym x.22) c.2))
        .trl (u1.2 .thd)]
| .liftr.p ↦ u0 ↦ [
  | .fst.p ⤇ rel (𝕗S .A) x.20 x.21 (sym x.22) .liftr (u0.2 .fst)
  | .fst.1 ⤇
      rel (𝕗S .A) (rel x.0) x.2 (lconn (S .Γ) (𝕗S .Γ) x.0 x.1 x.2)
        .trr (rel u0 .fst)
  | .snd ⤇ rel (𝕗S .B) x.2 .liftr (u0 .snd)
  | .thd.p ↦
      rel 𝕗Π (Br (S .C) x.20 x.21 (sym x.22))
          {c ↦ ℍ S (S .τ x.00 x.01 x.02 c)}
          {c ↦ ℍ S (S .τ x.10 x.11 x.12 c)}
          (c ⤇ Br ℍ S (rel (S .τ) x.20 x.21 (sym x.22) c.2))
          (rel (𝕗S .C) x.20 x.21 (sym x.22))
          {c ↦ 𝕗ℍ S 𝕗S (S .τ x.00 x.01 x.02 c)}
          {c ↦ 𝕗ℍ S 𝕗S (S .τ x.10 x.11 x.12 c)}
          (c ⤇ rel 𝕗ℍ S 𝕗S (rel (S .τ) x.20 x.21 (sym x.22) c.2))
        .liftr (u0.2 .thd)
  | .thd.1 ↦ c ↦
      rel 𝕗ℍ S 𝕗S
          (rel (S .τ) (rel x.0) x.2 (lconn (S .Γ) (𝕗S .Γ) x.0 x.1 x.2)
             (rel (𝕗S .C) (rel x.0) x.2 (lconn (S .Γ) (𝕗S .Γ) x.0 x.1 x.2)
              .liftl c))
        .trr
          (rel u0
           .thd.1
             (rel (𝕗S .C) (rel x.0) x.2 (lconn (S .Γ) (𝕗S .Γ) x.0 x.1 x.2)
              .trl c))]
| .liftl.p ↦ u1 ↦ [
  | .fst.p ⤇ rel (𝕗S .A) x.20 x.21 (sym x.22) .liftl (u1.2 .fst)
  | .fst.1 ⤇
      rel (𝕗S .A) x.2 (rel x.1) (rconn (S .Γ) (𝕗S .Γ) x.0 x.1 x.2)
        .trl (rel u1 .fst)
  | .snd ⤇ rel (𝕗S .B) x.2 .liftl (u1 .snd)
  | .thd.p ↦
      rel 𝕗Π (Br (S .C) x.20 x.21 (sym x.22))
          {c ↦ ℍ S (S .τ x.00 x.01 x.02 c)}
          {c ↦ ℍ S (S .τ x.10 x.11 x.12 c)}
          (c ⤇ Br ℍ S (rel (S .τ) x.20 x.21 (sym x.22) c.2))
          (rel (𝕗S .C) x.20 x.21 (sym x.22))
          {c ↦ 𝕗ℍ S 𝕗S (S .τ x.00 x.01 x.02 c)}
          {c ↦ 𝕗ℍ S 𝕗S (S .τ x.10 x.11 x.12 c)}
          (c ⤇ rel 𝕗ℍ S 𝕗S (rel (S .τ) x.20 x.21 (sym x.22) c.2))
        .liftl (u1.2 .thd)
  | .thd.1 ↦ c ↦
      rel 𝕗ℍ S 𝕗S
          (rel (S .τ) x.2 (rel x.1) (rconn (S .Γ) (𝕗S .Γ) x.0 x.1 x.2)
             (rel (𝕗S .C) x.2 (rel x.1) (rconn (S .Γ) (𝕗S .Γ) x.0 x.1 x.2)
              .liftr c))
        .trl
          (rel u1
           .thd.1
             (rel (𝕗S .C) x.2 (rel x.1) (rconn (S .Γ) (𝕗S .Γ) x.0 x.1 x.2)
              .trr c))]
| .id.p ↦ u0 u1 ↦
    𝕗eqv (ℍ (Shat S) (x.0, x.1, x.2, u0, u1)) (ℍ⁽ᵖ⁾ S x.2 u0 u1)
      (id_ℍ_iso S x.0 x.1 x.2 u0 u1)
      (𝕗ℍ (Shat S) (𝕗Shat S 𝕗S) (x.0, x.1, x.2, u0, u1))]

{` Since Γhat involves ℍ, we have to prove mutually that Γhat is also conditionally fibrant.  I haven't thought about generator tricks to ensure this is productive. `}

and cΓhat (S :♭| ℍspec) (𝕗S :♭| 𝕗ℍspec S) : condFib (Shat S .Γ)
  ≔ condfib_eqv
      (Σ (Σ (S .Γ × S .Γ) (x ↦ Br (S .Γ) (x .0) (x .1)))
         (x ↦ (ℍ S (x .0 .0) × ℍ S (x .0 .1)))) (Shat S .Γ)
      (to ≔ x ↦ (x .0 .0 .0, x .0 .0 .1, x .0 .1, x .1 .0, x .1 .1),
       fro ≔ x ↦ (((x .0, x .1), x .2), (x .3, x .4)),
       fro_to ≔ _ ↦ rfl.,
       to_fro ≔ _ ↦ rfl.,
       to_fro_to ≔ _ ↦ rfl.)
      (cfΣ (Σ (S .Γ × S .Γ) (x ↦ rel S .Γ (x .fst) (x .snd)))
         (x ↦ ℍ S (x .fst .fst) × ℍ S (x .fst .snd))
         (cfTotBr (S .Γ) (𝕗S .Γ))
         (x ↦
          𝕗prod (ℍ S (x .fst .fst)) (ℍ S (x .fst .snd)) (𝕗ℍ S 𝕗S (x .0 .0))
            (𝕗ℍ S 𝕗S (x .0 .1))))

and 𝕗Shat (S :♭| ℍspec) (𝕗S :♭| 𝕗ℍspec S) : 𝕗ℍspec (Shat S) ≔ (
  Γ ≔ cΓhat S 𝕗S,
  A ≔ (y0 y1 y2 ↦
    rel (𝕗S .A) (y0 .2) (y1 .2) (sym (y2 .2))
      .id (y2 .u0 .fst) (y2 .u1 .fst)),
  B ≔ (y ↦
    𝕗prod
      (S .A (y .x0) (y .x1) (y .x2)
       × Br (S .B) (y .x2) (y .u0 .snd) (y .u1 .snd))
      ((c : S .C (y .x0) (y .x1) (y .x2))
       → ℍ S (S .τ (y .x0) (y .x1) (y .x2) c))
      (𝕗prod (S .A (y .x0) (y .x1) (y .x2))
         (Br (S .B) (y .x2) (y .u0 .snd) (y .u1 .snd))
         ((𝕗S .A) (y .0) (y .1) (y .2))
         (rel (𝕗S .B) (y .2) .id (y .u0 .snd) (y .u1 .snd)))
      (𝕗Π (S .C (y .x0) (y .x1) (y .x2))
         (c ↦ ℍ S (S .τ (y .x0) (y .x1) (y .x2) c))
         ((𝕗S .C) (y .x0) (y .x1) (y .x2))
         (c ↦ 𝕗ℍ S 𝕗S (S .τ (y .x0) (y .x1) (y .x2) c)))),
  C ≔ (y0 y1 y2 ↦
    𝕗Σ (S .C (y0 .x0) (y1 .x0) (y2 .x0) × S .C (y0 .x1) (y1 .x1) (y2 .x1))
      (c ↦ Br (S .C) (y0 .x2) (y1 .x2) (sym (y2 .x2)) (c .fst) (c .snd))
      (𝕗prod (S .C (y0 .x0) (y1 .x0) (y2 .x0))
         (S .C (y0 .x1) (y1 .x1) (y2 .x1))
         ((𝕗S .C) (y0 .x0) (y1 .x0) (y2 .x0))
         ((𝕗S .C) (y0 .x1) (y1 .x1) (y2 .x1)))
      (c ↦
       rel (𝕗S .C) (y0 .x2) (y1 .x2) (sym (y2 .x2)) .id (c .fst) (c .snd))))
