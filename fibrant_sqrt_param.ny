{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-discrete-coreflector") -*- `}

import "bookhott"
import "isfibrant"
import "hott_bookhott"
import "fibrant_types"

{` A generic non-recursive higher coinductive type with one higher field and one lower field.  Note that the "spec" consisting of Γ, A, B are modal, so they will not get degenerated in bridges. `}

def √ (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x : Γ)
  : Type
  ≔ codata [
| s .fst.p : A x.0 x.1 x.2
| s .snd : B x ]

{` We need to assert an eq-extensionality principle for this.  The input to such a principle is also a higher coinductive type. `}

def eq_√ (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x0 x1 : Γ) (x2 : eq Γ x0 x1) (u0 : √ Γ A B x0)
  (u1 : √ Γ A B x1)
  : Type
  ≔ codata [
| e .fst.p
  : match x2.2 [ rfl. ⤇ eq (A x0.0 x0.1 x0.2) (u0.2 .fst) (u1.2 .fst) ]
| e .snd : match x2 [ rfl. ↦ eq (B x0) (u0 .snd) (u1 .snd) ] ]

axiom √_ext (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x : Γ) (u0 u1 : √ Γ A B x)
  (u2 : eq_√ Γ A B x x rfl. u0 u1)
  : eqd Γ (√ Γ A B) x x rfl. u0 u1

{` We also need a similar eq-extensionality principle for its bridges. `}

def eq_√ᵖ (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x00 x01 : Γ) (x02 : Br Γ x00 x01) (x10 x11 : Γ)
  (x12 : Br Γ x10 x11) (x20 : eq Γ x00 x10) (x21 : eq Γ x01 x11)
  (x22 : eq2d Γ Γ (x0 x1 ↦ Br Γ x0 x1) x00 x10 x20 x01 x11 x21 x02 x12)
  (u00 : √ Γ A B x00) (u01 : √ Γ A B x01) (u02 : Br (√ Γ A B) x02 u00 u01)
  (u10 : √ Γ A B x10) (u11 : √ Γ A B x11) (u12 : Br (√ Γ A B) x12 u10 u11)
  (u20 : eqd Γ (√ Γ A B) x00 x10 x20 u00 u10)
  (u21 : eqd Γ (√ Γ A B) x01 x11 x21 u01 u11)
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
        eq (Br B x02 (u00 .snd) (u01 .snd)) (u02 .snd) (u12 .snd)] ]

axiom √ᵖ_ext (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x0 x1 : Γ) (x2 : Br Γ x0 x1) (u0 : √ Γ A B x0)
  (u1 : √ Γ A B x1) (u20 u21 : √⁽ᵖ⁾ Γ A B x2 u0 u1)
  (u22 : eq_√ᵖ Γ A B x0 x1 x2 x0 x1 x2 rfl. rfl. rfl. u0 u1 u20 u0 u1 u21
           rfl. rfl.)
  : eq (√⁽ᵖ⁾ Γ A B x2 u0 u1) u20 u21

{` The bridge type of a √ will be another √.  Here we define the spec Γ, A, and B for that. `}

def Γhat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type)
  : Type
  ≔ sig (
  x0 : Γ,
  x1 : Γ,
  x2 : Br Γ x0 x1,
  u0 : √ Γ A B x0,
  u1 : √ Γ A B x1 )

def Ahat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (y0 y1 : Γhat Γ A B) (y2 : Br (Γhat Γ A B) y0 y1)
  : Type
  ≔ Br A (y0 .x2) (y1 .x2) (sym (y2 .x2)) (y2 .u0 .fst) (y2 .u1 .fst)

def Bhat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (y : Γhat Γ A B)
  : Type
  ≔ A (y .x0) (y .x1) (y .x2) × Br B (y .x2) (y .u0 .snd) (y .u1 .snd)

{` Now the isomorphism between Br √ and the other √.  `}

def id_√_iso_to (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x0 x1 : Γ) (x2 : Br Γ x0 x1) (u0 : √ Γ A B x0)
  (u1 : √ Γ A B x1)
  : √ (Γhat Γ A B) (Ahat Γ A B) (Bhat Γ A B) (x0, x1, x2, u0, u1)
    → Br (√ Γ A B) x2 u0 u1
  ≔ v ↦ [ .fst.p ⤇ v.2 .fst | .fst.1 ⤇ v .snd .fst | .snd ⤇ v .snd .snd ]

def id_√_iso_fro (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x0 x1 : Γ) (x2 : Br Γ x0 x1) (u0 : √ Γ A B x0)
  (u1 : √ Γ A B x1)
  : Br (√ Γ A B) x2 u0 u1
    → √ (Γhat Γ A B) (Ahat Γ A B) (Bhat Γ A B) (x0, x1, x2, u0, u1)
  ≔ u2 ↦ [ .fst.p ↦ u2 .fst.2 | .snd ↦ (u2 .fst.1, u2 .snd) ]

def id_√_iso (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x0 x1 : Γ) (x2 : Br Γ x0 x1) (u0 : √ Γ A B x0)
  (u1 : √ Γ A B x1)
  : √ (Γhat Γ A B) (Ahat Γ A B) (Bhat Γ A B) (x0, x1, x2, u0, u1)
    ≅ Br (√ Γ A B) x2 u0 u1
  ≔ adjointify
      (√ (Γhat Γ A B) (Ahat Γ A B) (Bhat Γ A B) (x0, x1, x2, u0, u1))
      (√⁽ᵖ⁾ Γ A B x2 u0 u1) (id_√_iso_to Γ A B x0 x1 x2 u0 u1)
      (id_√_iso_fro Γ A B x0 x1 x2 u0 u1)
      (v ↦
       √_ext (Γhat Γ A B) (Ahat Γ A B) (Bhat Γ A B) (x0, x1, x2, u0, u1)
         (id_√_iso_fro Γ A B x0 x1 x2 u0 u1
            (id_√_iso_to Γ A B x0 x1 x2 u0 u1 v)) v
         [ .fst.p ↦ rfl. | .snd ↦ rfl. ])
      (u2 ↦
       √ᵖ_ext Γ A B x0 x1 x2 u0 u1
         (id_√_iso_to Γ A B x0 x1 x2 u0 u1
            (id_√_iso_fro Γ A B x0 x1 x2 u0 u1 u2)) u2
         [ .fst.p ↦ rfl. | .fst1 ↦ rfl. | .snd ↦ rfl. ])

{` Finally, we can prove that √s are fibrant.  Note that the parameter type Γ is also required to be fibrant (although it would suffice to have connections). `}
      
def 𝕗√ (Γ :♭| Type) (𝕗Γ :♭| isFibrant Γ)
  (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (𝕗A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → isFibrant (A x₀ x₁ x₂))
  (B :♭| Γ → Type) (𝕗B :♭| (x : Γ) → isFibrant (B x)) (x : Γ)
  : isFibrant (√ Γ A B x)
  ≔ [
| .trr.p ↦ u0 ↦ [
  | .fst.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .trr (u0.2 .fst)
  | .snd ↦ rel 𝕗B x.2 .trr (u0 .snd)]
| .trl.p ↦ u1 ↦ [
  | .fst.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .trl (u1.2 .fst)
  | .snd ↦ rel 𝕗B x.2 .trl (u1 .snd)]
| .liftr.p ↦ u0 ↦ [
  | .fst.p ⤇ rel 𝕗A x.20 x.21 (sym x.22) .liftr (u0.2 .fst)
  | .fst.1 ⤇
      rel 𝕗A (rel x.0) x.2 (coconn (Γ, 𝕗Γ) x.0 x.1 x.2) .trr (rel u0 .fst)
  | .snd ⤇ rel 𝕗B x.2 .liftr (u0 .snd)]
| .liftl.p ↦ u1 ↦ [
  | .fst.p ⤇ rel 𝕗A x.20 x.21 (sym x.22) .liftl (u1.2 .fst)
  | .fst.1 ⤇
      rel 𝕗A x.2 (rel x.1) (conn (Γ, 𝕗Γ) x.0 x.1 x.2) .trl (rel u1 .fst)
  | .snd ⤇ rel 𝕗B x.2 .liftl (u1 .snd)]
| .id.p ↦ u0 u1 ↦
    𝕗eqv (√ (Γhat Γ A B) (Ahat Γ A B) (Bhat Γ A B) (x.0, x.1, x.2, u0, u1))
      (√⁽ᵖ⁾ Γ A B x.2 u0 u1) (id_√_iso Γ A B x.0 x.1 x.2 u0 u1)
      (𝕗√ (Γhat Γ A B) (𝕗Γhat Γ 𝕗Γ A 𝕗A B 𝕗B)
         (y0 y1 y2 ↦
          Br A (y0 .x2) (y1 .x2) (sym (y2 .x2)) (y2 .u0 .fst) (y2 .u1 .fst))
         (y0 y1 y2 ↦
          rel 𝕗A (y0 .2) (y1 .2) (sym (y2 .2))
          .id (y2 .u0 .fst) (y2 .u1 .fst))
         (y ↦
          A (y .x0) (y .x1) (y .x2)
          × Br B (y .x2) (y .u0 .snd) (y .u1 .snd))
         (y ↦
          𝕗prod (A (y .x0) (y .x1) (y .x2))
            (Br B (y .x2) (y .u0 .snd) (y .u1 .snd))
            (𝕗A (y .0) (y .1) (y .2))
            (rel 𝕗B (y .2) .id (y .u0 .snd) (y .u1 .snd)))
         (x.0, x.1, x.2, u0, u1))]

{` Since Γhat involves the √, we have to prove mutually that this is also fibrant.  I haven't thought about generator tricks to ensure this is productive. `}

and 𝕗Γhat (Γ :♭| Type) (𝕗Γ :♭| isFibrant Γ)
  (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (𝕗A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → isFibrant (A x₀ x₁ x₂))
  (B :♭| Γ → Type) (𝕗B :♭| (x : Γ) → isFibrant (B x))
  : isFibrant (Γhat Γ A B)
  ≔ 𝕗eqv
      (Σ (Γ × Γ)
         (x ↦ Br Γ (x .0) (x .1) × (√ Γ A B (x .0) × √ Γ A B (x .1))))
      (Γhat Γ A B)
      (to ≔ x ↦ (x .0 .0, x .0 .1, x .1 .0, x .1 .1 .0, x .1 .1 .1),
       fro ≔ x ↦ ((x .0, x .1), (x .2, (x .3, x .4))),
       fro_to ≔ _ ↦ rfl.,
       to_fro ≔ _ ↦ rfl.,
       to_fro_to ≔ _ ↦ rfl.)
      (𝕗Σ (Γ × Γ)
         (x ↦
          Br Γ (x .fst) (x .snd) × (√ Γ A B (x .fst) × √ Γ A B (x .snd)))
         (𝕗prod Γ Γ 𝕗Γ 𝕗Γ)
         (x ↦
          𝕗prod (Br Γ (x .fst) (x .snd))
            (√ Γ A B (x .fst) × √ Γ A B (x .snd))
            (rel 𝕗Γ .id (x .0) (x .1))
            (𝕗prod (√ Γ A B (x .fst)) (√ Γ A B (x .snd))
               (𝕗√ Γ 𝕗Γ A 𝕗A B 𝕗B (x .0)) (𝕗√ Γ 𝕗Γ A 𝕗A B 𝕗B (x .1)))))
