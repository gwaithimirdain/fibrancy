{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"

{` Missing stuff `}

def eq.trl (A : Type) (P : A → Type) (a0 a1 : A) (a2 : eq A a0 a1)
  (p : P a1)
  : P a0
  ≔ match a2 [ rfl. ↦ p ]

def eqv_idmap (A : Type) : A ≅ A ≔ (
  to ≔ x ↦ x,
  fro ≔ x ↦ x,
  fro_to ≔ x ↦ rfl.,
  to_fro ≔ x ↦ rfl.,
  to_fro_to ≔ x ↦ rfl.)

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

def sym_eqv′ (A00 A01 : Type) (A02 : Br Type A00 A01) (A10 A11 : Type)
  (A12 : Br Type A10 A11) (A20 : Br Type A00 A10) (A21 : Br Type A01 A11)
  (A22 : Br (Br Type) A02 A12 A20 A21) (a00 : A00) (a01 : A01)
  (a02 : A02 a00 a01) (a10 : A10) (a11 : A11) (a12 : A12 a10 a11)
  (a20 : A20 a00 a10) (a21 : A21 a01 a11)
  : sym A22 a20 a21 a02 a12 ≅ A22 a02 a12 a20 a21
  ≔ (
  to ≔ a22 ↦ sym a22,
  fro ≔ a22 ↦ sym a22,
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def Σ_eqv_functor (A0 : Type) (A1 : Type) (ea : A0 ≅ A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (eb : (a0 : A0) → B0 a0 ≅ B1 (ea .to a0))
  : Σ A0 B0 ≅ Σ A1 B1
  ≔ (
  to ≔ u ↦ (ea .to (u .0), eb (u .0) .to (u .1)),
  fro ≔ v ↦ (
    ea .fro (v .0),
    eb (ea .fro (v .0))
      .fro
        (eq.trl A1 B1 (ea .to (ea .fro (v .0))) (v .0) (ea .to_fro (v .0))
           (v .1))),
  fro_to ≔ ¿ʔ,
  to_fro ≔ ¿ʔ,
  to_fro_to ≔ ¿ʔ)

def Σ_eqv_functor_overid (A : Type) (B0 B1 : A → Type)
  (e : (a : A) → B0 a ≅ B1 a)
  : Σ A B0 ≅ Σ A B1
  ≔ (
  to ≔ u ↦ (u .0, e (u .0) .to (u .1)),
  fro ≔ v ↦ (v .0, e (v .0) .fro (v .1)),
  fro_to ≔ u ↦ ¿eq_Σʔ,
  to_fro ≔ ¿ʔ,
  to_fro_to ≔ ¿ʔ)

def Id_eq_rfl (A0 A1 : Type) (A2 : Br Type A0 A1) (a00 a01 : A0)
  (a02 : eq A0 a00 a01) (a10 a11 : A1) (a12 : eq A1 a10 a11)
  (a20 : A2 a00 a10) (a21 : A2 a01 a11)
  : eq (A2 a00 a10) a20
      (eq.trl2 A0 A1 (a0 a1 ↦ A2 a0 a1) a00 a01 a02 a10 a11 a12 a21)
    ≅ Br eq A2 a20 a21 a02 a12
  ≔ (
  to ≔ a22 ↦ match a02, a12, a22 [ rfl., rfl., rfl. ↦ rfl. ],
  fro ≔ [ rfl. ⤇ rfl. ],
  fro_to ≔ a22 ↦ match a02, a12, a22 [ rfl., rfl., rfl. ↦ rfl. ],
  to_fro ≔ [ rfl. ⤇ rfl. ],
  to_fro_to ≔ a22 ↦ match a02, a12, a22 [ rfl., rfl., rfl. ↦ rfl. ])

def eqv_trr2_trl2 (A00 A01 : Type) (A02 : A00 → A01 → Type)
  (A10 A11 : Type) (A12 : A10 → A11 → Type) (A20 : A00 → A10 → Type)
  (A21 : A01 → A11 → Type)
  (A22 : (a00 : A00) (a01 : A01) (a02 : A02 a00 a01) (a10 : A10)
         (a11 : A11) (a12 : A12 a10 a11) (a20 : A20 a00 a10)
         (a21 : A21 a01 a11)
         → Type) (a000 a001 : A00) (a002 : eq A00 a000 a001)
  (a010 a011 : A01) (a012 : eq A01 a010 a011) (a100 a101 : A10)
  (a102 : eq A10 a100 a101) (a110 a111 : A11) (a112 : eq A11 a110 a111)
  (a02 : A02 a000 a010) (a12 : A12 a100 a110) (a20 : A20 a001 a101)
  (a21 : A21 a011 a111)
  : A22 a000 a010 a02 a100 a110 a12
      (eq.trl2 A00 A10 A20 a000 a001 a002 a100 a101 a102 a20)
      (eq.trl2 A01 A11 A21 a010 a011 a012 a110 a111 a112 a21)
    ≅ A22 a001 a011 (eq.trr2 A00 A01 A02 a000 a001 a002 a010 a011 a012 a02)
        a101 a111 (eq.trr2 A10 A11 A12 a100 a101 a102 a110 a111 a112 a12)
        a20 a21
  ≔ match a002, a012, a102, a112 [
| rfl., rfl., rfl., rfl. ↦
    eqv_idmap (A22 a000 a010 a02 a100 a110 a12 a20 a21)]

{` Bisimulations for non-fibrant types.  These are defined just like for fibrant types, but in the non-fibrant case they are not just a notion of HoTT equivalence but carry more nontrivial information about how the higher parametricity translations correspond. `}

def isBisim (A B : Type) (R : A → B → Type) : Type ≔ codata [
| x .trr : A → B
| x .liftr : (a : A) → R a (x .trr a)
| x .trl : B → A
| x .liftl : (b : B) → R (x .trl b) b
| x .id.p
  : (a0 : A.0) (b0 : B.0) (r0 : R.0 a0 b0) (a1 : A.1) (b1 : B.1)
    (r1 : R.1 a1 b1)
    → isBisim (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ (R.2 a2 b2 r0 r1)) ]

{` Bisimulations transfer across isomorphisms. `}

def isBisim_eqv (A0 B0 : Type) (R0 : A0 → B0 → Type)
  (Rb0 : isBisim A0 B0 R0) (A1 B1 : Type) (R1 : A1 → B1 → Type)
  (ea : A0 ≅ A1) (eb : B0 ≅ B1)
  (er : (a0 : A0) (b0 : B0) → R0 a0 b0 ≅ R1 (ea .to a0) (eb .to b0))
  : isBisim A1 B1 R1
  ≔ [
| .trr ↦ a1 ↦ eb .to (Rb0 .trr (ea .fro a1))
| .liftr ↦ a1 ↦
    eq.trr A1 (a ↦ R1 a (eb .to (Rb0 .trr (ea .fro a1))))
      (ea .to (ea .fro a1)) a1 (ea .to_fro a1)
      (er (ea .fro a1) (Rb0 .trr (ea .fro a1))
       .to (Rb0 .liftr (ea .fro a1)))
| .trl ↦ b1 ↦ ea .to (Rb0 .trl (eb .fro b1))
| .liftl ↦ b1 ↦
    eq.trr B1 (b ↦ R1 (ea .to (Rb0 .trl (eb .fro b1))) b)
      (eb .to (eb .fro b1)) b1 (eb .to_fro b1)
      (er (Rb0 .trl (eb .fro b1)) (eb .fro b1)
       .to (Rb0 .liftl (eb .fro b1)))
| .id.p ↦ a10 b10 r10 a11 b11 r11 ↦
    isBisim_eqv (A0.2 (ea.0 .fro a10) (ea.1 .fro a11))
      (B0.2 (eb.0 .fro b10) (eb.1 .fro b11))
      (a2 b2 ↦
       R0.2 a2 b2
         (er.0 (ea.0 .fro a10) (eb.0 .fro b10)
          .fro
            (eq.trl2 A1.0 B1.0 R1.0 (ea.0 .to (ea.0 .fro a10)) a10
               (ea.0 .to_fro a10) (eb.0 .to (eb.0 .fro b10)) b10
               (eb.0 .to_fro b10) r10))
         (er.1 (ea.1 .fro a11) (eb.1 .fro b11)
          .fro
            (eq.trl2 A1.1 B1.1 R1.1 (ea.1 .to (ea.1 .fro a11)) a11
               (ea.1 .to_fro a11) (eb.1 .to (eb.1 .fro b11)) b11
               (eb.1 .to_fro b11) r11)))
      (Rb0.2 .id (ea.0 .fro a10) (eb.0 .fro b10)
         (er.0 (ea.0 .fro a10) (eb.0 .fro b10)
          .fro
            (eq.trl2 A1.0 B1.0 R1.0 (ea.0 .to (ea.0 .fro a10)) a10
               (ea.0 .to_fro a10) (eb.0 .to (eb.0 .fro b10)) b10
               (eb.0 .to_fro b10) r10)) (ea.1 .fro a11) (eb.1 .fro b11)
         (er.1 (ea.1 .fro a11) (eb.1 .fro b11)
          .fro
            (eq.trl2 A1.1 B1.1 R1.1 (ea.1 .to (ea.1 .fro a11)) a11
               (ea.1 .to_fro a11) (eb.1 .to (eb.1 .fro b11)) b11
               (eb.1 .to_fro b11) r11))) (A1.2 a10 a11) (B1.2 b10 b11)
      (a2 b2 ↦ R1.2 a2 b2 r10 r11)
      (Id_eqv A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 ea.0 ea.1 ea.2 a10 a11)
      (Id_eqv B0.0 B0.1 B0.2 B1.0 B1.1 B1.2 eb.0 eb.1 eb.2 b10 b11)
      (a02 b02 ↦
       comp_eqv
         (R0.2 a02 b02
            (er.0 (ea.0 .fro a10) (eb.0 .fro b10)
             .fro
               (eq.trl2 A1.0 B1.0 R1.0 (ea.0 .to (ea.0 .fro a10)) a10
                  (ea.0 .to_fro a10) (eb.0 .to (eb.0 .fro b10)) b10
                  (eb.0 .to_fro b10) r10))
            (er.1 (ea.1 .fro a11) (eb.1 .fro b11)
             .fro
               (eq.trl2 A1.1 B1.1 R1.1 (ea.1 .to (ea.1 .fro a11)) a11
                  (ea.1 .to_fro a11) (eb.1 .to (eb.1 .fro b11)) b11
                  (eb.1 .to_fro b11) r11)))
         (R1.2 (ea.2 .to a02) (eb.2 .to b02)
            (eq.trl2 A1.0 B1.0 R1.0 (ea.0 .to (ea.0 .fro a10)) a10
               (ea.0 .to_fro a10) (eb.0 .to (eb.0 .fro b10)) b10
               (eb.0 .to_fro b10) r10)
            (eq.trl2 A1.1 B1.1 R1.1 (ea.1 .to (ea.1 .fro a11)) a11
               (ea.1 .to_fro a11) (eb.1 .to (eb.1 .fro b11)) b11
               (eb.1 .to_fro b11) r11))
         (R1.2
            (eq.trr2 A1.0 A1.1 (b0 b1 ↦ A1.2 b0 b1)
               (ea.0 .to (ea.0 .fro a10)) a10 (ea.0 .to_fro a10)
               (ea.1 .to (ea.1 .fro a11)) a11 (ea.1 .to_fro a11)
               (ea.2 .to a02))
            (eq.trr2 B1.0 B1.1 (b0 b1 ↦ B1.2 b0 b1)
               (eb.0 .to (eb.0 .fro b10)) b10 (eb.0 .to_fro b10)
               (eb.1 .to (eb.1 .fro b11)) b11 (eb.1 .to_fro b11)
               (eb.2 .to b02)) r10 r11)
         (Id_eqv (R0.0 (ea.0 .fro a10) (eb.0 .fro b10))
            (R0.1 (ea.1 .fro a11) (eb.1 .fro b11))
            (R0.2 {ea.0 .fro a10} {ea.1 .fro a11} a02 {eb.0 .fro b10}
               {eb.1 .fro b11} b02)
            (R1.0 (ea.0 .to (ea.0 .fro a10)) (eb.0 .to (eb.0 .fro b10)))
            (R1.1 (ea.1 .to (ea.1 .fro a11)) (eb.1 .to (eb.1 .fro b11)))
            (R1.2 {ea.0 .to (ea.0 .fro a10)} {ea.1 .to (ea.1 .fro a11)}
               (ea.2 .to {ea.0 .fro a10} {ea.1 .fro a11} a02)
               {eb.0 .to (eb.0 .fro b10)} {eb.1 .to (eb.1 .fro b11)}
               (eb.2 .to {eb.0 .fro b10} {eb.1 .fro b11} b02))
            (er.0 (ea.0 .fro a10) (eb.0 .fro b10))
            (er.1 (ea.1 .fro a11) (eb.1 .fro b11)) (er.2 a02 b02)
            (eq.trl2 A1.0 B1.0 R1.0 (ea.0 .to (ea.0 .fro a10)) a10
               (ea.0 .to_fro a10) (eb.0 .to (eb.0 .fro b10)) b10
               (eb.0 .to_fro b10) r10)
            (eq.trl2 A1.1 B1.1 R1.1 (ea.1 .to (ea.1 .fro a11)) a11
               (ea.1 .to_fro a11) (eb.1 .to (eb.1 .fro b11)) b11
               (eb.1 .to_fro b11) r11))
         (eqv_trr2_trl2 A1.0 A1.1 (x y ↦ A1.2 x y) B1.0 B1.1
            (x y ↦ B1.2 x y) R1.0 R1.1
            (x y z w u v p q ↦ R1.2 {x} {y} z {w} {u} v p q)
            (ea.0 .to (ea.0 .fro a10)) a10 (ea.0 .to_fro a10)
            (ea.1 .to (ea.1 .fro a11)) a11 (ea.1 .to_fro a11)
            (eb.0 .to (eb.0 .fro b10)) b10 (eb.0 .to_fro b10)
            (eb.1 .to (eb.1 .fro b11)) b11 (eb.1 .to_fro b11)
            (ea.2 .to a02) (eb.2 .to b02) r10 r11))]

def isBisim_eqv_overid (A B : Type) (R0 : A → B → Type)
  (Rb0 : isBisim A B R0) (R1 : A → B → Type)
  (er : (a : A) (b : B) → R0 a b ≅ R1 a b)
  : isBisim A B R1
  ≔ isBisim_eqv A B R0 Rb0 A B R1 (eqv_idmap A) (eqv_idmap B) er

{` Isomorphism is a bisimulation.  This may seem like a simpler result, but it actually requires the previous one! `}

def isBisim_≅ (A B : Type) (e : A ≅ B)
  : isBisim A B (a b ↦ eq A (e .fro b) a)
  ≔ [
| .trr ↦ e .to
| .liftr ↦ a ↦ e .fro_to a
| .trl ↦ e .fro
| .liftl ↦ b ↦ rfl.
| .id.p ↦ a0 b0 r0 a1 b1 r1 ↦ match r0, r1 [
  | rfl., rfl. ↦
      isBisim_eqv_overid (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
        (a b ↦ eq.eq (A.2 (e.0 .fro b0) (e.1 .fro b1)) (e.2 .fro b) a)
        (isBisim_≅ (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
           (Id_eqv A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1))
        (a2 b2 ↦ eq.eq⁽ᵖ⁾ A.2 (e.2 .fro b2) a2 rfl. rfl.)
        (a2 b2 ↦
         Id_eq_rfl A.0 A.1 A.2 (e.0 .fro b0) (e.0 .fro b0) rfl.
           (e.1 .fro b1) (e.1 .fro b1) rfl. (e.2 .fro b2) a2)]]

{` Like with very-surjectivity, fibrancy transfers across bisimulations. `}

def isfibrant_isbisim (A B : Type) (R : A → B → Type) (Rb : isBisim A B R)
  (fB : isFibrant B)
  : isFibrant A
  ≔ [
| .trr.p ↦ a0 ↦ Rb.1 .trl (fB.2 .trr (Rb.0 .trr a0))
| .liftr.p ↦ a0 ↦
    Rb.2
      .id a0 (Rb.0 .trr a0) (Rb.0 .liftr a0)
        (Rb.1 .trl (fB.2 .trr (Rb.0 .trr a0))) (fB.2 .trr (Rb.0 .trr a0))
        (Rb.1 .liftl (fB.2 .trr (Rb.0 .trr a0)))
      .trl (fB.2 .liftr (Rb.0 .trr a0))
| .trl.p ↦ a1 ↦ Rb.0 .trl (fB.2 .trl (Rb.1 .trr a1))
| .liftl.p ↦ a1 ↦
    Rb.2
      .id (Rb.0 .trl (fB.2 .trl (Rb.1 .trr a1))) (fB.2 .trl (Rb.1 .trr a1))
        (Rb.0 .liftl (fB.2 .trl (Rb.1 .trr a1))) a1 (Rb.1 .trr a1)
        (Rb.1 .liftr a1)
      .trl (fB.2 .liftl (Rb.1 .trr a1))
| .id.p ↦ a0 a1 ↦
    isfibrant_isbisim (A.2 a0 a1) (B.2 (Rb.0 .trr a0) (Rb.1 .trr a1))
      ((a2 b2 ↦ R.2 a2 b2 (Rb.0 .liftr a0) (Rb.1 .liftr a1)))
      (Rb.2 .id a0 (Rb.0 .trr a0) (Rb.0 .liftr a0) a1 (Rb.1 .trr a1)
         (Rb.1 .liftr a1)) (fB .id (Rb.0 .trr a0) (Rb.1 .trr a1))]

{` But bisimulations have several advantages over very-surjective maps.  One is that they pass to Σ-types without a separate notion of "dependent bisimulation": a dependent bisimulation is just a family of bisimulations indexed by corresponding points below. `}

def isBisim_Σ (A B : Type) (R : A → B → Type) (Rb : isBisim A B R)
  (Aᵈ : A → Type) (Bᵈ : B → Type)
  (Rᵈ : (a : A) (b : B) (r : R a b) → Aᵈ a → Bᵈ b → Type)
  (Rbᵈ : (a : A) (b : B) (r : R a b) → isBisim (Aᵈ a) (Bᵈ b) (Rᵈ a b r))
  : isBisim (Σ A Aᵈ) (Σ B Bᵈ)
      (a b ↦ Σ (R (a .0) (b .0)) (r ↦ Rᵈ (a .0) (b .0) r (a .1) (b .1)))
  ≔ [
| .trr ↦ a ↦ (
    Rb .trr (a .0),
    Rbᵈ (a .0) (Rb .trr (a .0)) (Rb .liftr (a .0)) .trr (a .1))
| .liftr ↦ a ↦ (
    Rb .liftr (a .0),
    Rbᵈ (a .0) (Rb .trr (a .0)) (Rb .liftr (a .0)) .liftr (a .1))
| .trl ↦ b ↦ (
    Rb .trl (b .0),
    Rbᵈ (Rb .trl (b .0)) (b .0) (Rb .liftl (b .0)) .trl (b .1))
| .liftl ↦ b ↦ (
    Rb .liftl (b .0),
    Rbᵈ (Rb .trl (b .0)) (b .0) (Rb .liftl (b .0)) .liftl (b .1))
| .id.p ↦ a0 b0 r0 a1 b1 r1 ↦
    isBisim_eqv
      (Σ (A.2 (a0 .fst) (a1 .fst)) (a2 ↦ Aᵈ.2 a2 (a0 .snd) (a1 .snd)))
      (Σ (B.2 (b0 .fst) (b1 .fst)) (b2 ↦ Bᵈ.2 b2 (b0 .snd) (b1 .snd)))
      (a b ↦
       Σ (R.2 (a .fst) (b .fst) (r0 .fst) (r1 .fst))
         (r ↦
          Rᵈ.2 (a .fst) (b .fst) r (a .snd) (b .snd) (r0 .snd) (r1 .snd)))
      (isBisim_Σ (A.2 (a0 .0) (a1 .0)) (B.2 (b0 .0) (b1 .0))
         (a2 b2 ↦ R.2 a2 b2 (r0 .0) (r1 .0))
         (Rb.2 .id (a0 .0) (b0 .0) (r0 .0) (a1 .0) (b1 .0) (r1 .0))
         (a2 ↦ Aᵈ.2 a2 (a0 .1) (a1 .1)) (b2 ↦ Bᵈ.2 b2 (b0 .1) (b1 .1))
         (a2 b2 r2 a2ᵈ b2ᵈ ↦ Rᵈ.2 a2 b2 r2 a2ᵈ b2ᵈ (r0 .1) (r1 .1))
         (a2 b2 r2 ↦
          Rbᵈ.2 a2 b2 r2
          .id (a0 .1) (b0 .1) (r0 .1) (a1 .1) (b1 .1) (r1 .1)))
      (Σ⁽ᵖ⁾ A.2 Aᵈ.2 a0 a1) (Σ⁽ᵖ⁾ B.2 Bᵈ.2 b0 b1)
      (a2 b2 ↦
       Σ⁽ᵖ⁾ (R.2 (a2 .fst) (b2 .fst))
         {r ↦ Rᵈ.0 (a0 .fst) (b0 .fst) r (a0 .snd) (b0 .snd)}
         {r ↦ Rᵈ.1 (a1 .fst) (b1 .fst) r (a1 .snd) (b1 .snd)}
         (r ⤇ Rᵈ.2 (a2 .fst) (b2 .fst) r.2 (a2 .snd) (b2 .snd)) r0 r1)
      (id_Σ_iso A.0 A.1 A.2 Aᵈ.0 Aᵈ.1 Aᵈ.2 (a0 .0) (a1 .0) (a0 .1) (a1 .1))
      (id_Σ_iso B.0 B.1 B.2 Bᵈ.0 Bᵈ.1 Bᵈ.2 (b0 .0) (b1 .0) (b0 .1) (b1 .1))
      (a2 b2 ↦
       id_Σ_iso (R.0 (a0 .fst) (b0 .fst)) (R.1 (a1 .fst) (b1 .fst))
         (R.2 {a0 .fst} {a1 .fst} (a2 .fst) {b0 .fst} {b1 .fst} (b2 .fst))
         (r ↦ Rᵈ.0 (a0 .fst) (b0 .fst) r (a0 .snd) (b0 .snd))
         (r ↦ Rᵈ.1 (a1 .fst) (b1 .fst) r (a1 .snd) (b1 .snd))
         (r ⤇
          Rᵈ.2 {a0 .fst} {a1 .fst} (a2 .fst) {b0 .fst} {b1 .fst} (b2 .fst)
            {r.0} {r.1} r.2 {a0 .snd} {a1 .snd} (a2 .snd) {b0 .snd}
            {b1 .snd} (b2 .snd)) (r0 .0) (r1 .0) (r0 .1) (r1 .1))]

{` Bisimulations also pass to types of functions with constant domain, without need of modification. `}

def fun_isBisim (C : Type) (A B : C → Type)
  (R : (c : C) → A c → B c → Type)
  (Rb : (c : C) → isBisim (A c) (B c) (R c))
  : isBisim ((c : C) → A c) ((c : C) → B c)
      (f g ↦ (c : C) → R c (f c) (g c))
  ≔ [
| .trr ↦ f c ↦ Rb c .trr (f c)
| .liftr ↦ f c ↦ Rb c .liftr (f c)
| .trl ↦ g c ↦ Rb c .trl (g c)
| .liftl ↦ g c ↦ Rb c .liftl (g c)
| .id.p ↦ f0 g0 r0 f1 g1 r1 ↦
    isBisim_eqv
      ((c : BR C.0 C.1 C.2)
       → A.2 {c .a0} {c .a1} (c .a2) (f0 (c .a0)) (f1 (c .a1)))
      ((c : BR C.0 C.1 C.2)
       → B.2 {c .a0} {c .a1} (c .a2) (g0 (c .a0)) (g1 (c .a1)))
      (f g ↦
       (c : BR C.0 C.1 C.2)
       → R.2 {c .a0} {c .a1} (c .a2) {f0 (c .a0)} {f1 (c .a1)} (f c)
           {g0 (c .a0)} {g1 (c .a1)} (g c) (r0 (c .a0)) (r1 (c .a1)))
      (fun_isBisim (BR C.0 C.1 C.2)
         (c ↦ A.2 (c .2) (f0 (c .0)) (f1 (c .1)))
         (c ↦ B.2 (c .2) (g0 (c .0)) (g1 (c .1)))
         (c a2 b2 ↦ R.2 (c .2) a2 b2 (r0 (c .0)) (r1 (c .1)))
         (c ↦
          Rb.2 (c .2)
          .id (f0 (c .0)) (g0 (c .0)) (r0 (c .0)) (f1 (c .1)) (g1 (c .1))
            (r1 (c .1))))
      ({c₀ : C.0} {c₁ : C.1} (c₂ : C.2 c₀ c₁)
       →⁽ᵖ⁾ A.2 {c₀} {c₁} c₂ (f0 c₀) (f1 c₁))
      ({c₀ : C.0} {c₁ : C.1} (c₂ : C.2 c₀ c₁)
       →⁽ᵖ⁾ B.2 {c₀} {c₁} c₂ (g0 c₀) (g1 c₁))
      (a2 b2 ↦
       {c₀ : C.0} {c₁ : C.1} (c₂ : C.2 c₀ c₁)
       →⁽ᵖ⁾ R.2 {c₀} {c₁} c₂ {f0 c₀} {f1 c₁} (a2 {c₀} {c₁} c₂) {g0 c₀}
              {g1 c₁} (b2 {c₀} {c₁} c₂) (r0 c₀) (r1 c₁))
      (id_Π_iso′ C.0 C.1 C.2 A.0 A.1 A.2 f0 f1)
      (id_Π_iso′ C.0 C.1 C.2 B.0 B.1 B.2 g0 g1)
      (f2 g2 ↦
       id_Π_iso′ C.0 C.1 C.2 (c0 ↦ R.0 c0 (f0 c0) (g0 c0))
         (c1 ↦ R.1 c1 (f1 c1) (g1 c1))
         (c ⤇ R.2 c.2 (f2 (c.0, c.1, c.2)) (g2 (c.0, c.1, c.2))) r0 r1)]

{` And they compose, without needing fibrancy `}

def isBisim_comp (A B C : Type) (R : A → B → Type) (Rb : isBisim A B R)
  (S : B → C → Type) (Sb : isBisim B C S)
  : isBisim A C (a c ↦ Σ B (b ↦ R a b × S b c))
  ≔ [
| .trr ↦ a ↦ Sb .trr (Rb .trr a)
| .liftr ↦ a ↦ (Rb .trr a, (Rb .liftr a, Sb .liftr (Rb .trr a)))
| .trl ↦ c ↦ Rb .trl (Sb .trl c)
| .liftl ↦ c ↦ (Sb .trl c, (Rb .liftl (Sb .trl c), Sb .liftl c))
| .id.p ↦ a0 c0 brs0 a1 c1 brs1 ↦
    isBisim_eqv_overid (A.2 a0 a1) (C.2 c0 c1)
      (a c ↦
       Σ (B.2 (brs0 .fst) (brs1 .fst))
         (b ↦
          R.2 {a0} {a1} a {brs0 .fst} {brs1 .fst} b (brs0 .snd .fst)
            (brs1 .snd .fst)
          × S.2 {brs0 .fst} {brs1 .fst} b {c0} {c1} c (brs0 .snd .snd)
              (brs1 .snd .snd)))
      (isBisim_comp (A.2 a0 a1) (B.2 (brs0 .0) (brs1 .0)) (C.2 c0 c1)
         (a2 b2 ↦ R.2 a2 b2 (brs0 .1 .0) (brs1 .1 .0))
         (Rb.2 .id a0 (brs0 .0) (brs0 .1 .0) a1 (brs1 .0) (brs1 .1 .0))
         (b2 c2 ↦ S.2 b2 c2 (brs0 .1 .1) (brs1 .1 .1))
         (Sb.2 .id (brs0 .0) c0 (brs0 .1 .1) (brs1 .0) c1 (brs1 .1 .1)))
      (a2 b2 ↦
       Σ⁽ᵖ⁾ {B.0} {B.1} B.2 {b ↦ R.0 a0 b × S.0 b c0}
         {b ↦ R.1 a1 b × S.1 b c1}
         (b ⤇
          prod⁽ᵖ⁾ {R.0 a0 b.0} {R.1 a1 b.1}
            (R.2 {a0} {a1} a2 {b.0} {b.1} b.2) {S.0 b.0 c0} {S.1 b.1 c1}
            (S.2 {b.0} {b.1} b.2 {c0} {c1} b2)) brs0 brs1)
      (a2 c2 ↦
       comp_eqv
         (Σ (B.2 (brs0 .fst) (brs1 .fst))
            (b ↦
             R.2 {a0} {a1} a2 {brs0 .fst} {brs1 .fst} b (brs0 .snd .fst)
               (brs1 .snd .fst)
             × S.2 {brs0 .fst} {brs1 .fst} b {c0} {c1} c2 (brs0 .snd .snd)
                 (brs1 .snd .snd)))
         (Σ (B.2 (brs0 .fst) (brs1 .fst))
            (a2′ ↦
             prod⁽ᵖ⁾ {R.0 a0 (brs0 .fst)} {R.1 a1 (brs1 .fst)}
               (R.2 {a0} {a1} a2 {brs0 .fst} {brs1 .fst} a2′)
               {S.0 (brs0 .fst) c0} {S.1 (brs1 .fst) c1}
               (S.2 {brs0 .fst} {brs1 .fst} a2′ {c0} {c1} c2) (brs0 .snd)
               (brs1 .snd)))
         (Σ⁽ᵖ⁾ {B.0} {B.1} B.2 {b ↦ R.0 a0 b × S.0 b c0}
            {b ↦ R.1 a1 b × S.1 b c1}
            (b ⤇
             prod⁽ᵖ⁾ {R.0 a0 b.0} {R.1 a1 b.1}
               (R.2 {a0} {a1} a2 {b.0} {b.1} b.2) {S.0 b.0 c0} {S.1 b.1 c1}
               (S.2 {b.0} {b.1} b.2 {c0} {c1} c2)) brs0 brs1)
         (Σ_eqv_functor_overid (B.2 (brs0 .fst) (brs1 .fst))
            (b ↦
             R.2 {a0} {a1} a2 {brs0 .fst} {brs1 .fst} b (brs0 .snd .fst)
               (brs1 .snd .fst)
             × S.2 {brs0 .fst} {brs1 .fst} b {c0} {c1} c2 (brs0 .snd .snd)
                 (brs1 .snd .snd))
            (a2′ ↦
             prod⁽ᵖ⁾ {R.0 a0 (brs0 .fst)} {R.1 a1 (brs1 .fst)}
               (R.2 {a0} {a1} a2 {brs0 .fst} {brs1 .fst} a2′)
               {S.0 (brs0 .fst) c0} {S.1 (brs1 .fst) c1}
               (S.2 {brs0 .fst} {brs1 .fst} a2′ {c0} {c1} c2) (brs0 .snd)
               (brs1 .snd))
            (b2 ↦
             id_prod_iso (R.0 a0 (brs0 .fst)) (R.1 a1 (brs1 .fst))
               (R.2 {a0} {a1} a2 {brs0 .fst} {brs1 .fst} b2)
               (S.0 (brs0 .fst) c0) (S.1 (brs1 .fst) c1)
               (S.2 {brs0 .fst} {brs1 .fst} b2 {c0} {c1} c2) (brs0 .1 .0)
               (brs1 .1 .0) (brs0 .1 .1) (brs1 .1 .1)))
         (id_Σ_iso B.0 B.1 B.2 (b ↦ R.0 a0 b × S.0 b c0)
            (b ↦ R.1 a1 b × S.1 b c1)
            (b ⤇
             prod⁽ᵖ⁾ {R.0 a0 b.0} {R.1 a1 b.1}
               (R.2 {a0} {a1} a2 {b.0} {b.1} b.2) {S.0 b.0 c0} {S.1 b.1 c1}
               (S.2 {b.0} {b.1} b.2 {c0} {c1} c2)) (brs0 .0) (brs1 .0)
            (brs0 .1) (brs1 .1)))]

{` Beware, though: the identity correspondence of a type is not a bisimulation unless the type is fibrant.  This makes it impossible to define isBisim_gel in the following style. `}

{`
def isBisim_gel (A B : Type)
  : isBisim (Br Type A B) (A → B → Type)
      (C R ↦
       Σ ((a : A) (b : B) → C a b → R a b → Type)
         (E ↦ (a : A) (b : B) → isBisim (C a b) (R a b) (E a b)))
  ≔ [
| .trr ↦ C a b ↦ C a b
| .liftr ↦ C ↦ (a b c c' ↦ Br (C a b) c c', a b ↦ ¿ʔ)
| .trl ↦ R ↦ Gel A B R
| .liftl ↦ R ↦ (a b c r ↦ Br (R a b) (c .ungel) r, a b ↦ ¿ʔ)
| .id.p ↦ ¿C R ʔ]
 `}

{` However, we can do it up to isomorphism, and it again seems plausible that we could build this version into Narya. `}

def isBisim_gel (A0 A1 : Type)
  : isBisim (Br Type A0 A1) (A0 → A1 → Type)
      (A2 R ↦ (a0 : A0) (a1 : A1) → A2 a0 a1 ≅ R a0 a1)
  ≔ [
| .trr ↦ A2 a0 a1 ↦ A2 a0 a1
| .liftr ↦ A2 a0 a1 ↦ eqv_idmap (A2 a0 a1)
| .trl ↦ R ↦ Gel A0 A1 R
| .liftl ↦ R a0 a1 ↦ Gel_iso′ A0 A1 R a0 a1
| .id.p ↦ A20 R0 e0 A21 R1 e1 ↦ [
  | .trr ↦
    {` Unfortunately we have to Gel here even in the left-to-right direction, to get a bridge between correspondences by transferring across isomorphisms. `}
    A22 ↦ a0 a1 ⤇
      Gel (R0 a0.0 a1.0) (R1 a0.1 a1.1)
        (r0 r1 ↦
         A22 a0.2 a1.2 (e0 a0.0 a1.0 .fro r0) (e1 a0.1 a1.1 .fro r1))
  {` This should be Gel_eqv composed with pullback along two isomorphisms. `}
  | .liftr ↦ A22 ↦ a0 a1 ⤇ ¿ʔ
  | .trl ↦ A22 ↦
      Gel2 A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 A20 A21
        (a00 a01 a02 a10 a11 a12 a20 a21 ↦
         A22 a02 a12 (e0 a00 a10 .to a20) (e1 a01 a11 .to a21))
  | .liftl ↦ A22 ↦ a0 a1 ⤇ ¿ʔ
  | .id.p ↦ A220 R20 e20 A221 R21 e21 ↦ ¿ʔ]]

{` Now the central issue with extending a correspondence of this sort to the fibrant universe is that we have different coinductive types on the two sides, [Br isFibrant] on the left, which is a property of 1-dimensional types, and some analogous thing on the right that is a property of correspondences.  However, bisimulations are exactly the right tool for comparing coinductive definitions.  We exhibit this for non-higher coinductive types by showing that two such are bisimilar as soon as their field types are. `}

{` Basics of 𝕄-types `}

def 𝕄_spec : Type ≔ sig (
  R : Type,
  A : R → Type,
  B : (r : R) → A r → Type,
  k : (r : R) (a : A r) → B r a → R )

def 𝕄 (s : 𝕄_spec) (r : s .R) : Type ≔ codata [
| x .recv : s .A r
| x .send : (b : s .B r (x .recv)) → 𝕄 s (s .k r (x .recv) b) ]

{` Encode-decode for 𝕄-types based on eq.eq.  This is required in order to show that the bridges of an 𝕄-type is isomorphic to another 𝕄-type.  `}

section 𝕄_encode_decode ≔

  def 𝕄_code_spec (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) : 𝕄_spec ≔ (
    R ≔ sig (
      r0 : s0 .R,
      r1 : s1 .R,
      r2 : s2 .R r0 r1,
      x0 : 𝕄 s0 r0,
      x1 : 𝕄 s1 r1 ),
    A ≔ r ↦ s2 .A (r .r2) (r .x0 .recv) (r .x1 .recv),
    B ≔ r a2 ↦
      Σ (s0 .B (r .r0) (r .x0 .recv))
        (b0 ↦ Σ (s1 .B (r .r1) (r .x1 .recv)) (b1 ↦ s2 .B (r .r2) a2 b0 b1)),
    k ≔ r a2 b ↦ (
      r0 ≔ s0 .k (r .r0) (r .x0 .recv) (b .0),
      r1 ≔ s1 .k (r .r1) (r .x1 .recv) (b .1 .0),
      r2 ≔ s2 .k (r .r2) a2 (b .1 .1),
      x0 ≔ r .x0 .send (b .0),
      x1 ≔ r .x1 .send (b .1 .0)))

  def 𝕄_encode (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
    (x2 : rel 𝕄 s2 r2 x0 x1)
    : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
    ≔ [
  | .recv ↦ x2 .recv
  | .send ↦ b ↦
      𝕄_encode s0 s1 s2 (s0 .k r0 (x0 .recv) (b .0))
        (s1 .k r1 (x1 .recv) (b .1 .0)) (s2 .k r2 (x2 .recv) (b .1 .1))
        (x0 .send (b .0)) (x1 .send (b .1 .0)) (x2 .send (b .1 .1))]

  def 𝕄_decode (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
    (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
    : rel 𝕄 s2 r2 x0 x1
    ≔ [
  | .recv ↦ y2 .recv
  | .send ↦ b ⤇
      𝕄_decode s0 s1 s2 (s0 .k r0 (x0 .recv) b.0) (s1 .k r1 (x1 .recv) b.1)
        (s2 .k r2 (y2 .recv) b.2) (x0 .send b.0) (x1 .send b.1)
        (y2 .send (b.0, (b.1, b.2)))]

{` We need "coinductive extensionality" for eq.  The version we need says that the eq-types of 𝕄, dependent over an equality of indices, are again an 𝕄-type, similar to the codes for Br but without changing the spec.  In the application we only use this over a fixed index, but we can't *define* it in general without passing to a non-rfl equality of indices. `}

  def 𝕄_bisim (s : 𝕄_spec) (r0 : s .R) (r1 : s .R) (r2 : eq (s .R) r0 r1)
    (x0 : 𝕄 s r0) (x1 : 𝕄 s r1)
    : Type
    ≔ codata [
  | x2 .recv : eqd (s .R) (r ↦ s .A r) r0 r1 r2 (x0 .recv) (x1 .recv)
  | x2 .send
    : (b0 : s .B r0 (x0 .recv)) (b1 : s .B r1 (x1 .recv))
      (b2
      : eqdd (s .R) (r ↦ s .A r) (r a ↦ s .B r a) r0 r1 r2 (x0 .recv)
          (x1 .recv) (x2 .recv) b0 b1)
      → 𝕄_bisim s (s .k r0 (x0 .recv) b0) (s .k r1 (x1 .recv) b1)
          (ap3d (s .R) (r ↦ s .A r) (r a ↦ s .B r a) (s .R) (s .k) r0 r1 r2
             (x0 .recv) (x1 .recv) (x2 .recv) b0 b1 b2) (x0 .send b0)
          (x1 .send b1) ]

  axiom 𝕄_ext (s : 𝕄_spec) (r : s .R) (x0 x1 : 𝕄 s r)
    (y2 : 𝕄_bisim s r r rfl. x0 x1)
    : eq (𝕄 s r) x0 x1

  def 𝕄_encode_decode_bisim (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1)
    (r0 : s0 .R) (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0)
    (x1 : 𝕄 s1 r1) (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
    : 𝕄_bisim (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
        (r0, r1, r2, x0, x1) rfl.
        (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1
           (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2)) y2
    ≔ [
  | .recv ↦ rfl.
  | .send ↦ b0 b1 b2 ↦ match b2 [
    | rfl. ↦
        𝕄_encode_decode_bisim s0 s1 s2 (s0 .k r0 (x0 .recv) (b0 .0))
          (s1 .k r1 (x1 .recv) (b0 .1 .0)) (s2 .k r2 (y2 .recv) (b0 .1 .1))
          (x0 .send (b0 .0)) (x1 .send (b0 .1 .0)) (y2 .send b0)]]

  def 𝕄_encode_decode (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
    (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
    : eq (𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
        (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1
           (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2)) y2
    ≔ 𝕄_ext (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
        (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1
           (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2)) y2
        (𝕄_encode_decode_bisim s0 s1 s2 r0 r1 r2 x0 x1 y2)

{` For the other direction we need a version of this for rel 𝕄. `}

  def refl_𝕄_bisim (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r20 : s2 .R r0 r1) (r21 : s2 .R r0 r1)
    (r22 : eq (s2 .R r0 r1) r20 r21) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
    (x20 : rel 𝕄 s2 r20 x0 x1) (x21 : rel 𝕄 s2 r21 x0 x1)
    : Type
    ≔ codata [
  | y2 .recv
    : eqd (s2 .R r0 r1) (r2 ↦ s2 .A r2 (x0 .recv) (x1 .recv)) r20 r21 r22
        (x20 .recv) (x21 .recv)
  | y2 .send
    : (b0 : s0 .B r0 (x0 .recv)) (b1 : s1 .B r1 (x1 .recv))
      (b20 : s2 .B r20 (x20 .recv) b0 b1)
      (b21 : s2 .B r21 (x21 .recv) b0 b1)
      (b22
      : eqdd (s2 .R r0 r1) (r2 ↦ s2 .A r2 (x0 .recv) (x1 .recv))
          (r2 a2 ↦ s2 .B r2 a2 b0 b1) r20 r21 r22 (x20 .recv) (x21 .recv)
          (y2 .recv) b20 b21)
      → refl_𝕄_bisim s0 s1 s2 (s0 .k r0 (x0 .recv) b0)
          (s1 .k r1 (x1 .recv) b1) (s2 .k r20 (x20 .recv) b20)
          (s2 .k r21 (x21 .recv) b21)
          (ap3d (s2 .R r0 r1) (r2 ↦ s2 .A r2 (x0 .recv) (x1 .recv))
             (r2 a2 ↦ s2 .B r2 a2 b0 b1)
             (s2 .R (s0 .k r0 (x0 .recv) b0) (s1 .k r1 (x1 .recv) b1))
             (r2 a2 b2 ↦ s2 .k r2 a2 b2) r20 r21 r22 (x20 .recv)
             (x21 .recv) (y2 .recv) b20 b21 b22) (x0 .send b0)
          (x1 .send b1) (x20 .send b20) (x21 .send b21) ]

  axiom refl_𝕄_ext (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
    (x20 : rel 𝕄 s2 r2 x0 x1) (x21 : rel 𝕄 s2 r2 x0 x1)
    (y22 : refl_𝕄_bisim s0 s1 s2 r0 r1 r2 r2 rfl. x0 x1 x20 x21)
    : eq (rel 𝕄 s2 r2 x0 x1) x20 x21

  def 𝕄_decode_encode_bisim (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1)
    (r0 : s0 .R) (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0)
    (x1 : 𝕄 s1 r1) (x2 : rel 𝕄 s2 r2 x0 x1)
    : refl_𝕄_bisim s0 s1 s2 r0 r1 r2 r2 rfl. x0 x1
        (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1
           (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2)) x2
    ≔ [
  | .recv ↦ rfl.
  | .send ↦ b0 b1 b20 b21 b22 ↦ match b22 [
    | rfl. ↦
        𝕄_decode_encode_bisim s0 s1 s2 (s0 .k r0 (x0 .recv) b0)
          (s1 .k r1 (x1 .recv) b1) (s2 .k r2 (x2 .recv) b20) (x0 .send b0)
          (x1 .send b1) (x2 .send b20)]]

  def 𝕄_decode_encode (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
    (x2 : rel 𝕄 s2 r2 x0 x1)
    : eq (rel 𝕄 s2 r2 x0 x1)
        (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1
           (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2)) x2
    ≔ refl_𝕄_ext s0 s1 s2 r0 r1 r2 x0 x1
        (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1
           (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2)) x2
        (𝕄_decode_encode_bisim s0 s1 s2 r0 r1 r2 x0 x1 x2)

  def Id_𝕄_iso (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
    : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1) ≅ rel 𝕄 s2 r2 x0 x1
    ≔ adjointify (𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
        (rel 𝕄 s2 r2 x0 x1) (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1)
        (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1)
        (𝕄_encode_decode s0 s1 s2 r0 r1 r2 x0 x1)
        (𝕄_decode_encode s0 s1 s2 r0 r1 r2 x0 x1)

end

import 𝕄_encode_decode | only Id_𝕄_iso

{` We define "a bisimulation between the input data" of two 𝕄-types.  Importantly, note that the two can have different parameter spaces -- all we require is they be related by a correspondence. `}

def 𝕄_spec_corr (s0 s1 : 𝕄_spec) : Type ≔ sig (
  s2 .R : s0 .R → s1 .R → Type,
  s2 .A : (r0 : s0 .R) (r1 : s1 .R) (r2 : s2 .R r0 r1) → s0 .A r0 →
          s1 .A r1
          → Type,
  s2 .B : (r0 : s0 .R) (r1 : s1 .R) (r2 : s2 .R r0 r1) (a0 : s0 .A r0)
          (a1 : s1 .A r1) (a2 : s2 .A r0 r1 r2 a0 a1) → s0 .B r0 a0 →
          s1 .B r1 a1
          → Type,
  s2 .k : (r0 : s0 .R) (r1 : s1 .R) (r2 : s2 .R r0 r1) (a0 : s0 .A r0)
          (a1 : s1 .A r1) (a2 : s2 .A r0 r1 r2 a0 a1) (b0 : s0 .B r0 a0)
          (b1 : s1 .B r1 a1) (b2 : s2 .B r0 r1 r2 a0 a1 a2 b0 b1)
          → s2 .R (s0 .k r0 a0 b0) (s1 .k r1 a1 b1) )

def corr_𝕄_spec (s0 s1 : 𝕄_spec) (s2 : 𝕄_spec_corr s0 s1) : 𝕄_spec ≔ (
  R ≔ sig (
    r0 : s0 .R,
    r1 : s1 .R,
    r2 : s2 .R r0 r1,
    x0 : 𝕄 s0 r0,
    x1 : 𝕄 s1 r1 ),
  A ≔ r ↦ s2 .A (r .r0) (r .r1) (r .r2) (r .x0 .recv) (r .x1 .recv),
  B ≔ r a2 ↦
    Σ (s0 .B (r .r0) (r .x0 .recv) × s1 .B (r .r1) (r .x1 .recv))
      (b ↦
       s2 .B (r .r0) (r .r1) (r .r2) (r .x0 .recv) (r .x1 .recv) a2 (b .0)
         (b .1)),
  k ≔ r a2 b ↦ (
    r0 ≔ s0 .k (r .r0) (r .x0 .recv) (b .0 .0),
    r1 ≔ s1 .k (r .r1) (r .x1 .recv) (b .0 .1),
    r2 ≔
      s2 .k (r .r0) (r .r1) (r .r2) (r .x0 .recv) (r .x1 .recv) a2
        (b .0 .0) (b .0 .1) (b .1),
    x0 ≔ r .x0 .send (b .0 .0),
    x1 ≔ r .x1 .send (b .0 .1)))

{` Such a correspondence is a bisimulation f it is pointwise so. `}

def 𝕄_spec_isBisim (s0 s1 : 𝕄_spec) (s2 : 𝕄_spec_corr s0 s1) : Type ≔ sig (
` Not used?
` b2 .R : isBisim (s0 .R) (s1 .R) (s2 .R),
  b2 .A : (r0 : s0 .R) (r1 : s1 .R) (r2 : s2 .R r0 r1)
          → isBisim (s0 .A r0) (s1 .A r1) (s2 .A r0 r1 r2),
  b2 .B : (r0 : s0 .R) (r1 : s1 .R) (r2 : s2 .R r0 r1) (a0 : s0 .A r0)
          (a1 : s1 .A r1) (a2 : s2 .A r0 r1 r2 a0 a1)
          → isBisim (s0 .B r0 a0) (s1 .B r1 a1) (s2 .B r0 r1 r2 a0 a1 a2) )

def 𝕄_bisim_trr (s0 s1 : 𝕄_spec) (s2 : 𝕄_spec_corr s0 s1)
  (sb : 𝕄_spec_isBisim s0 s1 s2) (r0 : s0 .R) (r1 : s1 .R)
  (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0)
  : 𝕄 s1 r1
  ≔ [
| .recv ↦ sb .A r0 r1 r2 .trr (x0 .recv)
| .send ↦ b1 ↦
    𝕄_bisim_trr s0 s1 s2 sb
      (s0 .k r0 (x0 .recv)
         (sb
          .B r0 r1 r2 (x0 .recv) (sb .A r0 r1 r2 .trr (x0 .recv))
            (sb .A r0 r1 r2 .liftr (x0 .recv))
          .trl b1)) (s1 .k r1 (sb .A r0 r1 r2 .trr (x0 .recv)) b1)
      (s2 .k r0 r1 r2 (x0 .recv) (sb .A r0 r1 r2 .trr (x0 .recv))
         (sb .A r0 r1 r2 .liftr (x0 .recv))
         (sb
          .B r0 r1 r2 (x0 .recv) (sb .A r0 r1 r2 .trr (x0 .recv))
            (sb .A r0 r1 r2 .liftr (x0 .recv))
          .trl b1) b1
         (sb
          .B r0 r1 r2 (x0 .recv) (sb .A r0 r1 r2 .trr (x0 .recv))
            (sb .A r0 r1 r2 .liftr (x0 .recv))
          .liftl b1))
      (x0 .send
         (sb
          .B r0 r1 r2 (x0 .recv) (sb .A r0 r1 r2 .trr (x0 .recv))
            (sb .A r0 r1 r2 .liftr (x0 .recv))
          .trl b1))]

{` In progress `}
def 𝕄_bisim_liftr (s0 s1 : 𝕄_spec) (s2 : 𝕄_spec_corr s0 s1)
  (sb : 𝕄_spec_isBisim s0 s1 s2) (r0 : s0 .R) (r1 : s1 .R)
  (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0)
  : 𝕄 (corr_𝕄_spec s0 s1 s2)
      (r0, r1, r2, x0, 𝕄_bisim_trr s0 s1 s2 sb r0 r1 r2 x0)
  ≔ [
| .recv ↦ sb .A r0 r1 r2 .liftr (x0 .recv)
| .send ↦ b1 ↦
    ¿
    𝕄_bisim_liftr s0 s1 s2 sb
      (s0 .k r0 (x0 .recv)
         (sb
          .B r0 r1 r2 (x0 .recv) (sb .A r0 r1 r2 .trr (x0 .recv))
            (sb .A r0 r1 r2 .liftr (x0 .recv))
          .trl b1)) (s1 .k r1 (sb .A r0 r1 r2 .trr (x0 .recv)) b1)
      (s2 .k r0 r1 r2 (x0 .recv) (sb .A r0 r1 r2 .trr (x0 .recv))
         (sb .A r0 r1 r2 .liftr (x0 .recv))
         (sb
          .B r0 r1 r2 (x0 .recv) (sb .A r0 r1 r2 .trr (x0 .recv))
            (sb .A r0 r1 r2 .liftr (x0 .recv))
          .trl b1) b1
         (sb
          .B r0 r1 r2 (x0 .recv) (sb .A r0 r1 r2 .trr (x0 .recv))
            (sb .A r0 r1 r2 .liftr (x0 .recv))
          .liftl b1))
      (x0 .send
         (sb
          .B r0 r1 r2 (x0 .recv) (sb .A r0 r1 r2 .trr (x0 .recv))
            (sb .A r0 r1 r2 .liftr (x0 .recv))
          .trl b1))ʔ]

def 𝕄_bisim (s0 s1 : 𝕄_spec) (s2 : 𝕄_spec_corr s0 s1)
  (sb : 𝕄_spec_isBisim s0 s1 s2) (r0 : s0 .R) (r1 : s1 .R)
  (r2 : s2 .R r0 r1)
  : isBisim (𝕄 s0 r0) (𝕄 s1 r1)
      (x0 x1 ↦ 𝕄 (corr_𝕄_spec s0 s1 s2) (r0, r1, r2, x0, x1))
  ≔ [
| .trr ↦ 𝕄_bisim_trr s0 s1 s2 sb r0 r1 r2
| .liftr ↦ 𝕄_bisim_liftr s0 s1 s2 sb r0 r1 r2
| .trl ↦ ¿ʔ
| .liftl ↦ ¿ʔ
| .id.p ↦ x00 x10 x20 x01 x11 x21 ↦
    ¿𝕄_bisim (𝕄_code_spec s0.0 s0.1 s0.2) (𝕄_code_spec s1.0 s1.1 s1.2) ? ? ? ? ?ʔ]

{` Comparing isFibrant over an isomorphism, by a coinductively defined custom bisimulation.  In each field we could choose to hypothesize an A or a B.  I chose B for .id because that's what we already have in Id_eqv. `}

def isFibrant_iso (A B : Type) (e : A ≅ B) (Af : isFibrant A)
  (Bf : isFibrant B)
  : Type
  ≔ codata [
| x .trr.p
  : (a0 : A.0) → eq B.1 (e.1 .to (Af.2 .trr a0)) (Bf.2 .trr (e.0 .to a0))
| x .liftr.p
  : (a0 : A.0)
    → eqd B.1 (b1 ↦ B.2 (e.0 .to a0) b1) (e.1 .to (Af.2 .trr a0))
        (Bf.2 .trr (e.0 .to a0)) (x.2 .trr a0) (e.2 .to (Af.2 .liftr a0))
        (Bf.2 .liftr (e.0 .to a0))
| x .trl.p
  : (a1 : A.1) → eq B.0 (e.0 .to (Af.2 .trl a1)) (Bf.2 .trl (e.1 .to a1))
| x .liftl.p
  : (a1 : A.1)
    → eqd B.0 (b0 ↦ B.2 b0 (e.1 .to a1)) (e.0 .to (Af.2 .trl a1))
        (Bf.2 .trl (e.1 .to a1)) (x.2 .trl a1) (e.2 .to (Af.2 .liftl a1))
        (Bf.2 .liftl (e.1 .to a1))
| x .id.p
  : (b0 : B.0) (b1 : B.1)
    → isFibrant_iso (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
        (Id_eqv A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1)
        (Af.2 .id (e.0 .fro b0) (e.1 .fro b1)) (Bf.2 .id b0 b1) ]

{` A fibrancy witness and its transfer are related. `}

def isFibrant_iso_eqv (A B : Type) (e : A ≅ B) (Af : isFibrant A)
  : isFibrant_iso A B e Af (𝕗eqv A B e Af)
  ≔ [
| .trr.p ↦ a0 ↦
    eq.ap A.0 B.1 (a ↦ e.1 .to (Af.2 .trr a)) a0 (e.0 .fro (e.0 .to a0))
      (eq.inv A.0 (e.0 .fro (e.0 .to a0)) a0 (e.0 .fro_to a0))
| .liftr.p ↦ a0 ↦ ¿ ʔ ` Path algebra
| .trl.p ↦ ¿ʔ
| .liftl.p ↦ ¿ʔ
| .id.p ↦ b0 b1 ↦
    isFibrant_iso_eqv (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
      (Id_eqv A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1)
      (Af.2 .id (e.0 .fro b0) (e.1 .fro b1))]

{` Our custom bisimulation is a bisimulation `}

def isBisim_isFibrant_iso (A B : Type) (e : A ≅ B)
  : isBisim (isFibrant A) (isFibrant B) (isFibrant_iso A B e)
  ≔ [
| .trr ↦ 𝕗eqv A B e
| .liftr ↦ Af ↦ isFibrant_iso_eqv A B e Af
| .trl ↦ ¿ʔ
| .liftl ↦ ¿ʔ
` Here we need to recurse into more general parametrized HCTs, in particular [Br isFibrant].
| .id.p ↦ Af0 Bf0 ef0 Af1 Bf1 ef1 ↦ ¿ʔ]

{` Impossible alternative approach: just use [Br isFibrant] over the bridge induced by an isomorphism. `}

{`
def Br_𝕗eqv (A B : Type) (e : A ≅ B) (Af : isFibrant A)
  : Br isFibrant (Gel A B (a b ↦ eq B (e .to a) b)) Af (𝕗eqv A B e Af)
  ≔ [
| .trr.p ⤇ c0 ⤇ (
    eq.ap A.0 B.1 (a ↦ e.1 .to (Af.2 .trr a)) c0.0 (e.0 .fro c0.1)
      (eq.cat A.0 c0.0 (e.0 .fro (e.0 .to c0.0)) (e.0 .fro c0.1)
         (eq.inv A.0 (e.0 .fro (e.0 .to c0.0)) c0.0 (e.0 .fro_to c0.0))
         (eq.ap B.0 A.0 (e.0 .fro) (e.0 .to c0.0) c0.1 (c0.2 .ungel))),)
| .trr.1 ⤇ e .to
| .trl.p ⤇ c1 ⤇ (¿c1.2 .ungelʔ,)
| .trl.1 ⤇ e .fro
| .liftr.p ⤇ {a0} {b0} r0 ↦ sym (¿ʔ,)
| .liftr.1 ⤇ a ↦ (rfl.,)
| .liftl.p ⤇ ¿ʔ
| .liftl.1 ⤇ b ↦ (e .to_fro b,)
| .id.p ⤇ {a0} {b0} r0 {a1} {b1} r1 ↦ ¿ʔ
` Whoops!  This is not true!
| .id.1 ⤇ 𝕗Gel A B (x y ↦ eq B (e .to x) y) (a b ↦ ¿ʔ)]
`}

{` A version of [Br isFibrant] transferred to correspondences.  Note that it has a corecursive field referring to *itself*, not to [Br isFibrant] of a [Gel].  `}

def Br_isFibrant_corr (A0 A1 : Fib) (R : A0 .t → A1 .t → Type) : Type
  ≔ codata [
| x .trr.p
  : (a00 : A0.0 .t) (a10 : A1.0 .t) (a20 : R.0 a00 a10)
    → R.1 (A0.2 .f .trr a00) (A1.2 .f .trr a10)
| x .trr1 : A0 .t → A1 .t
| x .trl.p
  : (a01 : A0.1 .t) (a11 : A1.1 .t) (a21 : R.1 a01 a11)
    → R.0 (A0.2 .f .trl a01) (A1.2 .f .trl a11)
| x .trl1 : A1 .t → A0 .t
| x .liftr.p
  : (a00 : A0.0 .t) (a10 : A1.0 .t) (a20 : R.0 a00 a10)
    → R.2 (A0.2 .f .liftr a00) (A1.2 .f .liftr a10) a20
        (x .trr a00 a10 a20)
| x .liftr1 : (a0 : A0 .t) → R a0 (x .trr1 a0)
| x .liftl.p
  : (a01 : A0.1 .t) (a11 : A1.1 .t) (a21 : R.1 a01 a11)
    → R.2 (A0.2 .f .liftl a01) (A1.2 .f .liftl a11) (x .trl a01 a11 a21)
        a21
| x .liftl1 : (a1 : A1 .t) → R (x .trl1 a1) a1
| x .id.p
  : (a00 : A0.0 .t) (a10 : A1.0 .t) (a20 : R.0 a00 a10) (a01 : A0.1 .t)
    (a11 : A1.1 .t) (a21 : R.1 a01 a11)
    → Br_isFibrant_corr (A0.2 .t a00 a01, A0.2 .f .id a00 a01)
        (A1.2 .t a10 a11, A1.2 .f .id a10 a11)
        (a02 a12 ↦ R.2 a02 a12 a20 a21)
| x .id1 : (a0 : A0 .t) (a1 : A1 .t) → isFibrant (R a0 a1) ]

{` An intended bisimulation between [Br isFibrant] and [Br_isFibrant_corr]. `}

def Br_Br_isFibrant (A0 A1 : Fib) (A2t : Br Type (A0 .t) (A1 .t))
  (R : A0 .t → A1 .t → Type)
  (e : (a0 : A0 .t) (a1 : A1 .t) → A2t a0 a1 ≅ R a0 a1)
  (A2f : Br isFibrant A2t (A0 .f) (A1 .f)) (Rf : Br_isFibrant_corr A0 A1 R)
  : Type
  ≔ codata [
| x .trr.p
  : (a00 : A0.0 .t) (a10 : A1.0 .t) (a20 : R.0 a00 a10)
    → eq (R.1 (A0.2 .f .trr a00) (A1.2 .f .trr a10))
        (e.1 (A0.2 .f .trr a00) (A1.2 .f .trr a10)
         .to (A2f .trr.2 (e.0 a00 a10 .fro a20))) (Rf .trr a00 a10 a20)
| x .trr1 : (a0 : A0 .t) → eq (A1 .t) (A2f .trr.1 a0) (Rf .trr1 a0)
| x .liftr.p : (a00 : A0.0 .t) (a10 : A1.0 .t) (a20 : R.0 a00 a10) → ¿ʔ
| x .liftr1
  : (a0 : A0 .t)
    → eqd (A1 .t) (R a0) (A2f .trr.1 a0) (Rf .trr1 a0) (x .trr1 a0)
        (e a0 (A2f .trr.1 a0) .to (A2f .liftr.1 a0)) (Rf .liftr1 a0)
| x .trl.p : ¿ʔ
| x .trl1 : ¿ʔ
| x .liftl.p : ¿ʔ
| x .liftl1 : ¿ʔ
| x .id.p
  : (a00 : A0.0 .t) (a10 : A1.0 .t) (a20 : R.0 a00 a10) (a01 : A0.1 .t)
    (a11 : A1.1 .t) (a21 : R.1 a01 a11)
    → Br_Br_isFibrant (A0.2 .t a00 a01, A0.2 .f .id a00 a01)
        (A1.2 .t a10 a11, A1.2 .f .id a10 a11)
        (sym A2t.2 (e.0 a00 a10 .fro a20) (e.1 a01 a11 .fro a21))
        (a02 a12 ↦ R.2 {a00} {a01} a02 {a10} {a11} a12 a20 a21)
        (a02 a12 ↦
         comp_eqv
           (sym A2t.2 (e.0 a00 a10 .fro a20) (e.1 a01 a11 .fro a21) a02 a12)
           (A2t.2 a02 a12 (e.0 a00 a10 .fro a20) (e.1 a01 a11 .fro a21))
           (R.2 {a00} {a01} a02 {a10} {a11} a12 a20 a21)
           (sym_eqv′ (A0.0 .t) (A0.1 .t) (A0.2 .t) (A1.0 .t) (A1.1 .t)
              (A1.2 .t) A2t.0 A2t.1 A2t.2 a00 a01 a02 a10 a11 a12
              (e.0 a00 a10 .fro a20) (e.1 a01 a11 .fro a21))
           (Id_eqv (A2t.0 a00 a10) (A2t.1 a01 a11) (A2t.2 a02 a12)
              (R.0 a00 a10) (R.1 a01 a11)
              (R.2 {a00} {a01} a02 {a10} {a11} a12) (e.0 a00 a10)
              (e.1 a01 a11) (e.2 a02 a12) a20 a21))
        (A2f .id.2 (e.0 a00 a10 .fro a20) (e.1 a01 a11 .fro a21))
        (Rf .id.1 a00 a10 a20 a01 a11 a21)
| x .id1
  : (a0 : A0 .t) (a1 : A1 .t)
    → isFibrant_iso (A2t a0 a1) (R a0 a1) (e a0 a1) (A2f .id.1 a0 a1)
        (Rf .id1 a0 a1) ]

{` Proving that this is a bisimulation will similarly involve recursing into more general HCTs. `}

{`
In general, given

0. A parameter type Γ (here Fib × Fib)
1. A type family ∂ : Γ → Type (here (A0, A1) ↦ A0 × A1)
2. A type family B : Γ → Type (here (A0, A1) ↦ Br Type (A0 .t) (A1 .t))
3. A function f : (γ:Γ) → B γ → ∂ γ → Type (here (A0, A1) A2 (a0, a1) ↦ A2 a0 a1)
4. Nonrecursive destructors for a higher coinductive type with parameters Σ Γ (γ ↦ ∂ γ → Type) (here the tr/lift fields of Br_isFibrant_corr)
5. Recursive higher destructors over Σ Γ B and Σ Γ (γ ↦ ∂ γ → Type) that commute with f (here the id.p fields of Br isFibrant and Br_isFibrant_corr)
6. Nonrecursive destructors landing in some other HCT parametrized by ... (here the id.1 fields)
7. Assume that pointwise isomorphism is, for each γ, a bisimulation from B γ to ∂ γ → Type.

We can define a "bridging" HCT forming a bisimulation between the sums of the two HCTs on both sides.

Then we get a bisimulation between Br Fib A B and Σ Br_isFibrant_corr.  Unrolling Br_isFibrant_corr once we get a sum over Fib-valued correspondences of a bunch of fibrant stuff plus Br_isFibrant_corr of some stuff that will hopefully make it fibrant.

`}
