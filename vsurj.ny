{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"
import "univalence"

{` Some general facts that aren't in Narya yet. `}

def mapΣ (A B : Type) (f : A → B) (Aᵈ : A → Type) (Bᵈ : B → Type)
  (fᵈ : (x : A) → Aᵈ x → Bᵈ (f x))
  : Σ A Aᵈ → Σ B Bᵈ
  ≔ u ↦ (f (u .fst), fᵈ (u .fst) (u .snd))

def Id_eql (A0 A1 : Type) (A2 : Br Type A0 A1) (a00 : A0) (a01 : A1)
  (a02 : A2 a00 a01) (a10 : A0) (a11 : A1) (a12 : A2 a10 a11)
  (a20 : eq A0 a00 a10) (a21 : eq A1 a01 a11)
  (a22 : Br eq A2 a02 a12 a20 a21)
  : eq (A2 a00 a01) a02
      (eq.trl2 A0 A1 (x y ↦ A2 x y) a00 a10 a20 a01 a11 a21 a12)
  ≔ match a22 [ rfl. ⤇ rfl. ]

{` Very surjective functions `}

{` A function is "very surjective", a.k.a. a "trivial fibration", if it is (split) surjective "up to bridges", and all aps of it are also very surjective, higher-coinductively.  It may seem odd that we can get away with surjectivity up to bridges, but in the only place we use it these bridges will actually like in a fibrant type, so they will behave like equalities. `}
def vsurj (A B : Type) (f : A → B) : Type ≔ codata [
| s .surj : B → A
| s .surjeq : (b : B) → Br B (f (s .surj b)) b
| s .id.p
  : (a0 : A.0) (a1 : A.1)
    → vsurj (A.2 a0 a1) (B.2 (f.0 a0) (f.1 a1)) (a2 ↦ f.2 a2) ]

{` This yields surjectivity on all cubes relative to their boundaries, justifying the name. `}
axiom X : Type
axiom Y : Type
axiom f : X → Y
axiom s : vsurj X Y f

{` Surjectivity on points `}
echo s .surj

{` Surjectivity on paths `}
axiom x0 : X
axiom x1 : X
echo rel s .id x0 x1 .surj

{` Surjectivity on squares `}
axiom x00 : X
axiom x01 : X
axiom x02 : Br X x00 x01
axiom x10 : X
axiom x11 : X
axiom x12 : Br X x10 x11
axiom x20 : Br X x00 x10
axiom x21 : Br X x01 x11
echo rel (rel s) .id.1 x02 x12 .id x20 x21 .surj

{` Very-surjectivity transports across Book HoTT equivalences. `}
def vsurj_eqv (A0 B0 : Type) (f0 : A0 → B0) (A1 B1 : Type) (f1 : A1 → B1)
  (eA : A0 ≅ A1) (eB : B0 ≅ B1)
  (ef : (x : A0) → eq.eq B1 (eB .to (f0 x)) (f1 (eA .to x)))
  (s0 : vsurj A0 B0 f0)
  : vsurj A1 B1 f1
  ≔ [
| .surj ↦ b1 ↦ eA .to (s0 .surj (eB .fro b1))
| .surjeq ↦ b1 ↦
    eq.trr2 B1 B1 (x y ↦ Br B1 x y) (eB .to (f0 (s0 .surj (eB .fro b1))))
      (f1 (eA .to (s0 .surj (eB .fro b1)))) (ef (s0 .surj (eB .fro b1)))
      (eB .to (eB .fro b1)) b1 (eB .to_fro b1)
      (rel (eB .to) (s0 .surjeq (eB .fro b1)))
| .id.p ↦ a0 a1 ↦
    vsurj_eqv (A0.2 (eA.0 .fro a0) (eA.1 .fro a1))
      (B0.2 (f0.0 (eA.0 .fro a0)) (f0.1 (eA.1 .fro a1))) (a2 ↦ f0.2 a2)
      (A1.2 a0 a1) (B1.2 (f1.0 a0) (f1.1 a1)) (a2 ↦ f1.2 a2)
      (Id_eqv A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 eA.0 eA.1 eA.2 a0 a1)
      (comp_eqv (B0.2 (f0.0 (eA.0 .fro a0)) (f0.1 (eA.1 .fro a1)))
         (B0.2 (eB.0 .fro (f1.0 a0)) (eB.1 .fro (f1.1 a1)))
         (B1.2 (f1.0 a0) (f1.1 a1))
         (eqv_trr2 B0.0 B0.1 (x y ↦ B0.2 x y) (f0.0 (eA.0 .fro a0))
            (eB.0 .fro (f1.0 a0))
            (eqv_transpose A0.0 B0.0 f0.0 A1.0 B1.0 f1.0 eA.0 eB.0 ef.0 a0)
            (f0.1 (eA.1 .fro a1)) (eB.1 .fro (f1.1 a1))
            (eqv_transpose A0.1 B0.1 f0.1 A1.1 B1.1 f1.1 eA.1 eB.1 ef.1 a1))
         (Id_eqv B0.0 B0.1 B0.2 B1.0 B1.1 B1.2 eB.0 eB.1 eB.2 (f1.0 a0)
            (f1.1 a1)))
      ` Hole to be filled here, should be just lots of path algebra
      (a2 ↦
       ¿
Id_eq B1.0 B1.1 B1.2 (eB.0 .to (f0.0 (eA.0 .fro a0))) (eB.1 .to (f0.1 (eA.1 .fro a1))) (eB.2 .to (f0.2 a2)) (f1.0 (eA.0 .to (eA.0 .fro a0))) (f1.1 (eA.1 .to (eA.1 .fro a1)))  (f1.2 (eA.2 .to a2)) (ef.0 (eA.0 .fro a0)) (ef.1 (eA.1 .fro a1)) (ef.2 a2)
 ʔ)
      (s0.2 .id (eA.0 .fro a0) (eA.1 .fro a1))]

{` Here's the crucial bit: if the codomain of a very-surjective function is fibrant, then so is its domain.  Note that this is the only place where we use the bridge .surjeq, and in this case it lies in a fibrant type, so it acts like an equality. `}
def fib_vsurj (A B : Type) (f : A → B) (s : vsurj A B f) (fB : isFibrant B)
  : isFibrant A
  ≔ [
| .trr.p ↦ a0 ↦ s.1 .surj (fB.2 .trr (f.0 a0))
| .trl.p ↦ a1 ↦ s.0 .surj (fB.2 .trl (f.1 a1))
| .liftr.p ↦ a0 ↦
    s.2
      .id a0 (s.1 .surj (fB.2 .trr (f.0 a0)))
      .surj
        (rel (b1 ↦ fB.2 .id (f.0 a0) b1) (s.1 .surjeq (fB.2 .trr (f.0 a0)))
         .trl (fB.2 .liftr (f.0 a0)))
| .liftl.p ↦ a1 ↦
    s.2
      .id (s.0 .surj (fB.2 .trl (f.1 a1))) a1
      .surj
        (rel (b0 ↦ fB.2 .id b0 (f.1 a1)) (s.0 .surjeq (fB.2 .trl (f.1 a1)))
         .trl (fB.2 .liftl (f.1 a1)))
| .id.p ↦ a0 a1 ↦
    fib_vsurj (A.2 a0 a1) (B.2 (f.0 a0) (f.1 a1)) (a2 ↦ f.2 a2)
      (s .id a0 a1) (fB .id (f.0 a0) (f.1 a1))]

{` Now the game is that to prove something is fibrant, like "Br Fib A0 A1", it suffices to show that it admits a very-surjective map to some other type that we know is fibrant. `}

{` To build this, we start with a dependent/displayed version of very-surjective. `}
def vsurjᵈ (A B : Type) (f : A → B) (Aᵈ : A → Type) (Bᵈ : B → Type)
  (fᵈ : (x : A) → Aᵈ x → Bᵈ (f x)) (s : vsurj A B f)
  : Type
  ≔ codata [
| t .surj : (b : B) → Bᵈ b → Aᵈ (s .surj b)
| t .surjeq
  : (b : B) (b' : Bᵈ b)
    → Br Bᵈ (s .surjeq b) (fᵈ (s .surj b) (t .surj b b')) b'
| t .id.p
  : (a0 : A.0) (a0' : Aᵈ.0 a0) (a1 : A.1) (a1' : Aᵈ.1 a1)
    → vsurjᵈ (A.2 a0 a1) (B.2 (f.0 a0) (f.1 a1)) (a2 ↦ f.2 a2)
        (a2 ↦ Aᵈ.2 a2 a0' a1') (b2 ↦ Bᵈ.2 b2 (fᵈ.0 a0 a0') (fᵈ.1 a1 a1'))
        (a2 a2' ↦ fᵈ.2 a2 a2') (s.2 .id a0 a1) ]

{` A displayed very-surjective map over a very-surjective one has a very-surjective Σ-map. `}
def vsurjΣ (A B : Type) (f : A → B) (Aᵈ : A → Type) (Bᵈ : B → Type)
  (fᵈ : (x : A) → Aᵈ x → Bᵈ (f x)) (s : vsurj A B f)
  (sᵈ : vsurjᵈ A B f Aᵈ Bᵈ fᵈ s)
  : vsurj (Σ A Aᵈ) (Σ B Bᵈ) (mapΣ A B f Aᵈ Bᵈ fᵈ)
  ≔ [
| .surj ↦ v ↦ (s .surj (v .fst), sᵈ .surj (v .fst) (v .snd))
| .surjeq ↦ v ↦ (s .surjeq (v .fst), sᵈ .surjeq (v .fst) (v .snd))
| .id.p ↦ u0 u1 ↦
    vsurj_eqv
      (Σ (A.2 (u0 .fst) (u1 .fst)) (a2 ↦ Aᵈ.2 a2 (u0 .snd) (u1 .snd)))
      (Σ (B.2 (f.0 (u0 .fst)) (f.1 (u1 .fst)))
         (b2 ↦
          Bᵈ.2 b2 (fᵈ.0 (u0 .fst) (u0 .snd)) (fᵈ.1 (u1 .fst) (u1 .snd))))
      (mapΣ (A.2 (u0 .fst) (u1 .fst)) (B.2 (f.0 (u0 .fst)) (f.1 (u1 .fst)))
         (a2 ↦ f.2 {u0 .fst} {u1 .fst} a2)
         (a2 ↦ Aᵈ.2 a2 (u0 .snd) (u1 .snd))
         (b2 ↦
          Bᵈ.2 b2 (fᵈ.0 (u0 .fst) (u0 .snd)) (fᵈ.1 (u1 .fst) (u1 .snd)))
         (a2 a2' ↦ fᵈ.2 a2 a2')) (Σ⁽ᵖ⁾ A.2 Aᵈ.2 u0 u1)
      (Σ⁽ᵖ⁾ B.2 Bᵈ.2 (mapΣ A.0 B.0 f.0 Aᵈ.0 Bᵈ.0 fᵈ.0 u0)
         (mapΣ A.1 B.1 f.1 Aᵈ.1 Bᵈ.1 fᵈ.1 u1))
      (a2 ↦ rel mapΣ A.2 B.2 f.2 Aᵈ.2 Bᵈ.2 fᵈ.2 a2)
      (id_Σ_iso A.0 A.1 A.2 Aᵈ.0 Aᵈ.1 Aᵈ.2 (u0 .fst) (u1 .fst) (u0 .snd)
         (u1 .snd))
      (id_Σ_iso B.0 B.1 B.2 Bᵈ.0 Bᵈ.1 Bᵈ.2 (f.0 (u0 .fst)) (f.1 (u1 .fst))
         (fᵈ.0 (u0 .fst) (u0 .snd)) (fᵈ.1 (u1 .fst) (u1 .snd))) (u2 ↦ rfl.)
      (vsurjΣ (A.2 (u0 .fst) (u1 .fst))
         (B.2 (f.0 (u0 .fst)) (f.1 (u1 .fst))) (a2 ↦ f.2 a2)
         (a2 ↦ Aᵈ.2 a2 (u0 .snd) (u1 .snd))
         (b2 ↦
          Bᵈ.2 b2 (fᵈ.0 (u0 .fst) (u0 .snd)) (fᵈ.1 (u1 .fst) (u1 .snd)))
         (a2 a2' ↦ fᵈ.2 a2 a2') (s .id (u0 .fst) (u1 .fst))
         (sᵈ .id (u0 .fst) (u0 .snd) (u1 .fst) (u1 .snd)))]

{` Now we can state "the existence of Gel-types in all dimensions at once" as the fact that the "instantiation" map from bridges in the universe to correspondences is very surjective.  We can't *prove* the whole thing internally to Narya today, since it doesn't have a syntax for Gel types parametrized over dimensions.  But since the pattern is very systematic, non-dependent, and entirely parametric without involving any fibrancy, we should be able to modify Narya to build-in an inhabitant of this type. `}
def vsurj_gel (A0 A1 : Type)
  : vsurj (Br Type A0 A1) (A0 → A1 → Type) (A2 ↦ a0 a1 ↦ A2 a0 a1)
  ≔ [
| .surj ↦ A2 ↦ Gel A0 A1 A2
| .surjeq ↦ A2 ↦ a0 a1 ⤇
    Gel (Gel A0 A1 A2 a0.0 a1.0) (A2 a0.1 a1.1)
      (a20 a21 ↦ Br A2 a0.2 a1.2 (a20 .ungel) a21)
| .id.p ↦ A20 A21 ↦ [
  | .surj ↦ A22 ↦
      Gel2 A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 A20 A21
        (a00 a01 a02 a10 a11 a12 a20 a21 ↦ A22 a02 a12 a20 a21)
  | .surjeq ↦ A22 ↦ a0 a1 ⤇
      Gel2 (A20 a0.00 a1.00) (A20 a0.01 a1.01) (Br A20 a0.02 a1.02)
        (A21 a0.10 a1.10) (A21 a0.11 a1.11) (Br A21 a0.12 a1.12)
        (Gel2 A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 A20 A21
           (a00 a01 a02 a10 a11 a12 a20 a21 ↦ A22 a02 a12 a20 a21) a0.20
           a1.20) (A22 a0.21 a1.21)
        (a200 a201 a202 a210 a211 a212 a220 a221 ↦
         Br A22 a0.22 a1.22 a202 a212 (a220 .ungel) a221)
  | .id.p ↦ ¿ʔ]]

{` Now I claim that the map from Br-isFibrant that extracts both pointwise fibrancy and bisimulation structure is *displayed* very-surjective over the above.  At the first level this is just univalence (for isBisim).  I hope the rest of it should be provable by corecursion, as a generalization of univalence -- although probably not in Narya today (see below). `}
def vsurjᵈ_glue (A0 A1 : Fib)
  : vsurjᵈ (Br Type (A0 .t) (A1 .t)) (A0 .t → A1 .t → Type)
      (A2 ↦ a0 a1 ↦ A2 a0 a1) (A2 ↦ Br isFibrant A2 (A0 .f) (A1 .f))
      (A2t ↦
       Σ ((a0 : A0 .t) (a1 : A1 .t) → isFibrant (A2t a0 a1))
         (A2f ↦ isBisim A0 A1 (a0 a1 ↦ (A2t a0 a1, A2f a0 a1))))
      (A2t A2f ↦ (fst ≔ A2f .id, snd ≔ bisim_of_Id A0 A1 (A2t, A2f)))
      (vsurj_gel (A0 .t) (A1 .t))
  ≔ [
| .surj ↦ A2t A2f ↦
    univalence_bisim A0 A1 (a0 a1 ↦ (A2t a0 a1, A2f .fst a0 a1)) (A2f .snd)
      .f
| .surjeq ↦ ¿ʔ
| .id.p ↦ ¿ʔ]

{` Given that claim, we can deduce that the map from Br-Fib to pointwise-fibrant bisimulations is very surjective. `}
def vsurj_brfib (A0 A1 : Fib)
  : vsurj (Br Fib A0 A1) (Σ (A0 .t → A1 .t → Fib) (A2 ↦ isBisim A0 A1 A2))
      (A2 ↦ (a0 a1 ↦ Idd𝕗 A0 A1 A2 a0 a1, bisim_of_Id A0 A1 A2))
  ≔ vsurj_eqv
      (Σ (Type⁽ᵖ⁾ (A0 .t) (A1 .t)) (A2 ↦ isFibrant⁽ᵖ⁾ A2 (A0 .f) (A1 .f)))
      (Σ (A0 .t → A1 .t → Type)
         (A2t ↦
          Σ ((a0 : A0 .t) (a1 : A1 .t) → isFibrant (A2t a0 a1))
            (A2f ↦ isBisim A0 A1 (a0 a1 ↦ (A2t a0 a1, A2f a0 a1)))))
      (mapΣ (Type⁽ᵖ⁾ (A0 .t) (A1 .t)) (A0 .t → A1 .t → Type)
         (A2 a0 a1 ↦ A2 a0 a1) (A2 ↦ isFibrant⁽ᵖ⁾ A2 (A0 .f) (A1 .f))
         (A2t ↦
          Σ ((a0 : A0 .t) (a1 : A1 .t) → isFibrant (A2t a0 a1))
            (A2f ↦ isBisim A0 A1 (a0 a1 ↦ (A2t a0 a1, A2f a0 a1))))
         (A2t A2f ↦ (fst ≔ A2f .id, snd ≔ bisim_of_Id A0 A1 (A2t, A2f))))
      (Br Fib A0 A1) (Σ (A0 .t → A1 .t → Fib) (A2 ↦ isBisim A0 A1 A2))
      (A2 ↦ (a0 a1 ↦ Idd𝕗 A0 A1 A2 a0 a1, bisim_of_Id A0 A1 A2))
      (to ≔ x ↦ (t ≔ x .fst, f ≔ x .snd),
       fro ≔ y ↦ (fst ≔ y .t, snd ≔ y .f),
       fro_to ≔ x ↦ rfl.,
       to_fro ≔ y ↦ rfl.,
       to_fro_to ≔ x ↦ rfl.)
      (to ≔ x ↦ (
         fst ≔ a0 a1 ↦ (t ≔ x .fst a0 a1, f ≔ x .snd .fst a0 a1),
         snd ≔ x .snd .snd),
       fro ≔ y ↦ (
         fst ≔ a0 a1 ↦ y .fst a0 a1 .t,
         snd ≔ (fst ≔ a0 a1 ↦ y .fst a0 a1 .f, snd ≔ y .snd)),
       fro_to ≔ x ↦ rfl.,
       to_fro ≔ y ↦ rfl.,
       to_fro_to ≔ x ↦ rfl.) (x ↦ rfl.)
      (vsurjΣ (Br Type (A0 .t) (A1 .t)) (A0 .t → A1 .t → Type)
         (A2 ↦ a0 a1 ↦ A2 a0 a1) (A2 ↦ Br isFibrant A2 (A0 .f) (A1 .f))
         (A2t ↦
          Σ ((a0 : A0 .t) (a1 : A1 .t) → isFibrant (A2t a0 a1))
            (A2f ↦ isBisim A0 A1 (a0 a1 ↦ (A2t a0 a1, A2f a0 a1))))
         (A2t A2f ↦ (fst ≔ A2f .id, snd ≔ bisim_of_Id A0 A1 (A2t, A2f)))
         (vsurj_gel (A0 .t) (A1 .t)) (vsurjᵈ_glue A0 A1))

{` And therefore, since its codomain is fibrant (corecursively), so is its domain. `}
def 𝕗Fib : isFibrant Fib ≔ [
| .trr.p ↦ X ↦ X
| .trl.p ↦ X ↦ X
| .liftr.p ↦ X ↦ rel X
| .liftl.p ↦ X ↦ rel X
| .id.p ↦ A0 A1 ↦
    fib_vsurj (Br Fib A0 A1)
      (Σ (A0 .t → A1 .t → Fib) (A2 ↦ isBisim A0 A1 A2))
      (A2 ↦ (a0 a1 ↦ Idd𝕗 A0 A1 A2 a0 a1, bisim_of_Id A0 A1 A2))
      (vsurj_brfib A0 A1)
      (𝕗Σ (A0 .t → A1 .t → Fib) (A2 ↦ isBisim A0 A1 A2)
         (𝕗Π (A0 .t) (_ ↦ A1 .t → Fib) (A0 .f)
            (a0 ↦
             𝕗Π (A1 .t) (_ ↦ Fib) (A1 .f)
               ` Here is a corecursive call.  Hopefully something like Szumi's trick would make this guarded.
               (_ ↦ 𝕗Fib)))
         ` And here we just need to know that higher coinductive types with all fibrant inputs and parameters are fibrant.  This should be true, though not provable internally to Narya today (see below).
         (A2 ↦ ¿ʔ))]

{` In addition to building in vsurj_gel, what's missing to be able to finish these proofs in Narya is the ability to prove generic things about higher coinductive types for vsurjᵈ_glue and "isFibrant isBisim".  The problem is that the higher coinductive type changes as we pass to higher dimensions in the corecursive cases.  The obvious idea would be to formulate a general family of such (a "higher indexed M-type") and then generalize the statement to apply to all of them, so that the corecursive case is an honest corecursive call to a different element of the family.  But I think in order for that to work, the parameters of the family have to be "modal" in some way that prevent them from getting degenerated in the context of higher destructors; see "test/black/hct-hott.t/fibrant_sqrt.ny". `}

` it seems that we need to assume A, B, B' are fibrant to make this
` work. we only have funext for fibrant types. in the place where we
` want to apply it, we only have that A is fibrant
def vsurj_fun (A : Type) (B B' : A → Type) (f : (a : A) → B a → B' a)
  (v : (a : A) → vsurj (B a) (B' a) (f a))
  : vsurj ((a : A) → B a) ((a : A) → B' a) (g a ↦ f a (g a))
  ≔ [
| .surj ↦ g' a ↦ v a .surj (g' a)
| .surjeq ↦ g' ↦ {a₀} {a₁} a₂ ↦ ¿v a₀ .surjeq (g' a₀)ʔ
| .id.p ↦ ¿ʔ]

` this doesn't work either:
def vsurj_fun' (A : Type) (B B' : A → Type)
  (f : (a₀ a₁ : A) (a₂ : Br A a₀ a₁) → B a₀ → B' a₁)
  (v : (a₀ a₁ : A) (a₂ : Br A a₀ a₁) → vsurj (B a₀) (B' a₁) (f a₀ a₁ a₂))
  : vsurj ((a : A) → B a) ((a : A) → B' a) (g a ↦ f a a (rel a) (g a))
  ≔ [
| .surj ↦ g' a ↦ v a a (rel a) .surj (g' a)
| .surjeq ↦ g' ↦ {a₀} {a₁} a₂ ↦ ¿v a₀ a₁ a₂ .surjeq (g' a₁)ʔ
| .id.p ↦ ¿ʔ]

` we cannot prove the following closure of vsurj under × this way, we
` need a more heterogeneous version (this is also a consequence of
` vsurjΣ); this shows why we are in trouble if we want to prove
def vsurj× (A B : Type) (f : A → B) (v : vsurj Aa B f)
  : vsurj (A × A) (B × B) (aa ↦ (f (aa .fst), f (aa .snd)))
  ≔ [
| .surj ↦ bb ↦ (v .surj (bb .fst), v .surj (bb .snd))
| .surjeq ↦ bb ↦ (fst ≔ v .surjeq (bb .fst), snd ≔ v .surjeq (bb .snd))
| .id.p ↦ aa₀ aa₁ ↦
    vsurj_eqv (A.2 (aa₀ .fst) (aa₁ .fst) × A.2 (aa₀ .snd) (aa₁ .snd))
      (B.2 (f.0 (aa₀ .fst)) (f.1 (aa₁ .fst))
       × B.2 (f.0 (aa₀ .snd)) (f.1 (aa₁ .snd)))
      (aa₂ ↦ (f.2 (aa₂ .fst), f.2 (aa₂ .snd))) (prod⁽ᵖ⁾ A.2 A.2 aa₀ aa₁)
      (prod⁽ᵖ⁾ B.2 B.2 (f.0 (aa₀ .fst), f.0 (aa₀ .snd))
         (f.1 (aa₁ .fst), f.1 (aa₁ .snd)))
      (a2 ↦ (f.2 (a2 .fst), f.2 (a2 .snd)))
      (id_prod_iso A.0 A.1 A.2 A.0 A.1 A.2 (aa₀ .fst) (aa₁ .fst) (aa₀ .snd)
         (aa₁ .snd))
      (id_prod_iso B.0 B.1 B.2 B.0 B.1 B.2 (f.0 (aa₀ .fst))
         (f.1 (aa₁ .fst)) (f.0 (aa₀ .snd)) (f.1 (aa₁ .snd))) (aa₂ ↦ rfl.)
      ¿vsurj× (A.2 (aa₀ .fst) (aa₁ .fst)) (A.2 (aa₀ .snd) (aa₁ .snd)) ()ʔ]
