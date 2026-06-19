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

{` A function is "very surjective", a.k.a. a "trivial fibration", if it is (split) surjective "up to bridges", and all aps of it are also very surjective, higher-coinductively.  It may seem odd that we can get away with surjectivity up to bridges, but in the only place we use it these bridges will actually like in a fibrant type, so they will behave like equalities.  We do, however, need these to be possibly-heterogeneous bridges. `}
def vsurj (A B : Type) (f : A → B) : Type ≔ codata [
| s .surj : B → A
| s .surjeq.p
  : (b0 : B.0) (b1 : B.1) (b2 : B.2 b0 b1) → B.2 (f.0 (s.0 .surj b0)) b1
| s .id.p
  : (a0 : A.0) (a1 : A.1)
    → vsurj (A.2 a0 a1) (B.2 (f.0 a0) (f.1 a1)) (a2 ↦ f.2 a2) ]

{` Very-surjectivity transports across Book HoTT equivalences. `}
def vsurj_eqv (A0 B0 : Type) (f0 : A0 → B0) (A1 B1 : Type) (f1 : A1 → B1)
  (eA : A0 ≅ A1) (eB : B0 ≅ B1)
  (ef : (x : A0) → eq.eq B1 (eB .to (f0 x)) (f1 (eA .to x)))
  (s0 : vsurj A0 B0 f0)
  : vsurj A1 B1 f1
  ≔ [
| .surj ↦ b1 ↦ eA .to (s0 .surj (eB .fro b1))
| .surjeq.p ↦ b10 b11 b12 ↦
    eq.trr2 B1.0 B1.1 (x y ↦ B1.2 x y)
      (eB.0 .to (f0.0 (s0.0 .surj (eB.0 .fro b10))))
      (f1.0 (eA.0 .to (s0.0 .surj (eB.0 .fro b10))))
      (ef.0 (s0.0 .surj (eB.0 .fro b10))) (eB.1 .to (eB.1 .fro b11)) b11
      (eB.1 .to_fro b11)
      (eB.2 .to
         (s0.2 .surjeq (eB.0 .fro b10) (eB.1 .fro b11) (eB.2 .fro b12)))
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


def vsurj_fun (A : Type) (B B' : A → Type) (f : (a : A) → B a → B' a)
  (v : (a : A) → vsurj (B a) (B' a) (f a))
  : vsurj ((a : A) → B a) ((a : A) → B' a) (g a ↦ f a (g a))
  ≔ [
| .surj ↦ g' a ↦ v a .surj (g' a)
| .surjeq.p ↦ g0 g1 g2 ↦ a ⤇ v.2 a.2 .surjeq (g0 a.0) (g1 a.1) (g2 a.2)
| .id.p ↦ g0 g1 ↦
    vsurj_eqv
      ((a₀ : A.0) (a₁ : A.1) (a₂ : A.2 a₀ a₁) → B.2 a₂ (g0 a₀) (g1 a₁))
      ((a₀ : A.0) (a₁ : A.1) (a₂ : A.2 a₀ a₁)
       → B'.2 a₂ (f.0 a₀ (g0 a₀)) (f.1 a₁ (g1 a₁)))
      (g2 ↦ a0 a1 a2 ↦ f.2 a2 (g2 a0 a1 a2))
      ({a₀ : A.0} {a₁ : A.1} (a₂ : A.2 a₀ a₁) →⁽ᵖ⁾ B.2 a₂ (g0 a₀) (g1 a₁))
      ({a₀ : A.0} {a₁ : A.1} (a₂ : A.2 a₀ a₁)
       →⁽ᵖ⁾ B'.2 a₂ (f.0 a₀ (g0 a₀)) (f.1 a₁ (g1 a₁)))
      (g2 ↦ a ⤇ f.2 a.2 (g2 a.2)) (id_Π_iso A.0 A.1 A.2 B.0 B.1 B.2 g0 g1)
      (id_Π_iso A.0 A.1 A.2 B'.0 B'.1 B'.2 (a0 ↦ f.0 a0 (g0 a0))
         (a1 ↦ f.1 a1 (g1 a1))) (g2 ↦ rfl.)
      (vsurj_fun A.0
         (a₀ ↦ (a₁ : A.1) (a₂ : A.2 a₀ a₁) → B.2 a₂ (g0 a₀) (g1 a₁))
         (a₀ ↦
          (a₁ : A.1) (a₂ : A.2 a₀ a₁)
          → B'.2 a₂ (f.0 a₀ (g0 a₀)) (f.1 a₁ (g1 a₁)))
         (a₀ g2 a₁ a₂ ↦ f.2 a₂ (g2 a₁ a₂))
         (a₀ ↦
          vsurj_fun A.1 (a₁ ↦ (a₂ : A.2 a₀ a₁) → B.2 a₂ (g0 a₀) (g1 a₁))
            (a₁ ↦
             (a₂ : A.2 a₀ a₁) → B'.2 a₂ (f.0 a₀ (g0 a₀)) (f.1 a₁ (g1 a₁)))
            (a₁ g2 a₂ ↦ f.2 a₂ (g2 a₂))
            (a₁ ↦
             vsurj_fun (A.2 a₀ a₁) (a₂ ↦ B.2 a₂ (g0 a₀) (g1 a₁))
               (a₂ ↦ B'.2 a₂ (f.0 a₀ (g0 a₀)) (f.1 a₁ (g1 a₁)))
               (a₂ b₂ ↦ f.2 a₂ b₂) (a₂ ↦ v.2 a₂ .id (g0 a₀) (g1 a₁)))))]

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
        (rel (b1 ↦ fB.2 .id (f.0 a0) b1)
             (rel s.1
              .surjeq (fB.2 .trr (f.0 a0)) (fB.2 .trr (f.0 a0))
                (rel (fB.2 .trr (f.0 a0))))
         .trl (fB.2 .liftr (f.0 a0)))
| .liftl.p ↦ a1 ↦
    s.2
      .id (s.0 .surj (fB.2 .trl (f.1 a1))) a1
      .surj
        (rel (b0 ↦ fB.2 .id b0 (f.1 a1))
             (rel s.0
              .surjeq (fB.2 .trl (f.1 a1)) (fB.2 .trl (f.1 a1))
                (rel (fB.2 .trl (f.1 a1))))
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
| t .surjeq.p
  : (b0 : B.0) (b1 : B.1) (b2 : B.2 b0 b1) (b0' : Bᵈ.0 b0) (b1' : Bᵈ.1 b1)
    (b2' : Bᵈ.2 b2 b0' b1')
    → Bᵈ.2 (s.2 .surjeq.1 b0 b1 b2)
        (fᵈ.0 (s.0 .surj b0) (t.0 .surj b0 b0')) b1'
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
| .surjeq.p ↦ v0 v1 v2 ↦ (
    s.2 .surjeq (v0 .fst) (v1 .fst) (v2 .fst),
    sᵈ.2 .surjeq (v0 .fst) (v1 .fst) (v2 .fst) (v0 .snd) (v1 .snd)
      (v2 .snd))
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
| .surjeq.p ↦ A20 A21 A22 ↦ a0 a1 ⤇
    Gel (Gel A0.0 A1.0 A20 a0.0 a1.0) (A21 a0.1 a1.1)
      (a20 a21 ↦ A22 a0.2 a1.2 (a20 .ungel) a21)
| .id.p ↦ A20 A21 ↦ [
  | .surj ↦ A22 ↦
      Gel2 A0.0 A0.1 A0.2 A1.0 A1.1 A1.2 A20 A21
        (a00 a01 a02 a10 a11 a12 a20 a21 ↦ A22 a02 a12 a20 a21)
  | .surjeq.p ↦ A220 A221 A222 ↦ a0 a1 ⤇
      Gel2 (A20.0 a0.00 a1.00) (A20.1 a0.01 a1.01) (A20.2 a0.02 a1.02)
        (A21.0 a0.10 a1.10) (A21.1 a0.11 a1.11) (A21.2 a0.12 a1.12)
        (Gel2 A0.00 A0.10 A0.20 A1.00 A1.10 A1.20 A20.0 A21.0
           (a00 a01 a02 a10 a11 a12 a20 a21 ↦ A220 a02 a12 a20 a21) a0.20
           a1.20) (A221 a0.21 a1.21)
        (a200 a201 a202 a210 a211 a212 a220 a221 ↦
         A222 a0.22 a1.22 a202 a212 (a220 .ungel) a221)
  | .id.p ↦ ¿ʔ]]
