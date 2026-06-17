{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

axiom A00 : Type
axiom A01 : Type
axiom A10 : Type
axiom A11 : Type
axiom A02 : Br Type A00 A01
axiom A12 : Br Type A10 A11
axiom A20 : Br Type A00 A10
axiom A21 : Br Type A01 A11
axiom A22 : Br (Br Type) A02 A12 A20 A21

axiom a00 : A00
axiom a01 : A01
axiom a10 : A10
axiom a11 : A11
axiom a02 : A02 a00 a01
axiom a12 : A12 a10 a11
axiom a20 : A20 a00 a10
axiom a21 : A21 a01 a11

def f (a22 : A22 a02 a12 a20 a21) : sym A22 a20 a21 a02 a12 ≔ sym a22

def g (a22 : sym A22 a20 a21 a02 a12) : A22 a02 a12 a20 a21 ≔ sym a22

def eq (X : Type) (x : X) : X → Type ≔ data [ rfl. : eq X x x ]

def fg (a22 : sym A22 a20 a21 a02 a12)
  : eq (sym A22 a20 a21 a02 a12) (f (g a22)) a22
  ≔ rfl.

def gf (a22 : A22 a02 a12 a20 a21)
  : eq (A22 a02 a12 a20 a21) (g (f a22)) a22
  ≔ rfl.

` doesn't this give an example of why we can't have Br Type A B ≅ A → B → Type?

def T (A : Type) : Type ≔ codata [ x .des.p : A.0 ]

axiom A : Type
axiom x : T A

echo rel x .des
echo rel x .des.1

def eee : eq A (rel x .des) (rel x .des.1) ≔ rfl.

echo rel (rel x) .des.1
echo rel (rel x) .des.2

def Span (A B : Type) : Type ≔ sig ( C : Type, f : C → A, g : C → B )

def toSpan (A B : Type) (R : Br Type A B) : Span A B ≔ (
  C ≔ sig (
    a : A,
    b : B,
    c : R a b ),
  f ≔ abc ↦ abc .a,
  g ≔ abc ↦ abc .b)

def Gel (A B : Type) (s : Span A B) : Br Type A B ≔ sig a b ↦ (
  ungel : sig ( c : s .C, e : eq A (s .f c) a, e' : eq B (s .g c) b ) )

def spanRound (A B : Type) (s : Span A B)
  : eq (Span A B) (toSpan A B (Gel A B s)) s
  ≔ ¿rfl.ʔ

` content of fibrancy

def isFibrant (A : Type) : Type ≔ codata [
| x .trr.p : A.0 → A.1
| x .trl.p : A.1 → A.0
| x .liftr.p : (a₀ : A.0) → A.2 a₀ (x.2 .trr a₀)
| x .liftl.p : (a₁ : A.1) → A.2 (x.2 .trl a₁) a₁
| x .id.p : (a₀ : A.0) (a₁ : A.1) → isFibrant (A.2 a₀ a₁) ]

axiom A : Type
axiom f : isFibrant A

{`
INPUT:
a₀

OUTPUT:
    a₂
a₀------a₁
 `}
def 1_line (a₀ : A) : sig ( a₁ : A, a₂ : A⁽ᵖ⁾ a₀ a₁ ) ≔ (
  f⁽ᵖ⁾ .trr a₀,
  f⁽ᵖ⁾ .liftr a₀)
{`
INPUT:
    a₀₂
a₀₀------a₀₁

OUTPUT:
       a₁₂
   a₁₀------a₁₁
    |        |
a₂₀ |  a₂₂   |a₂₁
    |        |
   a₀₀------a₀₁
       a₀₂
 `}
def 2_line (a₀₀ a₀₁ : A) (a₀₂ : A⁽ᵖ⁾ a₀₀ a₀₁)
  : sig (
      a₁₀ : A,
      a₁₁ : A,
      a₁₂ : A⁽ᵖ⁾ a₁₀ a₁₁,
      a₂₀ : A⁽ᵖ⁾ a₀₀ a₁₀,
      a₂₁ : A⁽ᵖ⁾ a₀₁ a₁₁,
      a₂₂ : A⁽ᵖᵖ⁾ a₀₂ a₁₂ a₂₀ a₂₁ )
  ≔ (
  a₁₀ ≔ f⁽ᵖ⁾ .trr a₀₀,
  a₁₁ ≔ f⁽ᵖ⁾ .trr a₀₁,
  a₁₂ ≔ f⁽ᵖᵖ⁾ .trr.1 a₀₂,
  a₂₀ ≔ f⁽ᵖ⁾ .liftr a₀₀,
  a₂₁ ≔ f⁽ᵖ⁾ .liftr a₀₁,
  a₂₂ ≔ f⁽ᵖᵖ⁾ .liftr.1 a₀₂)
  
{`
INPUT:
      
   a₁₀      a₁₁
    |        |
a₂₀ |        |a₂₁
    |        |
   a₀₀------a₀₁
       a₀₂

OUTPUT:
       a₁₂
   a₁₀------a₁₁
    |        |
a₂₀ |  a₂₂   |a₂₁
    |        |
   a₀₀------a₀₁
       a₀₂
 `}
def 2_square (a₀₀ a₀₁ : A) (a₀₂ : A⁽ᵖ⁾ a₀₀ a₀₁) (a₁₀ : A) (a₁₁ : A)
  (a₂₀ : A⁽ᵖ⁾ a₀₀ a₁₀) (a₂₁ : A⁽ᵖ⁾ a₀₁ a₁₁)
  : sig ( a₁₂ : A⁽ᵖ⁾ a₁₀ a₁₁, a₂₂ : A⁽ᵖᵖ⁾ a₀₂ a₁₂ a₂₀ a₂₁ )
  ≔ (
  a₁₂ ≔ f⁽ᵖᵖ⁾ .id.1 {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ .trr a₀₂,
  a₂₂ ≔ sym (f⁽ᵖᵖ⁾ .id.1 {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ .liftr a₀₂))

def 3_cube (a₀₀₀ a₀₀₁ : A) (a₀₀₂ : A⁽ᵖ⁾ a₀₀₀ a₀₀₁) (a₀₁₀ : A) (a₀₁₁ : A)
  (a₀₁₂ : A⁽ᵖ⁾ a₀₁₀ a₀₁₁) (a₀₂₀ : A⁽ᵖ⁾ a₀₀₀ a₀₁₀) (a₀₂₁ : A⁽ᵖ⁾ a₀₀₁ a₀₁₁)
  (a₀₂₂ : A⁽ᵖᵖ⁾ a₀₀₂ a₀₁₂ a₀₂₀ a₀₂₁) (a₁₀₀ a₁₀₁ : A)
  (a₁₀₂ : A⁽ᵖ⁾ a₁₀₀ a₁₀₁) (a₁₁₀ : A) (a₁₁₁ : A) (a₁₁₂ : A⁽ᵖ⁾ a₁₁₀ a₁₁₁)
  (a₁₂₀ : A⁽ᵖ⁾ a₁₀₀ a₁₁₀) (a₁₂₁ : A⁽ᵖ⁾ a₁₀₁ a₁₁₁)
  (a₁₂₂ : A⁽ᵖᵖ⁾ a₁₀₂ a₁₁₂ a₁₂₀ a₁₂₁) (a₂₀₀ : A⁽ᵖ⁾ a₀₀₀ a₁₀₀)
  (a₂₀₁ : A⁽ᵖ⁾ a₀₀₁ a₁₀₁) (a₂₀₂ : A⁽ᵖᵖ⁾ a₀₀₂ a₁₀₂ a₂₀₀ a₂₀₁)
  (a₂₁₀ : A⁽ᵖ⁾ a₀₁₀ a₁₁₀) (a₂₁₁ : A⁽ᵖ⁾ a₀₁₁ a₁₁₁)
  (a₂₁₂ : A⁽ᵖᵖ⁾ a₀₁₂ a₁₁₂ a₂₁₀ a₂₁₁) (a₂₂₀ : A⁽ᵖᵖ⁾ a₀₂₀ a₁₂₀ a₂₀₀ a₂₁₀)
  : sig (
      a₂₂₁ : A⁽ᵖᵖ⁾ a₀₂₁ a₁₂₁ a₂₀₁ a₂₁₁,
      a₂₂₂ : A⁽ᵖᵖᵖ⁾ a₀₂₂ a₁₂₂ a₂₀₂ a₂₁₂ a₂₂₀ a₂₂₁ )
  ≔ (
  a₂₂₁ ≔ f⁽ᵖᵖᵖ⁾ .id.1 a₀₂₂ a₁₂₂ .id.1 a₂₀₂ a₂₁₂ .trr a₂₂₀,
  a₂₂₂ ≔ f⁽ᵖᵖᵖ⁾ .id.1 a₀₂₂ a₁₂₂ .id.1 a₂₀₂ a₂₁₂ .liftr a₂₂₀)

def 3_line (a₀₀₀ a₀₀₁ : A) (a₀₀₂ : A⁽ᵖ⁾ a₀₀₀ a₀₀₁) (a₀₁₀ : A) (a₀₁₁ : A)
  (a₀₁₂ : A⁽ᵖ⁾ a₀₁₀ a₀₁₁) (a₀₂₀ : A⁽ᵖ⁾ a₀₀₀ a₀₁₀) (a₀₂₁ : A⁽ᵖ⁾ a₀₀₁ a₀₁₁)
  (a₀₂₂ : A⁽ᵖᵖ⁾ a₀₀₂ a₀₁₂ a₀₂₀ a₀₂₁)
  : sig (
      a₁₀₀ : A,
      a₁₀₁ : A,
      a₁₀₂ : A⁽ᵖ⁾ a₁₀₀ a₁₀₁,
      a₁₁₀ : A,
      a₁₁₁ : A,
      a₁₁₂ : A⁽ᵖ⁾ a₁₁₀ a₁₁₁,
      a₁₂₀ : A⁽ᵖ⁾ a₁₀₀ a₁₁₀,
      a₁₂₁ : A⁽ᵖ⁾ a₁₀₁ a₁₁₁,
      a₁₂₂ : A⁽ᵖᵖ⁾ a₁₀₂ a₁₁₂ a₁₂₀ a₁₂₁,
      a₂₀₀ : A⁽ᵖ⁾ a₀₀₀ a₁₀₀,
      a₂₀₁ : A⁽ᵖ⁾ a₀₀₁ a₁₀₁,
      a₂₀₂ : A⁽ᵖᵖ⁾ a₀₀₂ a₁₀₂ a₂₀₀ a₂₀₁,
      a₂₁₀ : A⁽ᵖ⁾ a₀₁₀ a₁₁₀,
      a₂₁₁ : A⁽ᵖ⁾ a₀₁₁ a₁₁₁,
      a₂₁₂ : A⁽ᵖᵖ⁾ a₀₁₂ a₁₁₂ a₂₁₀ a₂₁₁,
      a₂₂₀ : A⁽ᵖᵖ⁾ a₀₂₀ a₁₂₀ a₂₀₀ a₂₁₀,
      a₂₂₁ : A⁽ᵖᵖ⁾ a₀₂₁ a₁₂₁ a₂₀₁ a₂₁₁,
      a₂₂₂ : A⁽ᵖᵖᵖ⁾ a₀₂₂ a₁₂₂ a₂₀₂ a₂₁₂ a₂₂₀ a₂₂₁ )
  ≔
  let a₁₀₀ ≔ 1_line a₀₀₀ .a₁ in
  let a₁₀₁ ≔ 1_line a₀₀₁ .a₁ in
  let a₁₁₀ ≔ f⁽ᵖ⁾ .trr a₀₁₀ in
  let a₁₁₁ ≔ f⁽ᵖ⁾ .trr a₀₁₁ in
  let a₂₀₀ ≔ 1_line a₀₀₀ .a₂ in
  let a₂₀₁ ≔ 1_line a₀₀₁ .a₂ in
  let a₂₀₁ ≔ 1_line a₀₀₁ .a₂ in
  let a₂₁₀ ≔ 1_line a₀₁₀ .a₂ in
  let a₂₁₁ ≔ 1_line a₀₁₁ .a₂ in
  let a₁₀₂ ≔ 2_square a₀₀₀ a₀₀₁ a₀₀₂ a₁₀₀ a₁₀₁ a₂₀₀ a₂₀₁ .a₁₂ in
  let a₁₁₂ ≔ 2_square a₀₁₀ a₀₁₁ a₀₁₂ a₁₁₀ a₁₁₁ a₂₁₀ a₂₁₁ .a₁₂ in
  let a₁₂₀ ≔ 2_square a₀₀₀ a₀₁₀ a₀₂₀ a₁₀₀ a₁₁₀ a₂₀₀ a₂₁₀ .a₁₂ in
  let a₁₂₁ ≔ 2_square a₀₀₁ a₀₁₁ a₀₂₁ a₁₀₁ a₁₁₁ a₂₀₁ a₂₁₁ .a₁₂ in
  let a₂₀₂ ≔ 2_square a₀₀₀ a₀₀₁ a₀₀₂ a₁₀₀ a₁₀₁ a₂₀₀ a₂₀₁ .a₂₂ in
  let a₂₁₂ ≔ 2_square a₀₁₀ a₀₁₁ a₀₁₂ a₁₁₀ a₁₁₁ a₂₁₀ a₂₁₁ .a₂₂ in
  let a₂₂₀ ≔ 2_square a₀₀₀ a₀₁₀ a₀₂₀ a₁₀₀ a₁₁₀ a₂₀₀ a₂₁₀ .a₂₂ in
  let a₂₂₁ ≔ 2_square a₀₀₁ a₀₁₁ a₀₂₁ a₁₀₁ a₁₁₁ a₂₀₁ a₂₁₁ .a₂₂ in

  (a₁₀₀ ≔ a₁₀₀,
   a₁₀₁ ≔ a₁₀₁,
   a₁₀₂ ≔ a₁₀₂,
   a₁₁₀ ≔ a₁₁₀,
   a₁₁₁ ≔ a₁₁₁,
   a₁₁₂ ≔ a₁₁₂,
   a₁₂₀ ≔ a₁₂₀,
   a₁₂₁ ≔ a₁₂₁,
   a₁₂₂ ≔ ¿3_cube a₀₀₀ a₀₀₁ a₀₀₂ a₀₁₀ a₀₁₁ a₀₁₂ a₀₂₀ a₀₂₁ a₀₂₂ a₁₀₀ a₁₀₁ a₁₀₂ a₁₁₀ a₁₁₁ a₁₁₂ a₁₂₀ a₁₂₁ ʔ,
   a₂₀₀ ≔ a₂₀₀,
   a₂₀₁ ≔ a₂₀₁,
   a₂₀₂ ≔ a₂₀₂,
   a₂₁₀ ≔ a₂₁₀,
   a₂₁₁ ≔ a₂₁₁,
   a₂₁₂ ≔ a₂₁₂,
   a₂₂₀ ≔ a₂₂₀,
   a₂₂₁ ≔ a₂₂₁,
   a₂₂₂ ≔ ¿ʔ)
