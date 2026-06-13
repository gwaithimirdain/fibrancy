{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"

section single ≔

  {` In the simplest higher coinductive type √, the type we take a √ of has to be global, not a parameter, since then it would get degenerated when defining the type of the destructor.  This is the syntactic analogue of the fact that √ is not a fibered functor. `}

  axiom A : Type
  axiom 𝕗A : isFibrant A

  {` We can, however, include another non-higher destructor that depends on parameters. `}
  def √A× (B : Type) : Type ≔ codata [ x .root.p : A | x .else : B ]

  def eq√A× (B0 B1 : Type) (B2 : eq Type B0 B1) (x0 : √A× B0) (x1 : √A× B1)
    : Type
    ≔ codata [
  | z .root.p : eq A (x0.2 .root) (x1.2 .root)
  | z .else : eqd Type (X ↦ X) B0 B1 B2 (x0 .else) (x1 .else) ]

  axiom √A×_ext (B : Type) (x0 : √A× B) (x1 : √A× B)
    (x2 : eq√A× B B rfl. x0 x1)
    : eq (√A× B) x0 x1

  {` The Id-types of a √ are another √.  Unfortunately, since the higher output A has to be global, we can't define a sufficiently general form of √ for this to be simply an instance of it.  So we define it as its own type. `}
  def √IdA× (B0 B1 : Type) (B2 : Br Type B0 B1) (x0 : √A× B0) (x1 : √A× B1)
    : Type
    ≔ codata [
  | z .root.p : Br A (x0.2 .root) (x1.2 .root)
  | z .root1 : A
  | z .else : B2 (x0 .else) (x1 .else) ]

  {` To prove this, we need extensionality axioms for both √IdA× and √A×⁽ᵖ⁾.  The two look almost exactly the same, involving another higher coinductive type of eq-bisimulations. `}

  def eq√IdA× (B00 B01 : Type) (B02 : eq Type B00 B01) (B10 B11 : Type)
    (B12 : eq Type B10 B11) (B20 : Br Type B00 B10) (B21 : Br Type B01 B11)
    (B22 : eq2d Type Type (X Y ↦ Br Type X Y) B00 B01 B02 B10 B11 B12 B20
             B21) (x00 : √A× B00) (x01 : √A× B01)
    (x02 : eqd Type √A× B00 B01 B02 x00 x01) (x10 : √A× B10)
    (x11 : √A× B11) (x12 : eqd Type √A× B10 B11 B12 x10 x11)
    (x20 : √IdA× B00 B10 B20 x00 x10) (x21 : √IdA× B01 B11 B21 x01 x11)
    : Type
    ≔ codata [
  | z .root.p
    : eq2d A A (x y ↦ Br A x y) (x00.2 .root) (x01.2 .root)
        (eq.ap2121 Type Type (X Y ↦ Br Type X Y) √A× √A×
           (X0 X1 X2 x0 x1 ↦ √A×⁽ᵖ⁾ X2 x0 x1) A
           (X0 X1 X2 x0 x1 x2 ↦ x2 .root) B00.0 B01.0 B02.0 B00.1 B01.1
           B02.1 B00.2 B01.2 (match B02.2 [ rfl. ⤇ rfl. ]) x00.0 x01.0
           x02.0 x00.1 x01.1 x02.1 x00.2 x01.2
           (match B02.2, x02.2 [ rfl., rfl. ⤇ rfl. ])) (x10.2 .root)
        (x11.2 .root)
        (eq.ap2121 Type Type (X Y ↦ Br Type X Y) √A× √A×
           (X0 X1 X2 x0 x1 ↦ √A×⁽ᵖ⁾ X2 x0 x1) A
           (X0 X1 X2 x0 x1 x2 ↦ x2 .root) B10.0 B11.0 B12.0 B10.1 B11.1
           B12.1 B10.2 B11.2 (match B12.2 [ rfl. ⤇ rfl. ]) x10.0 x11.0
           x12.0 x10.1 x11.1 x12.1 x10.2 x11.2
           (match B12.2, x12.2 [ rfl., rfl. ⤇ rfl. ])) (x20.2 .root)
        (x21.2 .root)
  | z .root1 : eq A (x20 .root1) (x21 .root1)
  | z .else
    : eqd Type (X ↦ X) (B20 (x00 .else) (x10 .else))
        (B21 (x01 .else) (x11 .else))
        (eq.ap212 Type Type (X Y ↦ Type⁽ᵖ⁾ X Y) (X ↦ X) (X ↦ X) Type
           (X0 X1 X2 x0 x1 ↦ X2 x0 x1) B00 B01 B02 B10 B11 B12 B20 B21 B22
           (x00 .else) (x01 .else)
           (eq.ap1d Type √A× (X ↦ X) (B u ↦ u .else) B00 B01 B02 x00 x01
              x02) (x10 .else) (x11 .else)
           (eq.ap1d Type √A× (X ↦ X) (B u ↦ u .else) B10 B11 B12 x10 x11
              x12)) (x20 .else) (x21 .else) ]

  axiom √IdA×_ext (B0 B1 : Type) (B2 : Br Type B0 B1) (x0 : √A× B0)
    (x1 : √A× B1) (x20 x21 : √IdA× B0 B1 B2 x0 x1)
    (x22 : eq√IdA× B0 B0 rfl. B1 B1 rfl. B2 B2 rfl. x0 x0 rfl. x1 x1 rfl.
             x20 x21)
    : eq (√IdA× B0 B1 B2 x0 x1) x20 x21

  def eq√A×ᵖ (B00 B01 : Type) (B02 : eq Type B00 B01) (B10 B11 : Type)
    (B12 : eq Type B10 B11) (B20 : Br Type B00 B10) (B21 : Br Type B01 B11)
    (B22 : eq2d Type Type (X Y ↦ Br Type X Y) B00 B01 B02 B10 B11 B12 B20
             B21) (x00 : √A× B00) (x01 : √A× B01)
    (x02 : eqd Type √A× B00 B01 B02 x00 x01) (x10 : √A× B10)
    (x11 : √A× B11) (x12 : eqd Type √A× B10 B11 B12 x10 x11)
    (x20 : √A×⁽ᵖ⁾ B20 x00 x10) (x21 : √A×⁽ᵖ⁾ B21 x01 x11)
    : Type
    ≔ codata [
  | z .root.p
    : eq2d A A (x y ↦ Br A x y) (x00.2 .root) (x01.2 .root)
        (eq.ap2121 Type Type (X Y ↦ Br Type X Y) √A× √A×
           (X0 X1 X2 x0 x1 ↦ √A×⁽ᵖ⁾ X2 x0 x1) A
           (X0 X1 X2 x0 x1 x2 ↦ x2 .root) B00.0 B01.0 B02.0 B00.1 B01.1
           B02.1 B00.2 B01.2 (match B02.2 [ rfl. ⤇ rfl. ]) x00.0 x01.0
           x02.0 x00.1 x01.1 x02.1 x00.2 x01.2
           (match B02.2, x02.2 [ rfl., rfl. ⤇ rfl. ])) (x10.2 .root)
        (x11.2 .root)
        (eq.ap2121 Type Type (X Y ↦ Br Type X Y) √A× √A×
           (X0 X1 X2 x0 x1 ↦ √A×⁽ᵖ⁾ X2 x0 x1) A
           (X0 X1 X2 x0 x1 x2 ↦ x2 .root) B10.0 B11.0 B12.0 B10.1 B11.1
           B12.1 B10.2 B11.2 (match B12.2 [ rfl. ⤇ rfl. ]) x10.0 x11.0
           x12.0 x10.1 x11.1 x12.1 x10.2 x11.2
           (match B12.2, x12.2 [ rfl., rfl. ⤇ rfl. ])) (x20.2 .root.2)
        (x21.2 .root.2)
  | z .root1 : eq A (x20 .root.1) (x21 .root.1)
  | z .else
    : eqd Type (X ↦ X) (B20 (x00 .else) (x10 .else))
        (B21 (x01 .else) (x11 .else))
        (eq.ap212 Type Type (X Y ↦ Type⁽ᵖ⁾ X Y) (X ↦ X) (X ↦ X) Type
           (X0 X1 X2 x0 x1 ↦ X2 x0 x1) B00 B01 B02 B10 B11 B12 B20 B21 B22
           (x00 .else) (x01 .else)
           (eq.ap1d Type √A× (X ↦ X) (B u ↦ u .else) B00 B01 B02 x00 x01
              x02) (x10 .else) (x11 .else)
           (eq.ap1d Type √A× (X ↦ X) (B u ↦ u .else) B10 B11 B12 x10 x11
              x12)) (x20 .else) (x21 .else) ]

  axiom √A×ᵖ_ext (B0 B1 : Type) (B2 : Br Type B0 B1) (x0 : √A× B0)
    (x1 : √A× B1) (x20 x21 : √A×⁽ᵖ⁾ B2 x0 x1)
    (x22 : eq√A×ᵖ B0 B0 rfl. B1 B1 rfl. B2 B2 rfl. x0 x0 rfl. x1 x1 rfl.
             x20 x21)
    : eq (√A×⁽ᵖ⁾ B2 x0 x1) x20 x21

  {` We define both directions of the isomorphism. `}

  def id√_iso.to (B0 B1 : Type) (B2 : Br Type B0 B1) (x0 : √A× B0)
    (x1 : √A× B1)
    : √IdA× B0 B1 B2 x0 x1 → Br √A× B2 x0 x1
    ≔ (y2 ↦ [
  | .root.p ↦ y2.2 .root
  | .root.1 ↦ y2 .root1
  | .else ↦ y2 .else])

  def id√_iso.fro (B0 B1 : Type) (B2 : Br Type B0 B1) (x0 : √A× B0)
    (x1 : √A× B1)
    : Br √A× B2 x0 x1 → √IdA× B0 B1 B2 x0 x1
    ≔ (x2 ↦ [
  | .root.p ↦ x2.2 .root.2
  | .root1 ↦ x2 .root
  | .else ↦ x2 .else])

  {` And put them together. `}

  def id√_iso (B0 B1 : Type) (B2 : Br Type B0 B1) (x0 : √A× B0)
    (x1 : √A× B1)
    : √IdA× B0 B1 B2 x0 x1 ≅ Br √A× B2 x0 x1
    ≔ adjointify (√IdA× B0 B1 B2 x0 x1) (Br √A× B2 x0 x1)
        (id√_iso.to B0 B1 B2 x0 x1) (id√_iso.fro B0 B1 B2 x0 x1)
        (y2 ↦
         √IdA×_ext B0 B1 B2 x0 x1
           (id√_iso.fro B0 B1 B2 x0 x1 (id√_iso.to B0 B1 B2 x0 x1 y2)) y2
           [ .root.p ↦ rfl. | .root1 ↦ rfl. | .else ↦ rfl. ])
        (x2 ↦
         √A×ᵖ_ext B0 B1 B2 x0 x1
           (id√_iso.to B0 B1 B2 x0 x1 (id√_iso.fro B0 B1 B2 x0 x1 x2)) x2
           [ .root.p ↦ rfl. | .root1 ↦ rfl. | .else ↦ rfl. ])

  {` Now we can prove fibrancy of √A×, except for the recursive case that would be fibrancy of Id√A×, since the latter can't be an instance of the former. `}
  def 𝕗√A× (B : Type) (𝕗B : isFibrant B) : isFibrant (√A× B) ≔ [
  | .trr.p ↦ x0 ↦ [ .root.p ↦ x0.2 .root | .else ↦ 𝕗B.2 .trr (x0 .else) ]
  | .trl.p ↦ x1 ↦ [ .root.p ↦ x1.2 .root | .else ↦ 𝕗B.2 .trl (x1 .else) ]
  | .liftr.p ↦ x0 ↦ [
    | .root.p ↦ rel x0.2 .root.1
    | .root.1 ↦ rel x0 .root
    | .else ↦ 𝕗B.2 .liftr (x0 .else)]
  | .liftl.p ↦ x1 ↦ [
    | .root.p ↦ rel x1.2 .root.1
    | .root.1 ↦ rel x1 .root
    | .else ↦ 𝕗B.2 .liftl (x1 .else)]
  | .id.p ↦ x0 x1 ↦
      𝕗eqv (√IdA× B.0 B.1 B.2 x0 x1) (Br √A× B.2 x0 x1)
        (id√_iso B.0 B.1 B.2 x0 x1) ?]

end

section parametrized ≔

  {` We can also consider higher destructors whose typse depend on the parameters, but they have to depend on a degenerated version of the parameters.  In this case, however, it seems that we require the *parameter* to be fibrant as well. `}
  axiom Γ : Type
  axiom 𝕗Γ : isFibrant Γ
  axiom A (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) : Type
  axiom 𝕗A (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) : isFibrant (A x₀ x₁ x₂)

  {` For simplicity, we leave off any lower destructors. `}
  def √A (x : Γ) : Type ≔ codata [ a .root.p : A x.0 x.1 x.2 ]

  def 𝕗√A (x : Γ) : isFibrant (√A x) ≔ [
  | .trr.p ↦ a₀ ↦ [
    | .root.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .trr (a₀.2 .root)]
  | .trl.p ↦ a₁ ↦ [
    | .root.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .trl (a₁.2 .root)]
  | .liftr.p ↦ a₀ ↦ [
    | .root.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .liftr (a₀.2 .root)
    | .root.1 ↦
      {` Here we need fibrancy of Γ, to get a connection square. `}
      rel 𝕗A (rel x.0) x.2 (coconn (Γ, 𝕗Γ) x.0 x.1 x.2) .trr (rel a₀ .root)]
  | .liftl.p ↦ a₁ ↦ [
    | .root.p ↦ rel 𝕗A x.20 x.21 (sym x.22) .liftl (a₁.2 .root)
    | .root.1 ↦
        rel 𝕗A x.2 (rel x.1) (conn (Γ, 𝕗Γ) x.0 x.1 x.2) .trl (rel a₁ .root)]
  {` Again, we can't do the recursive case. `}
  | .id.p ↦ a₀ a₁ ↦ ?]

end
