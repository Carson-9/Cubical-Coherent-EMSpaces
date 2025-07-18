{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

module Cellular.Dependent-Path where

  compPathP-rightconst : ∀ {ℓ} (A : I → Type ℓ) {x : A i0} {y : A i1} {z : A i1} → PathP A x y → y ≡ z → PathP A x z
  compPathP-rightconst  A {x = x} p q i =
    hcomp
      (λ { j (i = i0) → x
         ; j (i = i1) → q j})
      (p i)

  compPathP-rightconst-filler : ∀ {ℓ} (A : I → Type ℓ) {x : A i0} {y : A i1} {z : A i1} 
    (p : PathP A x y) (q : y ≡ z) → PathP (λ i → PathP A x (q i)) p (compPathP-rightconst A p q)
  compPathP-rightconst-filler A {x = x} p q j i =
    hfill
      (λ { j (i = i0) → x
         ; j (i = i1) → q j})
      (inS (p i))
      j

  compPathP-rightconst-refl : ∀ {ℓ} (A : I → Type ℓ) {y : A i1} {z : A i1} (q : y ≡ z) 
    → (compPathP-rightconst (λ i → A i1) (refl {x = y}) q) ≡ q
  compPathP-rightconst-refl A {y = y} {z = z} q = J 
    (λ z q → (compPathP-rightconst (λ i → A i1) (refl) q) ≡ q) 
    (sym ((sym (transportRefl refl)) ∙ 
      fromPathP (compPathP-rightconst-filler (λ i → A i1) refl refl))) 
    q

  compPathP-leftconst : ∀ {ℓ} (A : I → Type ℓ) {x : A i0} {y : A i0} {z : A i1} → x ≡ y → PathP A y z → PathP A x z
  compPathP-leftconst A {z = z} p q i =
    hcomp
      (λ { j (i = i0) → (sym p) j
         ; j (i = i1) → z})
      (q i)
 
  compPathP-leftconst-filler : ∀ {ℓ} (A : I → Type ℓ) {x : A i0} {y : A i0} {z : A i1} 
    (p : x ≡ y) (q : PathP A y z) → PathP (λ i → PathP A (p (~ i)) z) q (compPathP-leftconst A p q)
  compPathP-leftconst-filler A {z = z} p q j i =
    hfill
      (λ { j (i = i0) → (sym p) j
         ; j (i = i1) → z})
      (inS (q i))
      j



  compPathP'-rightconst : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {x y : A} {p : x ≡ y}
    {x' : B x} {y' : B y} {z' : B y} → PathP (λ i → B (p i)) x' y' → y' ≡ z' → PathP (λ i → B (p i)) x' z'
  compPathP'-rightconst  {B = B} {x = x} {y = y} {p = p} {x' = x'} {y' = y'} {z' = z'} p' q' i =
    hcomp
      (λ { j (i = i0) → x'
         ; j (i = i1) → q' j})
      (p' i)

  compPathP'-rightconst-filler : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {x y : A} {p : x ≡ y}
    {x' : B x} {y' : B y} {z' : B y} (p' : PathP (λ i → B (p i)) x' y') (q' : y' ≡ z') 
    → PathP (λ i → PathP (λ i → B (p i)) x' (q' i)) p' (compPathP'-rightconst {B = B} p' q')
  compPathP'-rightconst-filler {B = B} {x = x} {y = y} {p = p} {x' = x'} {y' = y'} {z' = z'} p' q' j i =
    hfill
      (λ { j (i = i0) → x'
         ; j (i = i1) → q' j})
      (inS (p' i))
      j


  compPathP'-rightconst-refl : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {y : A}
    {y' : B y} {z' : B y} (q' : y' ≡ z') 
    → (compPathP'-rightconst {B = B} (refl {x = y'}) q') ≡ q'
  compPathP'-rightconst-refl {B = B} {y' = y'} {z' = z'} q' = J 
    (λ z q → (compPathP'-rightconst {B = B} (refl) q) ≡ q) 
    (sym ((sym (transportRefl refl)) ∙ 
      fromPathP (compPathP'-rightconst-filler {B = B} refl refl))) 
    q'


  compPathP'-leftconst : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {x y : A} {p : x ≡ y}
    {x' : B x} {y' : B x} {z' : B y} → x' ≡ y' → PathP (λ i → B (p i)) y' z' → PathP (λ i → B (p i)) x' z'
  compPathP'-leftconst {B = B} {x = x} {y = y} {p = p} {x' = x'} {y' = y'} {z' = z'} p' q' i =
    hcomp
      (λ { j (i = i0) → (sym p') j
         ; j (i = i1) → z'})
      (q' i)

 
  compPathP'-leftconst-filler : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {x y : A} {p : x ≡ y}
    {x' : B x} {y' : B x} {z' : B y} (p' : x' ≡ y') (q' : PathP (λ i → B (p i)) y' z')
    → PathP (λ i → PathP (λ i → B (p i)) (p' (~ i)) z') q' (compPathP'-leftconst {B = B} p' q')
  compPathP'-leftconst-filler {B = B} {x = x} {y = y} {p = p} {x' = x'} {y' = y'} {z' = z'} p' q' j i =
    hfill
      (λ { j (i = i0) → (sym p') j
         ; j (i = i1) → z'})
      (inS (q' i))
      j


  compPathP'-leftconst-refl : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {y : A}
    {x' : B y} {y' : B y} (p' : x' ≡ y') 
    → (compPathP'-leftconst {B = B} p' (refl {x = y'})) ≡ p'
  compPathP'-leftconst-refl {B = B} {x' = x'} {y' = y'} p' = J 
    (λ z p → (compPathP'-leftconst {B = B} p (refl)) ≡ p) 
    (sym ((sym (transportRefl refl)) ∙ 
      fromPathP (compPathP'-leftconst-filler {B = B} refl refl))) 
    p'

  postulate
    compPathP'-leftconst-reflconst : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {y z : A} {q : y ≡ z}
      {y' : B y} {z' : B z} (q' : PathP (λ i → B (q i)) y' z') 
      → (compPathP'-leftconst {B = B} (refl {x = y'}) q') ≡ q'
  -- compPathP'-leftconst-reflconst {B = B} {y' = y'} {z' = z'} q' =
  --  -- /!\ rUnitP' only gives a PathP, and not a non-dependent equality 
  --   {! JDep ? ? ?  !}


  -- Dependent composition on non-dependent paths is simple composition



  -- Replace a point

  PathP-replace-beginning : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} {a' : A i0} {b : A i1}
    (original-path : PathP A a b)
    (path-between-start : a ≡ a')
    → PathP A a' b

  PathP-replace-beginning {A = A} {a = a} {a' = a'} {b = b} original-path eq = 
    compPathP-leftconst A (sym eq) original-path

  PathP-replace-end : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} {b : A i1} {b' : A i1}
    (original-path : PathP A a b)
    (path-between-start : b ≡ b')
    → PathP A a b'

  PathP-replace-end {A = A} {a = a} {b = b} {b' = b'} original-path eq = 
    compPathP-rightconst A original-path eq
     


    -- Double Composition, similar to _∙∙_∙∙_ for regular paths

  infixr 40 ⟨_⟩_∙∙_∙∙_

  dep-doublecomp : {ℓ : Level} (A : I → I → Type ℓ) {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
    (left-path : PathP (λ j → A i0 (~ j)) a₀₁ a₀₀)
    (bot-path : PathP (λ i → A i i0) a₀₀ a₁₀)
    (right-path : PathP (λ j → A i1 j) a₁₀ a₁₁)
    → PathP (λ i → A i i1) a₀₁ a₁₁
  dep-doublecomp A left-path bot-path right-path = transport (λ j → PathP (λ i → A i j) (left-path (~ j)) (right-path j)) bot-path

  dep-doublecomp' : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} {a₀₀ a₁₀ a₀₁ a₁₁ : A} 
    {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁} 
    {la : a₀₀ ≡ a₀₁} {ba : a₀₀ ≡ a₁₀} {ra : a₁₀ ≡ a₁₁} 
    (left-path : PathP (λ j → B (la (~ j))) b₀₁ b₀₀)
    (bot-path : PathP (λ i → B (ba i)) b₀₀ b₁₀)
    (right-path : PathP (λ j → B (ra j)) b₁₀ b₁₁)
    → PathP (λ i → B (((sym la) ∙∙ ba ∙∙ ra) i)) b₀₁ b₁₁
  dep-doublecomp' {B = B} {la = la} {ba = ba} {ra = ra} left-path bot-path right-path = 
    transport 
      (λ j → PathP (λ i → B ((doubleCompPath-filler (sym la) ba ra) j i)) (left-path (~ j)) (right-path j)) 
      bot-path


  ⟨_⟩_∙∙_∙∙_ : {ℓ : Level} (A : I → I → Type ℓ) {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
      (left-path : PathP (λ j → A i0 (~ j)) a₀₁ a₀₀)
      (bot-path : PathP (λ i → A i i0) a₀₀ a₁₀)
      (right-path : PathP (λ j → A i1 j) a₁₀ a₁₁)
      → PathP (λ i → A i i1) a₀₁ a₁₁
  ⟨ A ⟩ left-path ∙∙ bot-path ∙∙ right-path = dep-doublecomp A left-path bot-path right-path

  dep-doublecomp-filler : {ℓ : Level} (A : I → I → Type ℓ) {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
      (left-path : PathP (λ j → A i0 (~ j)) a₀₁ a₀₀)
      (bot-path : PathP (λ i → A i i0) a₀₀ a₁₀)
      (right-path : PathP (λ j → A i1 j) a₁₀ a₁₁)
      → PathP (λ j → PathP (λ i → A i j) (left-path (~ j)) (right-path j)) bot-path (dep-doublecomp {ℓ = ℓ} A left-path bot-path right-path)
  dep-doublecomp-filler A left bot right = transport-filler (λ j → PathP (λ i → A i j) (left (~ j)) (right j)) bot

  dep-doublecomp'-filler : {ℓ : Level} {A : Type ℓ} {B : A → Type ℓ} {a₀₀ a₁₀ a₀₁ a₁₁ : A} 
    {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁} 
    {la : a₀₁ ≡ a₀₀} {ba : a₀₀ ≡ a₁₀} {ra : a₁₀ ≡ a₁₁} 
    (left-path : PathP (λ j → B (la j)) b₀₁ b₀₀)
    (bot-path : PathP (λ i → B (ba i)) b₀₀ b₁₀)
    (right-path : PathP (λ j → B (ra j)) b₁₀ b₁₁)
    → PathP (λ j → PathP (λ i → B ((doubleCompPath-filler la ba ra) j i)) (left-path (~ j)) (right-path j)) bot-path (dep-doublecomp' {B = B} left-path bot-path right-path)
  dep-doublecomp'-filler {A = A} {B = B} {la = la} {ba = ba} {ra = ra}  left bot right = 
    transport-filler (λ j → PathP (λ i → B ((doubleCompPath-filler la ba ra) j i)) (left (~ j)) (right j)) bot


  dep-doublecomp-identify-bottom :  {ℓ : Level} (A : I → I → Type ℓ) {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
      (left-path : PathP (λ j → A i0 (~ j)) a₀₁ a₀₀)
      (bot-path : PathP (λ i → A i i0) a₀₀ a₁₀)
      (right-path : PathP (λ j → A i1 j) a₁₀ a₁₁)
      (other-bot : PathP (λ i → A i i0) a₀₀ a₁₀) (eq : bot-path ≡ other-bot)
      → dep-doublecomp A left-path bot-path right-path ≡ dep-doublecomp A left-path other-bot right-path

  dep-doublecomp-identify-bottom A left bot right other eq = 
    cong (λ t → transport (λ j → PathP (λ i → A i j) (left (~ j)) (right j)) t) eq

  postulate
    dep-doublecomp-simplify-edge-rightconst : {ℓ : Level} (A : I → I → Type ℓ) {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} 
      {a₀₁ : A i0 i1} {a₁₁ : A i1 i1} {b₁₀ : A i1 i0} {b₁₁ : A i1 i1}
      (al : PathP (λ j → A i0 (~ j)) a₀₁ a₀₀)
      (ab : PathP (λ i → A i i0) a₀₀ a₁₀)
      (ar : PathP (λ j → A i1 j) a₁₀ a₁₁)
      (bb : PathP (λ i → A i1 i0) a₁₀ b₁₀)
      (br : PathP (λ j → A i1 j) b₁₀ b₁₁)
      → compPathP-rightconst (λ i → A i i1) (dep-doublecomp A al ab ar) (dep-doublecomp (λ i j → A i1 j) (symP ar) bb br) 
        ≡ (dep-doublecomp A al (compPathP-rightconst (λ i → A i i0) ab bb) br)

  
  constant-transport : ∀ {ℓ} {A : Type ℓ} {x : A} → transport (λ _ → A) x ≡ x 
  constant-transport {x = x} = transportRefl x
    
  postulate
    fromPathP-refl : ∀ {ℓ} {A : Type ℓ} {x : A} → (fromPathP (λ i → x)) ≡ constant-transport
    toPathP-refl :  ∀ {ℓ} {A : Type ℓ} {x : A} → (toPathP (constant-transport {A = A} {x = x})) ≡ (λ _ → x)

  transport-filler-refl : ∀ {ℓ} {A : Type ℓ} {x : A} → transport-filler (λ _ → A) x ≡ (sym constant-transport)
  transport-filler-refl {A = A} {x = x} = (
      (transport-filler (λ _ → A) x)    ≡⟨ refl ⟩
      (λ i → transp (λ j → A) (~ i) x)  ≡⟨ refl ⟩
      sym (λ i → transp (λ _ → A) i x)  ≡⟨ cong sym refl ⟩
      sym constant-transport ∎)


  rCancelP' :
    ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ')
    {x y : A} {p : x ≡ y} {z : B x} {w : B y}
    (q : PathP (λ i → B (p i)) z w)
    → PathP (λ j → PathP (λ i → B (rCancel p j i)) z z) (compPathP' {B = B} q (symP q)) refl
  rCancelP' = {!!}

  lCancelP' :
    ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ}
    {x y : A} {p : x ≡ y} {z : B x} {w : B y} 
    (p' : PathP (λ i → B (p i)) z w) →
    PathP (λ j → PathP (λ i → B (lCancel p j i)) w w) (compPathP' {B = B} (symP p') p') refl
  lCancelP' {B = B} {p = p} p' =
    JDep
    (λ _ p w p' → PathP (λ j → PathP (λ i → B (lCancel p j i)) w w) (compPathP' {B = B} (symP p') p') refl)
    {!!}
    p
    p'


  



  -- Trucs

    -- thm :
    -- ∀ {ℓ} {A : Type ℓ} (B : A → Type ℓ)
    -- {x y z : A} (p : x ≡ y) (q : y ≡ z)
    -- (f g h : (x : A) → B x)
    -- (P : PathP ? f g) (Q : PathP ? g h) →
  
  -- TODO: variante de compPath→Square
  comp-to-square : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) → p ∙ p ≡ refl → Square p refl refl p
  comp-to-square = {!!}
  
  bla :
    ∀ {ℓ} {A : Type ℓ} (B : A → Type ℓ)
    {x : A} (p : x ≡ x) (α : p ∙ p ≡ refl) {X : B x} (P : PathP (λ i → B (p i)) X X) →
    PathP (λ j → PathP (λ i → B (α j i)) X X) (compPathP' {B = B} P P) (refl {x = X}) →
    SquareP (λ i j → B (comp-to-square p α i j)) P refl refl P
  bla B p α P coh = toPathP {!substInPathsR ? ?!}
