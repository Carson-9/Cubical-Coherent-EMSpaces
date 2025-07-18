{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

open import Cellular.Dependent-Path
open import coh


module Cellular.Square where

    private
        variable
            ℓ ℓ' : Level

    {-
                a₀₁ ----------- a₁₁
                 |               |
                 |               |
                 |               |
                 |               |
                 |               |
                a₀₀ ----------- a₁₀
      j ^
        |
        •--->
            i
    -}

    -- Dependent Square Shenanigans --

    -- Squares over the Interval

    SquareP-horizontal : (A : I → I → Type ℓ)
        {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
        {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
        (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
        → Type ℓ
    SquareP-horizontal A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ j → PathP (λ i → A i j) (a₀₋ j) (a₁₋ j)) a₋₀ a₋₁

    SquareP-to-horizontal : {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
        {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
        → SquareP A a₀₋ a₁₋ a₋₀ a₋₁ → SquareP-horizontal A a₀₋ a₁₋ a₋₀ a₋₁
    SquareP-to-horizontal {A = A} s i j = s j i


    SquareP-to-vertical : {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
        {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
        → SquareP-horizontal A a₀₋ a₁₋ a₋₀ a₋₁ → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
    SquareP-to-vertical {A = A} s i j = s j i

    SquareP-replace-edge-left : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
        {al : PathP (λ j → A i0 j) a₀₀ a₀₁} {ar : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {ab : PathP (λ i → A i i0) a₀₀ a₁₀} {at : PathP (λ i → A i i1) a₀₁ a₁₁}
        {bl : PathP (λ j → A i0 j) a₀₀ a₀₁}
        (a-square : SquareP A (al) (ar) (ab) (at)) (l-id : al ≡ bl)
        → SquareP A (bl) (ar) (ab) (at)

    SquareP-replace-edge-left {A = A} {al = al} {ar = ar} {ab = ab} {at = at} {bl = bl}
        a-square l-id = PathP-replace-beginning a-square l-id

    SquareP-replace-edge-right : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
        {al : PathP (λ j → A i0 j) a₀₀ a₀₁} {ar : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {ab : PathP (λ i → A i i0) a₀₀ a₁₀} {at : PathP (λ i → A i i1) a₀₁ a₁₁}
        {br : PathP (λ j → A i1 j) a₁₀ a₁₁}
        (a-square : SquareP A (al) (ar) (ab) (at)) (r-id : ar ≡ br)
        → SquareP A (al) (br) (ab) (at)

    SquareP-replace-edge-right {A = A} {al = al} {ar = ar} {ab = ab} {at = at} {br = br}
        a-square r-id = PathP-replace-end a-square r-id

    SquareP-replace-edge-bottom : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
        {al : PathP (λ j → A i0 j) a₀₀ a₀₁} {ar : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {ab : PathP (λ i → A i i0) a₀₀ a₁₀} {at : PathP (λ i → A i i1) a₀₁ a₁₁}
        {bb : PathP (λ i → A i i0) a₀₀ a₁₀}
        (a-square : SquareP A (al) (ar) (ab) (at)) (b-id : ab ≡ bb)
        → SquareP A (al) (ar) (bb) (at)

    SquareP-replace-edge-bottom {A = A} {al = al} {ar = ar} {ab = ab} {at = at} {bb = bb}
        a-square b-id = SquareP-to-vertical (SquareP-replace-edge-left {A = λ i j → A j i} (SquareP-to-horizontal a-square) b-id)

    SquareP-replace-edge-top : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
        {al : PathP (λ j → A i0 j) a₀₀ a₀₁} {ar : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {ab : PathP (λ i → A i i0) a₀₀ a₁₀} {at : PathP (λ i → A i i1) a₀₁ a₁₁}
        {bt : PathP (λ i → A i i1) a₀₁ a₁₁}
        (a-square : SquareP A (al) (ar) (ab) (at)) (t-id : at ≡ bt)
        → SquareP A (al) (ar) (ab) (bt)

    SquareP-replace-edge-top {A = A} {al = al} {ar = ar} {ab = ab} {at = at} {bt = bt}
        a-square t-id = SquareP-to-vertical (SquareP-replace-edge-right {A = λ i j → A j i} (SquareP-to-horizontal a-square) t-id)



    SquareP-rotate-left : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
        {al : PathP (λ j → A i0 j) a₀₀ a₀₁} {ar : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {ab : PathP (λ i → A i i0) a₀₀ a₁₀} {at : PathP (λ i → A i i1) a₀₁ a₁₁}
        (square : SquareP A (al) (ar) (ab) (at))
        → SquareP (λ i j → A j (~ i)) (at) (ab) (symP al) (symP ar)
    SquareP-rotate-left {A = A} {al = al} {ar = ar} {ab = ab} {at = at} s i j = s j (~ i)

    SquareP-rotate-right : {ℓ : Level} {A : I → I → Type ℓ} 
        {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
        {al : PathP (λ j → A i0 j) a₀₀ a₀₁} {ar : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {ab : PathP (λ i → A i i0) a₀₀ a₁₀} {at : PathP (λ i → A i i1) a₀₁ a₁₁}
        (square : SquareP A (al) (ar) (ab) (at))
        → SquareP (λ i j → A (~ j) i) (symP ab) (symP at) (ar) (al)
    SquareP-rotate-right {A = A} {al = al} {ar = ar} {ab = ab} {at = at} s i j = s (~ j) i



    SquareP-top-comp-topconst : {ℓ : Level} {A : I → I → Type ℓ} 
        {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
        {b₀₁ : A i0 i1} {b₁₁ : A i1 i1}
        {al : PathP (λ j → A i0 j) a₀₀ a₀₁} {ar : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {ab : PathP (λ i → A i i0) a₀₀ a₁₀} {at : PathP (λ i → A i i1) a₀₁ a₁₁}
        {bl : PathP (λ j → A i0 i1) a₀₁ b₀₁} {br : PathP (λ j → A i1 i1) a₁₁ b₁₁}
        {bt : PathP (λ i → A i i1) b₀₁ b₁₁}
        (bot-square : SquareP A (al) (ar) (ab) (at))
        (top-square : SquareP (λ i j → A i i1) (bl) (br) (at) (bt))
        → SquareP A (compPathP-rightconst (λ j → A i0 j) al bl) (compPathP-rightconst (λ j → A i1 j) ar br) (ab) (bt)

    SquareP-top-comp-topconst {A = A} {al = al} {ar = ar} {ab = ab} {at = at} 
        {bl = bl} {br = br} {bt = bt} 
        bot-square top-square i j = 
        (compPathP-rightconst (λ j → A i j) (bot-square i) (top-square i)) j


    SquareP-right-comp-rightconst : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
        {b₁₀ : A i1 i0} {b₁₁ : A i1 i1}
        {al : PathP (λ j → A i0 j) a₀₀ a₀₁} {ar : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {ab : PathP (λ i → A i i0) a₀₀ a₁₀} {at : PathP (λ i → A i i1) a₀₁ a₁₁} 
        {br : PathP (λ j → A i1 j) b₁₀ b₁₁}
        {bb : PathP (λ i → A i1 i0) a₁₀ b₁₀} {bt : PathP (λ i → A i1 i1) a₁₁ b₁₁}
        (left-square : SquareP A (al) (ar) (ab) (at))
        (right-square : SquareP (λ i j → A i1 j) (ar) (br) (bb) (bt))
        → SquareP A (al) (br) (compPathP-rightconst (λ i → A i i0) ab bb) (compPathP-rightconst (λ i → A i i1) at bt)


    SquareP-right-comp-rightconst {A = A} {a₀₀ = a₀₀} {a₀₁ = a₀₁} {b₁₀ = b₁₀} {b₁₁ = b₁₁} 
        {al = al} {ar = ar} {ab = ab} {at = at} {br = br} {bb = bb} {bt = bt} 
        left-square right-square = (SquareP-to-vertical {A = A} total-square) where
                
                horizontal-left : SquareP-horizontal A (al) (ar) (ab) (at)
                horizontal-left = SquareP-to-horizontal {A = A} left-square

                horizontal-right : SquareP-horizontal (λ i j → A i1 j) (ar) (br) (bb) (bt)
                horizontal-right = SquareP-to-horizontal {A = (λ i j → A i1 j)} right-square

                total-square : SquareP-horizontal A (al) (br) (compPathP-rightconst (λ i → A i i0) ab bb) (compPathP-rightconst (λ i → A i i1) at bt)
                total-square i j = (compPathP-rightconst (λ j → A j i) (horizontal-left i) (horizontal-right i)) j


    -- Convert to SquareP

    toSquareP : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
        (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
        (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
        (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀)
        (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
        → (glue : (dep-doublecomp A (symP a₀₋) (a₋₀) (a₁₋)) ≡ (a₋₁))
        → SquareP A (a₀₋) (a₁₋) (a₋₀) (a₋₁)

    toSquareP {A = A} {a₀₀ = a₀₀} {a₀₁ = a₀₁} {a₁₀ = a₁₀} {a₁₁ = a₁₁} a₀₋ a₁₋ a₋₀ a₋₁ glue =
        SquareP-replace-edge-top 
            (SquareP-to-vertical (dep-doublecomp-filler A (symP a₀₋) a₋₀ a₁₋))
            glue



    -- Trop puissant, c'est faux
    {-
    toSquareP-comp : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
        (a₀₋ : transport (λ j → A i0 j) a₀₀ ≡ a₀₁)
        (a₁₋ : transport (λ j → A i1 j) a₁₀ ≡ a₁₁)
        (a₋₀ : transport (λ i → A i i0) a₀₀ ≡ a₁₀)
        (a₋₁ : transport (λ i → A i i1) a₀₁ ≡ a₁₁)
        (glue : 
            transport (λ j → A i1 j) (transport (λ i → A i i0) a₀₀) ≡ 
            transport (λ i → A i i1) (transport (λ j → A i0 j) a₀₀))
        → SquareP A (toPathP a₀₋) (toPathP a₁₋) (toPathP a₋₀) (toPathP a₋₁)

    toSquareP-comp {A = A} {a₀₀ = a₀₀} {a₀₁ = a₀₁} {a₁₀ = a₁₀} {a₁₁ = a₁₁} a₀₋ a₁₋ a₋₀ a₋₁ glue =
        toSquareP (toPathP a₀₋) (toPathP a₁₋) (toPathP a₋₀) (toPathP a₋₁) {! toPathP glue   !}

        -- transport (i -> toPathP a0- i = toPathP a1- i) toPathP a-0 = toPathP a-1
    -}

   {-  toSquareP-compP : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
        (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
        (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
        (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀)
        (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
        -- (glue : PathP (λ i → PathP (λ j → ((λ k → A (k ∨ i) (k ∧ i) ) ∙ (λ k → A (k ∨ (~ i)) (k ∧ (~ i)))) j) a₀₀ a₁₁) 
            -- (compPathP a₋₀ a₁₋) (compPathP a₀₋ a₋₁))
        (glue : ?)
        → SquareP A a₀₋ a₁₋ a₋₀ a₋₁

    toSquareP-compP a₀₋ a₁₋ a₋₀ a₋₁ glue = ? -}

    -- Regular Squares

    Square-horizontal : {A : Type ℓ} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
        (a₀₋ : a₀₀ ≡ a₀₁) (a₁₋ : a₁₀ ≡ a₁₁) (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
        → Type ℓ
    Square-horizontal a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ j → a₀₋ j ≡ a₁₋ j) a₋₀ a₋₁

    Square-to-horizontal : {A : Type ℓ} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
        → Square a₀₋ a₁₋ a₋₀ a₋₁ → Square-horizontal a₀₋ a₁₋ a₋₀ a₋₁
    Square-to-horizontal s i j = s j i

    Square-to-vertical : {A : Type ℓ} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
        → Square-horizontal a₀₋ a₁₋ a₋₀ a₋₁ → Square a₀₋ a₁₋ a₋₀ a₋₁
    Square-to-vertical s i j = s j i


    Square-comp-up : {A : Type ℓ} {abg abd amg amd ahg ahd : A}
        {Ah : ahg ≡ ahd } {Am : amg ≡ amd} {Ab : abg ≡ abd}
        {Ahg : amg ≡ ahg} {Ahd : amd ≡ ahd}
        {Abg : abg ≡ amg} {Abd : abd ≡ amd}
        (bot-square : Square Abg Abd Ab Am)
        (top-square : Square Ahg Ahd Am Ah)
        → Square (Abg ∙ Ahg) (Abd ∙ Ahd) Ab Ah

    Square-comp-up bot-square top-square = λ i → (bot-square i) ∙ (top-square i)

    Square-comp-up-botrefl : {A : Type ℓ} {amg amd ahg ahd : A}
        {Ah : ahg ≡ ahd } {Am : amg ≡ amd} {Ab : amg ≡ amd}
        {Ahg : amg ≡ ahg} {Ahd : amd ≡ ahd}
        (bot-square : Square refl refl Ab Am)
        (top-square : Square Ahg Ahd Am Ah)
        → Square Ahg Ahd Ab Ah

    Square-comp-up-botrefl {Ahg = Ahg} {Ahd = Ahd} bot-square top-square = SquareP-replace-edge-left (
        SquareP-replace-edge-right (Square-comp-up bot-square top-square) (sym (lUnit Ahd))) (sym (lUnit Ahg))

    Square-comp-up-toprefl : {A : Type ℓ} {abg abd amg amd : A}
        {Ah : amg ≡ amd } {Am : amg ≡ amd} {Ab : abg ≡ abd}
        {Abg : abg ≡ amg} {Abd : abd ≡ amd}
        (bot-square : Square Abg Abd Ab Am)
        (top-square : Square refl refl Am Ah)
        → Square Abg Abd Ab Ah

    Square-comp-up-toprefl {Abg = Abg} {Abd = Abd} bot-square top-square = SquareP-replace-edge-left (
        SquareP-replace-edge-right (Square-comp-up bot-square top-square) (sym (rUnit Abd))) (sym (rUnit Abg))

    Square-path-up-toprefl : {A : Type ℓ} {abg abd amg amd : A}
        {Ah : amg ≡ amd } {Am : amg ≡ amd} {Ab : abg ≡ abd}
        {Abg : abg ≡ amg} {Abd : abd ≡ amd}
        (bot-square : Square Abg Abd Ab Am)
        (top-square : Square refl refl Am Ah)
        → PathP (λ j → Square ((sym (rUnit Abg)) j) ((sym (rUnit Abd)) j) (Ab) (Ah))
            (Square-comp-up bot-square top-square) 
            (Square-comp-up-toprefl bot-square top-square)
    Square-path-up-toprefl bot-square top-square = {!   !}

    Square-comp-right : {A : Type ℓ} {abg abm abd ahg ahm ahd : A}
        {Ahg : ahg ≡ ahm } {Ahd : ahm ≡ ahd} 
        {Amg : abg ≡ ahg} {Amm : abm ≡ ahm} {Amd : abd ≡ ahd}
        {Abg : abg ≡ abm} {Abd : abm ≡ abd}
        (left-square : Square Amg Amm Abg Ahg)
        (right-square : Square Amm Amd Abd Ahd)
        → Square Amg Amd (Abg ∙ Abd) (Ahg ∙ Ahd)

    Square-comp-right left-square right-square = Square-to-vertical 
        (λ i → ((Square-to-horizontal left-square) i) ∙ ((Square-to-horizontal right-square) i))

    Square-comp-right-leftrefl : {A : Type ℓ} {abm abd ahm ahd : A}
        {Ahd : ahm ≡ ahd} 
        {Amg : abm ≡ ahm} {Amm : abm ≡ ahm} {Amd : abd ≡ ahd}
        {Abd : abm ≡ abd}
        (left-square : Square Amg Amm refl refl)
        (right-square : Square Amm Amd Abd Ahd)
        → Square Amg Amd Abd Ahd

    Square-comp-right-leftrefl {Ahd = Ahd} {Abd = Abd} left-square right-square = SquareP-replace-edge-bottom 
        (SquareP-replace-edge-top (Square-comp-right left-square right-square) (sym (lUnit Ahd))) (sym (lUnit Abd))

    Square-path-right-leftrefl : {A : Type ℓ} {abm abd ahm ahd : A}
        {Ahd : ahm ≡ ahd} 
        {Amg : abm ≡ ahm} {Amm : abm ≡ ahm} {Amd : abd ≡ ahd}
        {Abd : abm ≡ abd}
        (left-square : Square Amg Amm refl refl)
        (right-square : Square Amm Amd Abd Ahd)
        → PathP (λ i → Square (Amg) (Amd) ((sym (lUnit Abd)) i) ((sym (lUnit Ahd)) i)) 
            (Square-comp-right left-square right-square) 
            (Square-comp-right-leftrefl left-square right-square)
    Square-path-right-leftrefl left-square right-square = {!   !}

    Square-comp-right-rightrefl : {A : Type ℓ} {abg abm ahg ahm : A}
        {Ahg : ahg ≡ ahm }
        {Amg : abg ≡ ahg} {Amm : abm ≡ ahm} {Amd : abm ≡ ahm}
        {Abg : abg ≡ abm}
        (left-square : Square Amg Amm Abg Ahg)
        (right-square : Square Amm Amd refl refl)
        → Square Amg Amd Abg Ahg

    Square-comp-right-rightrefl {Ahg = Ahg} {Abg = Abg} left-square right-square = SquareP-replace-edge-bottom 
        (SquareP-replace-edge-top (Square-comp-right left-square right-square) (sym (rUnit Ahg))) (sym (rUnit Abg))


    Square-replace-edge-left : {A : Type ℓ} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
        {new-left : a₀₀ ≡ a₀₁}
        (square : Square a₀₋ a₁₋ a₋₀ a₋₁) (glue : a₀₋ ≡ new-left)
        → Square new-left a₁₋ a₋₀ a₋₁
    Square-replace-edge-left square glue = Square-comp-right-leftrefl (sym glue) square

    Square-replace-edge-bottom : {A : Type ℓ} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
        {new-bot : a₀₀ ≡ a₁₀}
        (square : Square a₀₋ a₁₋ a₋₀ a₋₁) (glue : a₋₀ ≡ new-bot)
        → Square a₀₋ a₁₋ new-bot a₋₁
    Square-replace-edge-bottom square glue = Square-comp-up-botrefl (Square-to-horizontal (sym glue)) square

    Square-replace-edge-top : {A : Type ℓ} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
        {new-top : a₀₁ ≡ a₁₁}
        (square : Square a₀₋ a₁₋ a₋₀ a₋₁) (glue : a₋₁ ≡ new-top)
        → Square a₀₋ a₁₋ a₋₀ new-top
    Square-replace-edge-top square glue = Square-comp-up-toprefl square (Square-to-horizontal (glue))



    -- Squares over a type family

    SquareP' : {A : Type ℓ} (B : A → Type ℓ')
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        (original-square : Square a₀₋ a₁₋ a₋₀ a₋₁)
        (b₀₋ : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁)
        (b₁₋ : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁)
        (b₋₀ : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀) 
        (b₋₁ : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁)
        → Type ℓ'
    SquareP' {A = A} B original-square b₀₋ b₁₋ b₋₀ b₋₁ =
        PathP (λ i → PathP (λ j → B (original-square i j)) (b₋₀ i) (b₋₁ i)) b₀₋ b₁₋

    
    SquareP'-horizontal : {A : Type ℓ} (B : A → Type ℓ')
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        (original-square : Square-horizontal a₀₋ a₁₋ a₋₀ a₋₁)
        (b₀₋ : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁)
        (b₁₋ : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁)
        (b₋₀ : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀) 
        (b₋₁ : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁)
        → Type ℓ' 
    SquareP'-horizontal {A = A} B original-square b₀₋ b₁₋ b₋₀ b₋₁ = 
        PathP (λ j → PathP (λ i → B (original-square j i)) (b₀₋ j) (b₁₋ j)) b₋₀ b₋₁

    SquareP'-to-horizontal : {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        {original-square : Square a₀₋ a₁₋ a₋₀ a₋₁}
        {b₀₋ : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁}
        {b₁₋ : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁}
        {b₋₀ : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀} 
        {b₋₁ : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁}
        → SquareP' B original-square b₀₋ b₁₋ b₋₀ b₋₁ 
        → SquareP'-horizontal B (Square-to-horizontal original-square) b₀₋ b₁₋ b₋₀ b₋₁
    SquareP'-to-horizontal {A = A} {B = B} s i j = s j i


    SquareP'-to-vertical : {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        {original-square : Square-horizontal a₀₋ a₁₋ a₋₀ a₋₁}
        {b₀₋ : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁}
        {b₁₋ : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁}
        {b₋₀ : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀} 
        {b₋₁ : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁}
        → SquareP'-horizontal B original-square b₀₋ b₁₋ b₋₀ b₋₁ 
        → SquareP' B (Square-to-vertical original-square) b₀₋ b₁₋ b₋₀ b₋₁
    SquareP'-to-vertical {A = A} {B = B} s i j = s j i
    
    SquareP'-compose-top : {A : Type ℓ} {B : A → Type ℓ'}
        {abg abd amg amd ahg ahd : A} 
        {bbg : B abg} {bmg : B amg} {bhg : B ahg} 
        {bbd : B abd} {bmd : B amd} {bhd : B ahd}
        {Ab : abg ≡ abd } {Am : amg ≡ amd} {Ah : ahg ≡ ahd}
        {Abg : abg ≡ amg} {Abd : abd ≡ amd}
        {Ahg : amg ≡ ahg} {Ahd : amd ≡ ahd}
        {Bb : PathP (λ i → B (Ab i)) bbg bbd} {Bm : PathP (λ i → B (Am i)) bmg bmd} 
        {Bh : PathP (λ i → B (Ah i)) bhg bhd} 
        {Bbg : PathP (λ i → B (Abg i)) bbg bmg} {Bbd : PathP (λ i → B (Abd i)) bbd bmd}
        {Bhg : PathP (λ i → B (Ahg i)) bmg bhg} {Bhd : PathP (λ i → B (Ahd i)) bmd bhd}
        {bot-a-square : Square Abg Abd Ab Am} {top-a-square : Square Ahg Ahd Am Ah}
        (bot-b-square : SquareP' B bot-a-square Bbg Bbd Bb Bm)
        (top-b-square : SquareP' B top-a-square Bhg Bhd Bm Bh)
        → SquareP' B (Square-comp-up bot-a-square top-a-square) 
            (compPathP' {B = B} Bbg Bhg) 
            (compPathP' {B = B} Bbd Bhd) 
            Bb
            Bh

    SquareP'-compose-top {A = A} {B = B} {bot-a-square = bot-a-square} {top-a-square = top-a-square} 
        bot-b-square top-b-square =  (λ i → compPathP' {B = B} {p = bot-a-square i} {q = top-a-square i}
                                            ((bot-b-square) i) 
                                            ((top-b-square) i))


    SquareP'-compose-right : {A : Type ℓ} {B : A → Type ℓ'}
        {abg abm abd ahg ahm ahd : A} 
        {bbg : B abg} {bbm : B abm} {bbd : B abd} 
        {bhg : B ahg} {bhm : B ahm} {bhd : B ahd}
        {Ahg : ahg ≡ ahm } {Ahd : ahm ≡ ahd} 
        {Amg : abg ≡ ahg} {Amm : abm ≡ ahm} {Amd : abd ≡ ahd}
        {Abg : abg ≡ abm} {Abd : abm ≡ abd}
        {Bhg : PathP (λ i → B (Ahg i)) bhg bhm } {Bhd : PathP (λ i → B (Ahd i)) bhm bhd} 
        {Bmg : PathP (λ i → B (Amg i)) bbg bhg} {Bmm : PathP (λ i → B (Amm i)) bbm bhm} {Bmd : PathP (λ i → B (Amd i)) bbd bhd}
        {Bbg : PathP (λ i → B (Abg i)) bbg bbm} {Bbd : PathP (λ i → B (Abd i)) bbm bbd}
        {left-a-square : Square Amg Amm Abg Ahg} {right-a-square : Square Amm Amd Abd Ahd}
        (left-b-square : SquareP' B left-a-square Bmg Bmm Bbg Bhg)
        (right-b-square : SquareP' B right-a-square Bmm Bmd Bbd Bhd)
        → SquareP' B (Square-comp-right left-a-square right-a-square) 
            Bmg 
            Bmd 
            (compPathP' {B = B} Bbg Bbd)
            (compPathP' {B = B} Bhg Bhd)

    SquareP'-compose-right {A = A} {B = B} {left-a-square = left-a-square} {right-a-square = right-a-square}
        left-b-square right-b-square = SquareP'-to-vertical {A = A} {B = B}
                (λ j → compPathP' {B = B} 
                    {p = (Square-to-horizontal left-a-square) j} 
                    {q = (Square-to-horizontal right-a-square) j}
                    ((SquareP'-to-horizontal {B = B} left-b-square) j) 
                    ((SquareP'-to-horizontal {B = B} right-b-square) j))


    SquareP'-replace-base-square : {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        {original-square : Square a₀₋ a₁₋ a₋₀ a₋₁}
        {bl : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁}
        {br : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁}
        {bb : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀} 
        {bt : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁}
        {new-base-square : Square a₀₋ a₁₋ a₋₀ a₋₁}
        (square : SquareP' B original-square bl br bb bt) (id : original-square ≡ new-base-square)
        → SquareP' B new-base-square bl br bb bt

    SquareP'-replace-base-square {B = B} {bl = bl}{br = br} {bb = bb} {bt = bt} square id = 
        transport (λ k → PathP (λ i → PathP (λ j → B (id k i j)) (bb i) (bt i)) bl br) square 
   
    SquareP'-replace-edge-left-constant : {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        {original-square : Square a₀₋ a₁₋ a₋₀ a₋₁}
        {bl : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁}
        {br : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁}
        {bb : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀} 
        {bt : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁}
        {new-b : PathP (λ j → B (a₀₋ j)) b₀₀ b₀₁}
        (square : SquareP' B original-square bl br bb bt) (id : new-b ≡ bl)
        → SquareP' B original-square (new-b) (br) (bb) (bt)

    SquareP'-replace-edge-left-constant {A = A} {B = B} {original-square = original-square} 
        {bl = bl} {br = br} {bb = bb} {bt = bt} {new-b = new-b} square id = 
            compPathP-leftconst (λ i → PathP (λ j → B (original-square i j)) (bb i) (bt i)) 
                {x = new-b} {y = bl} {z = br} 
                id 
                square

    SquareP'-replace-edge-right-constant : {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        {original-square : Square a₀₋ a₁₋ a₋₀ a₋₁}
        {bl : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁}
        {br : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁}
        {bb : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀} 
        {bt : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁}
        {new-b : PathP (λ j → B (a₁₋ j)) b₁₀ b₁₁}
        (square : SquareP' B original-square bl br bb bt) (id : br ≡ new-b)
        → SquareP' B original-square (bl) (new-b) (bb) (bt)

    SquareP'-replace-edge-right-constant {A = A} {B = B} {original-square = original-square} 
        {bl = bl} {br = br} {bb = bb} {bt = bt} {new-b = new-b} square id = 
            compPathP-rightconst (λ i → PathP (λ j → B (original-square i j)) (bb i) (bt i)) 
                {x = bl} {y = br} {z = new-b} 
                square
                id 

    SquareP'-replace-edge-bot-constant : {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        {original-square : Square a₀₋ a₁₋ a₋₀ a₋₁}
        {bl : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁}
        {br : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁}
        {bb : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀} 
        {bt : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁}
        {new-b : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀}
        (square : SquareP' B original-square bl br bb bt) (id : new-b ≡ bb)
        → SquareP' B original-square (bl) (br) (new-b) (bt)

    SquareP'-replace-edge-bot-constant {A = A} {B = B} {original-square = original-square} 
        {bl = bl} {br = br} {bb = bb} {bt = bt} {new-b = new-b} square id = SquareP'-to-vertical {B = B} (
            compPathP-leftconst (λ j → PathP (λ i → B (original-square i j)) (bl j) (br j)) 
                {x = new-b} {y = bb} {z = bt} 
                id
                (SquareP'-to-horizontal {B = B} square)       
        )
    

    SquareP'-replace-edge-top-constant : {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        {original-square : Square a₀₋ a₁₋ a₋₀ a₋₁}
        {bl : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁}
        {br : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁}
        {bb : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀} 
        {bt : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁}
        {new-b : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁}
        (square : SquareP' B original-square bl br bb bt) (id : bt ≡ new-b)
        → SquareP' B original-square (bl) (br) (bb) (new-b)

    SquareP'-replace-edge-top-constant {A = A} {B = B} {original-square = original-square} 
        {bl = bl} {br = br} {bb = bb} {bt = bt} {new-b = new-b} square id = SquareP'-to-vertical {B = B} (
            compPathP-rightconst (λ j → PathP (λ i → B (original-square i j)) (bl j) (br j)) 
                {x = bb} {y = bt} {z = new-b} 
                (SquareP'-to-horizontal {B = B} square)
                id       
        )


    SquareP'-replace-edge-left : {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        {original-square : Square a₀₋ a₁₋ a₋₀ a₋₁}
        {bl : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁}
        {br : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁}
        {bb : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀} 
        {bt : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁}
        {new-a : a₀₀ ≡ a₀₁} {a-id : new-a ≡ a₀₋}
        {new-b : PathP (λ j → B (new-a j)) b₀₀ b₀₁}
        (square : SquareP' B original-square bl br bb bt) (id : PathP (λ i → PathP (λ j → B (a-id i j)) b₀₀ b₀₁) new-b bl)
        → SquareP' B (Square-replace-edge-left original-square (sym a-id)) (new-b) (br) (bb) (bt)

    SquareP'-replace-edge-left {A = A} {B = B} {original-square = original-square} {bl = bl} {br = br} {bb = bb} {bt = bt} 
        {new-a = new-a} {a-id = a-id} {new-b = new-b}
        square id = SquareP'-replace-base-square {B = B} final-square equality-between-base-squares where
            comp-square : SquareP' B (Square-comp-right a-id original-square) new-b br (compPathP' {B = B} refl bb) (compPathP' {B = B} refl bt)
            comp-square = SquareP'-compose-right {A = A} {B = B} id square

            equality-between-base-squares : (Square-comp-right-leftrefl a-id original-square) ≡ (Square-replace-edge-left original-square (sym a-id))
            equality-between-base-squares = refl
            
            final-square : SquareP' B (Square-comp-right-leftrefl a-id original-square) (new-b) (br) (bb) (bt)
            final-square = transport (λ k → 
                PathP (λ i → 
                    PathP (λ j → B (((Square-path-right-leftrefl a-id original-square) k) i j)) 
                        (lUnitP' B bb (~ k) i) 
                        (lUnitP' B bt (~ k) i))
                    new-b     
                    br) 
                comp-square
                
    SquareP'-replace-edge-top : {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        {original-square : Square a₀₋ a₁₋ a₋₀ a₋₁}
        {bl : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁}
        {br : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁}
        {bb : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀} 
        {bt : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁}
        {new-a : a₀₁ ≡ a₁₁} {a-id : a₋₁ ≡ new-a}
        {new-b : PathP (λ j → B (new-a j)) b₀₁ b₁₁}
        (square : SquareP' B original-square bl br bb bt) (id : PathP (λ j → PathP (λ i → B (a-id j i)) b₀₁ b₁₁) bt new-b)
        → SquareP' B (Square-replace-edge-top original-square (a-id)) (bl) (br) (bb) (new-b)

    SquareP'-replace-edge-top {A = A} {B = B} {original-square = original-square} {bl = bl} {br = br} {bb = bb} {bt = bt} 
        {new-a = new-a} {a-id = a-id} {new-b = new-b} square id = 
            SquareP'-replace-base-square {B = B} final-square equality-between-base-squares where
                comp-square : SquareP' B (Square-comp-up original-square (Square-to-horizontal a-id)) (compPathP' {B = B} bl refl) (compPathP' {B = B} br refl) bb new-b
                comp-square = SquareP'-compose-top {A = A} {B = B} square (SquareP'-to-horizontal {B = B} id)

                equality-between-base-squares : (Square-comp-up-toprefl original-square (Square-to-horizontal a-id)) ≡ (Square-replace-edge-top original-square (a-id))
                equality-between-base-squares = refl
            
                final-square : SquareP' B (Square-comp-up-toprefl original-square (Square-to-horizontal a-id)) (bl) (br) (bb) (new-b)
                final-square = SquareP'-to-vertical {B = B} (transport (λ k → 
                    PathP (λ j → 
                        PathP (λ i → B (((Square-path-up-toprefl original-square (Square-to-horizontal a-id)) k) i j)) 
                            (rUnitP' B bl (~ k) j) 
                            (rUnitP' B br (~ k) j))
                        bb
                        new-b) 
                    (SquareP'-to-horizontal {B = B} comp-square))

{-
    square-replace-edge-right : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
        {al : PathP (λ j → A i0 j) a₀₀ a₀₁} {ar : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {ab : PathP (λ i → A i i0) a₀₀ a₁₀} {at : PathP (λ i → A i i1) a₀₁ a₁₁}
        {br : PathP (λ j → A i1 j) a₁₀ a₁₁}
        (a-square : SquareP A (al) (ar) (ab) (at)) (r-id : ar ≡ br)
        → SquareP A (al) (br) (ab) (at)

    square-replace-edge-right {A = A} {al = al} {ar = ar} {ab = ab} {at = at} {br = br}
        a-square r-id = PathP-replace-end a-square r-id

    square-replace-edge-bottom : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
        {al : PathP (λ j → A i0 j) a₀₀ a₀₁} {ar : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {ab : PathP (λ i → A i i0) a₀₀ a₁₀} {at : PathP (λ i → A i i1) a₀₁ a₁₁}
        {bb : PathP (λ i → A i i0) a₀₀ a₁₀}
        (a-square : SquareP A (al) (ar) (ab) (at)) (b-id : ab ≡ bb)
        → SquareP A (al) (ar) (bb) (at)

    square-replace-edge-bottom {A = A} {al = al} {ar = ar} {ab = ab} {at = at} {bb = bb}
        a-square b-id = dep-square-to-vertical (square-replace-edge-left {A = λ i j → A j i} (dep-square-to-horizontal a-square) b-id)

    square-replace-edge-top : {ℓ : Level} {A : I → I → Type ℓ}
        {a₀₀ : A i0 i0} {a₁₀ : A i1 i0} {a₀₁ : A i0 i1} {a₁₁ : A i1 i1}
        {al : PathP (λ j → A i0 j) a₀₀ a₀₁} {ar : PathP (λ j → A i1 j) a₁₀ a₁₁}
        {ab : PathP (λ i → A i i0) a₀₀ a₁₀} {at : PathP (λ i → A i i1) a₀₁ a₁₁}
        {bt : PathP (λ i → A i i1) a₀₁ a₁₁}
        (a-square : SquareP A (al) (ar) (ab) (at)) (t-id : at ≡ bt)
        → SquareP A (al) (ar) (ab) (bt)

    square-replace-edge-top {A = A} {al = al} {ar = ar} {ab = ab} {at = at} {bt = bt}
        a-square t-id = dep-square-to-vertical (square-replace-edge-right {A = λ i j → A j i} (dep-square-to-horizontal a-square) t-id)

-}
    postulate
        toSquareP' : {ℓ : Level} {A : Type ℓ} {B : A → Type ℓ'}
            {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
            {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
            {original-square : Square a₀₋ a₁₋ a₋₀ ((sym a₀₋) ∙∙ a₋₀ ∙∙ a₁₋)}
            {a-coherence : ((sym a₀₋) ∙∙ a₋₀ ∙∙ a₁₋) ≡ a₋₁}
            (bl : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁)
            (br : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁)
            (bb : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀) 
            (bt : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁)
            → (glue : transport (λ j → PathP (λ i → B (a-coherence j i)) b₀₁ b₁₁) (dep-doublecomp' {B = B} (symP bl) (bb) (br)) ≡ (bt))
            → SquareP' B (Square-replace-edge-top original-square a-coherence) (bl) (br) (bb) (bt)

    {- toSquareP' {B = B} {a₀₋ = a₀₋} {a₋₀ = a₋₀} {a₁₋ = a₁₋} {a₋₁ = a₋₁}
        {original-square = original-square} {a-coherence = a-coherence} bl br bb bt glue = {! test-3 !} where
        
        test-2 = SquareP'-replace-edge-top {B = B} {new-a = a₋₁} {a-id = a-coherence}
                    (SquareP'-to-vertical {B = B} (dep-doublecomp'-filler {B = B} (symP bl) bb br))
                    (toPathP glue)

        test-3 : SquareP' B (Square-replace-edge-top original-square a-coherence) (bl) (br) (bb) (bt)
        test-3 = SquareP'-replace-base-square {B = B} {new-base-square = Square-replace-edge-top original-square a-coherence}
                (SquareP'-replace-edge-left {B = B} test-2 (symInvoP bl)) 
                {!   !} -}




    --postulate
    --    SquareP'-from-comp-equality : {A : Type ℓ} {B : A → Type ℓ'}
    --        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
    --        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
    --        {glue-a : a₋₀ ∙ a₁₋ ≡ a₀₋ ∙ a₋₁}
    --        (b₀₋ : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁)
    --        (b₁₋ : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁)
    --        (b₋₀ : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀) 
    --        (b₋₁ : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁)
    --        (glue : PathP (λ i → PathP (λ j → B (glue-a i j)) b₀₀ b₁₁) (compPathP' {B = B} b₋₀ b₁₋) (compPathP' {B = B} b₀₋ b₋₁))
    --        → SquareP' B (compPath→Square glue-a) b₀₋ b₁₋ b₋₀ b₋₁

    -- SquareP'-from-comp-equality left right bot top glue = {!   !}

    SquareP'-to-SquareP : {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        {a-square : Square a₀₋ a₁₋ a₋₀  a₋₁}
        {b₀₋ : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁}
        {b₁₋ : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁}
        {b₋₀ : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀} 
        {b₋₁ : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁}
        (square : SquareP' B a-square b₀₋ b₁₋ b₋₀ b₋₁)
        → SquareP (λ i j → B (a-square i j)) b₀₋ b₁₋ b₋₀ b₋₁

    SquareP'-to-SquareP square i j = square i j 
        

    --compPath→Square
