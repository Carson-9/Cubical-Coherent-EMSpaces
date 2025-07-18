{-# OPTIONS --cubical --allow-unsolved-metas #-}


open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Pointed hiding (⋆)
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Univalence


open import Group.Em-Group
open import Cellular.Square
open import Cellular.Dependent-Path

open import Cellular.Path-Properties

module Group.Em-Delooping where

    private
        variable
            ℓ ℓ' : Level


    module _ (X : Type ℓ-zero) (G : Group X) where

      open import Group.Em-Delooping-prelude X G

      code : BG → Type ℓ-zero
      code =
        Delooping-2-elim
        X
        action
        {! (λ x y → setIsGroupoid X X) !} -- Un truc pas loin
        (isGroupoid→is2Groupoid (setIsGroupoid))

      encode : (x : BG) → ⋆ ≡ x → code x
      encode x p = subst code p e

      decode : (x : BG) → code x → ⋆ ≡ x
      decode = Delooping-2-ind
        incl
        inclP
        inclFunP
        {! λ x → isOfHLevelΠ   !} -- Un truc pas loin
        
        where
        
        inclP : (x : X) → PathP (λ i → code ([ x ]₂ i) → ⋆ ≡ [ x ]₂ i) incl incl
        inclP x = toPathP (
          transport (λ i → code ([ x ]₂ i) → ⋆ ≡ [ x ]₂ i) incl ≡⟨ fromPathP (funTypeTransp code (λ x → ⋆ ≡ x) (incl x) incl) ⟩
          subst (λ x → ⋆ ≡ x) (incl x) ∘ incl ∘ subst code (sym (incl x)) ≡⟨ {!   !} ⟩ --cong {! (λ t → subst (λ x → ⋆ ≡ x) (incl x) (incl t))  !} refl
          subst (λ x → ⋆ ≡ x) (incl x) ∘ incl ∘ (λ y → y × inv x) ≡⟨ refl ⟩
          subst (λ x → ⋆ ≡ x) (incl x) ∘ (λ y → incl (y × inv x)) ≡⟨ funExt (λ y → substInPathsL (incl x) (incl (y × inv x))) ⟩
          (λ y → incl (y × inv x) ∙ incl x) ≡⟨ funExt (λ y → incl-fun-equality (y × inv x) x) ⟩
          (λ y → incl ((y × inv x) × x)) ≡⟨ funExt (λ y → cong incl ((×-assoc y (inv x) x))) ⟩
          (λ y → incl (y × ((inv x) × x))) ≡⟨ funExt (λ y → cong (λ t → (incl (y × t))) (inv-left x)) ⟩
          (λ y → incl (y × e)) ≡⟨ funExt (λ y → cong incl (e-right y)) ⟩
          incl ∎)


        inclFunP : (x y : X) → SquareP (λ i j → code (incl-fun x y i j) → ⋆ ≡ incl-fun x y i j) (inclP y) (inclP (y × x)) (λ _ → incl) (inclP x)
        inclFunP x y i j = {!   !} where


          coin-bg-transp : (t : X) → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl x) ∙ (incl y)) ≡ incl t
          coin-bg-transp t = 
            subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl x) ∙ (incl y)) 
              ≡⟨ substInPathsL (incl (inv (x × y))) ((incl t) ∙ (incl x) ∙ (incl y)) ⟩
            ((incl t) ∙ (incl x) ∙ (incl y)) ∙ (incl (inv (x × y))) 
              ≡⟨ sym (assoc (incl t) ((incl x) ∙ (incl y)) (incl (inv (x × y)))) ⟩
            (incl t) ∙ (((incl x) ∙ (incl y)) ∙ (incl (inv (x × y))))
              ≡⟨ (cong (λ z → (incl t) ∙ (z ∙ incl (inv (x × y)))) (incl-fun-equality x y)) ⟩
            (incl t) ∙ (((incl (x × y))) ∙ (incl (inv (x × y))))
              ≡⟨ cong (λ z → (incl t) ∙ z) (incl-fun-equality (x × y) (inv (x × y))) ⟩
            (incl t) ∙ incl ((x × y) × (inv (x × y))) 
              ≡⟨ cong (λ z → incl t ∙ incl z) (inv-right (x × y)) ⟩
            (incl t) ∙ (incl e)
              ≡⟨ (cong (λ z → incl t ∙ z ) (incl-e)) ∙ (sym (rUnit (incl t))) ⟩
            incl t ∎

          coin-bd-transp : (t : X) → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl (x × y))) ≡ incl t
          coin-bd-transp t = 
            subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl (x × y)))
            ≡⟨ cong (λ w → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) w) 
                (cong (λ w' → incl t ∙ w') (sym (incl-fun-equality x y))) ⟩
            subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl x) ∙ (incl y))
            ≡⟨ coin-bg-transp t ⟩
            incl t ∎



          coin-hg-transp : (t : X) → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl (t × x)) ∙ (incl y)) ≡ incl t
          coin-hg-transp t = 
            subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl (t × x)) ∙ (incl y))
              ≡⟨ cong (λ w → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) w) 
                ((cong (λ w' → w' ∙ (incl y)) (sym (incl-fun-equality t x))) ∙ (sym (assoc (incl t) (incl x) (incl y)))) ⟩
            subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl x) ∙ (incl y))
              ≡⟨ coin-bg-transp t ⟩
            incl t ∎


          coin-hd-transp-leftassoc : (t : X) → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl ((t × x) × y)) ≡ incl t
          coin-hd-transp-leftassoc t = 
            subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl ((t × x) × y))
            ≡⟨ cong (λ w → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) w) 
                (sym (incl-fun-equality (t × x) y)) ⟩
            subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl (t × x)) ∙ (incl y))
              ≡⟨ coin-hg-transp t ⟩
            incl t ∎

          coin-hd-transp-rightassoc : (t : X) → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl (t × (x × y))) ≡ incl t
          coin-hd-transp-rightassoc t = 
            subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl (t × (x × y)))
            ≡⟨ cong (λ w → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) w) 
                (sym (incl-fun-equality t (x × y))) ⟩
            subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl t ∙ (incl (x × y)))
              ≡⟨ coin-bd-transp t ⟩
            incl t ∎


----- On montre que la "composée" des chemins commute bien -----
{-
                        inclP
        incl --------------------------> incl
          ^                               ^
          |                               |
  subst (λ z → ⋆ ≡ z) ⋯          subst (λ z → ⋆ ≡ z) ⋯
          |                               |
    λ t → incl t ∙ xxx ----------> λ t → incl t ∙ xxx 

-}

------------- LEFT FACE ---------------
          -- transport over x
          transp-acts-well-left : transport (λ i → code ([ x ]₂ i) → ⋆ ≡ [ x ]₂ i) 
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl x) ∙ (incl y)))
            ≡ λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl (t × x) ∙ incl y)
            --λ t → cong (λ w → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) w) (cong (λ w' → w' ∙ incl y) (incl-fun-equality t x))
          
          transp-acts-well-left = 
            transport (λ i → code ([ x ]₂ i) → ⋆ ≡ [ x ]₂ i) 
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl x) ∙ (incl y)))
            ≡⟨ cong (transport (λ i → code ([ x ]₂ i) → ⋆ ≡ [ x ]₂ i)) (funExt coin-bg-transp)  ⟩
            transport (λ i → code ([ x ]₂ i) → ⋆ ≡ [ x ]₂ i) incl
            ≡⟨ fromPathP (inclP x) ⟩
            incl
            ≡⟨ sym (funExt coin-hg-transp) ⟩
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl (t × x) ∙ incl y)) ∎


          left-face = toPathP {A = (λ l → code ([ x ]₂ l) → ⋆ ≡ [ x ]₂ l)} 
            {x = λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl x) ∙ (incl y))} 
            transp-acts-well-left



------------- BOTTOM FACE ---------------
          -- transport over x × y
          transp-acts-well-bot : transport (λ i → code ([ x × y ]₂ i) → ⋆ ≡ [ x × y ]₂ i) 
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl x) ∙ (incl y)))
            ≡ λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl t ∙ incl (x × y))
          
          transp-acts-well-bot = 
            transport (λ i → code ([ x × y ]₂ i) → ⋆ ≡ [ x × y ]₂ i) 
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl x) ∙ (incl y)))
            ≡⟨ cong (transport (λ i → code ([ x × y ]₂ i) → ⋆ ≡ [ x × y ]₂ i)) (funExt coin-bg-transp) ⟩
            transport (λ i → code ([ x × y ]₂ i) → ⋆ ≡ [ x × y ]₂ i) incl
            ≡⟨ fromPathP (inclP (x × y)) ⟩
            incl
            ≡⟨ sym (funExt coin-bd-transp) ⟩
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl t ∙ incl (x × y))) ∎
            
          bot-face = toPathP {A = (λ i → code ([ x × y ]₂ i) → ⋆ ≡ [ x × y ]₂ i)}
            {x = (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl x) ∙ (incl y)))}
            transp-acts-well-bot


------------- RIGHT FACE ---------------
          -- transport over refl
          transp-acts-well-right : transport (λ i → code ⋆ → ⋆ ≡ ⋆)
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl (x × y))))
            ≡ (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl ((t × x) × y))))

          transp-acts-well-right = 
            transport (λ i → code ⋆ → ⋆ ≡ ⋆)
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl (x × y))))
            ≡⟨ cong (transport (λ i → code ⋆ → ⋆ ≡ ⋆)) (funExt coin-bd-transp) ⟩
            transport (λ i → code ⋆ → ⋆ ≡ ⋆) incl
            ≡⟨ transportRefl incl ⟩
            incl 
            ≡⟨ sym (funExt coin-hd-transp-leftassoc) ⟩
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl ((t × x) × y)))) ∎
            
            {- funExt compwise where
            compwise : (t : X) → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl (x × y))) ≡ subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl ((t × x) × y)))
            compwise t = cong (λ w → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) w) (incl-fun-equality t (x × y))
              ∙ cong (λ w → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl w)) (sym (×-assoc t x y))
 -}
          right-face = toPathP {A = (λ i → code ⋆ → ⋆ ≡ ⋆)} 
            {x = (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl (x × y))))}
            transp-acts-well-right

          transport-compose-right : transport (λ i → code ⋆ → ⋆ ≡ ⋆) 
            (λ t → transport (λ i → ⋆ ≡ (incl (inv (x × y)) i)) (incl t ∙ incl (x × y)))
            ≡ λ t → transport (λ i → ⋆ ≡ (incl (inv (x × y)) i)) (transport (λ _ → ⋆ ≡ ⋆) (incl t ∙ incl (x × y))) 

          transport-compose-right = 
            transport (λ i → code ⋆ → ⋆ ≡ ⋆) 
            (λ t → transport (λ i → ⋆ ≡ (incl (inv (x × y)) i))  (incl t ∙ incl (x × y)))
              ≡⟨ cong (transport (λ i → code ⋆ → ⋆ ≡ ⋆))  (funExt coin-bd-transp) ⟩
            transport (λ i → code ⋆ → ⋆ ≡ ⋆)  incl
              ≡⟨ transportRefl incl ⟩
            incl
              ≡⟨ funExt (λ t → (sym (coin-hd-transp-leftassoc t))) ⟩
            (λ (t : X) → transport (λ i → ⋆ ≡ (incl (inv (x × y)) i)) (incl ((t × x) × y)))
              ≡⟨ funExt (λ t → refl) ⟩
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl ((t × x) × y))))
              ≡⟨ funExt (λ t → cong (subst (λ z → ⋆ ≡ z) (incl (inv (x × y)))) ((cong incl ((×-assoc t x y))) ∙ (sym (incl-fun-equality t (x × y))))) ⟩
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl t) ∙ (incl (x × y))))
              ≡⟨ funExt (λ t → cong (subst (λ z → ⋆ ≡ z) (incl (inv (x × y)))) (sym (transportRefl ((incl t) ∙ (incl (x × y)))))) ⟩
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (transport (λ _ → ⋆ ≡ ⋆) (incl t ∙ incl (x × y))))
              ≡⟨ funExt (λ t → refl) ⟩
            (λ (t : X) → transport (λ i → ⋆ ≡ (incl (inv (x × y)) i)) (transport (λ _ → ⋆ ≡ ⋆) (incl t ∙ incl (x × y)))) ∎


          right-square : (t : X) → SquareP ? (toPathP coin-bd-transp t) (toPathP coin-hd-transp-leftassoc t) (incl-fun-equality) (refl)
          right-square = toSquareP-comp (coin-bd-transp t) (coin-hd-transp-leftassoc t) () (transportRefl incl) transport-compose-right

------------- TOP FACE ---------------
          -- transport over y
          transp-acts-well-top : transport (λ i → code ([ y ]₂ i) → ⋆ ≡ [ y ]₂ i)
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl (t × x) ∙ incl y))
            ≡ (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl ((t × x) × y))))

          transp-acts-well-top = 
            transport (λ i → code ([ y ]₂ i) → ⋆ ≡ [ y ]₂ i)
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl (t × x) ∙ incl y))
            ≡⟨ cong (transport (λ i → code ([ y ]₂ i) → ⋆ ≡ [ y ]₂ i)) (funExt coin-hg-transp) ⟩
            transport (λ i → code ([ y ]₂ i) → ⋆ ≡ [ y ]₂ i) incl
            ≡⟨ fromPathP (inclP y) ⟩
            incl
            ≡⟨ sym (funExt coin-hd-transp-leftassoc) ⟩
            (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) ((incl ((t × x) × y)))) ∎


          top-face = toPathP {A = (λ i → code ([ y ]₂ i) → ⋆ ≡ [ y ]₂ i)}
            {x = (λ t → subst (λ z → ⋆ ≡ z) (incl (inv (x × y))) (incl (t × x) ∙ incl y))}
            transp-acts-well-top

          
          transport-compose-top : transport (λ i → code ([ y ]₂ i) → ⋆ ≡ [ y ]₂ i) 
            (λ t → transport (λ i → ⋆ ≡ (incl (inv (x × y)) i)) (incl (t × x) ∙ incl y))
            ≡ λ t → transport (λ i → ⋆ ≡ (incl (inv (x × y)) i)) (transport (λ _ → ⋆ ≡ ⋆) (incl (t × x) ∙ incl y)) --(transport (λ i → ⋆ ≡ ((incl-fun (t × x) y) i i) ) (incl (t × x) ∙ incl y)) --(fromPathP ((incl-fun (t × x) y)))

          transport-compose-top = 
            transport (λ i → code ([ y ]₂ i) → ⋆ ≡ [ y ]₂ i) 
            (λ t → transport (λ i → ⋆ ≡ (incl (inv (x × y)) i)) (incl (t × x) ∙ incl y))
              ≡⟨ cong (transport (λ i → code ([ y ]₂ i) → ⋆ ≡ [ y ]₂ i)) (funExt coin-hg-transp) ⟩
            transport (λ i → code ([ y ]₂ i) → ⋆ ≡ [ y ]₂ i) incl
              ≡⟨ fromPathP (inclP y) ⟩
            incl
              ≡⟨ funExt (λ t → (sym (coin-hd-transp-leftassoc t))) ⟩
            (λ (t : X) → transport (λ i → ⋆ ≡ (incl (inv (x × y)) i)) (incl ((t × x) × y)))
              ≡⟨ funExt (λ t → (cong (transport (λ i → ⋆ ≡ (incl (inv (x × y)) i))) ((sym (incl-fun-equality (t × x) y))))) ⟩
            (λ (t : X) → transport (λ i → ⋆ ≡ (incl (inv (x × y)) i)) (incl (t × x) ∙ incl y))
              ≡⟨ funExt (λ t → (cong (transport (λ i → ⋆ ≡ (incl (inv (x × y)) i))) (sym (transportRefl (incl (t × x) ∙ incl y))) )) ⟩
            (λ (t : X) → transport (λ i → ⋆ ≡ (incl (inv (x × y)) i)) (transport (λ _ → ⋆ ≡ ⋆) (incl (t × x) ∙ incl y))) ∎


          top-square : (t : X) → SquareP {! !} (toPathP (coin-hg-transp t)) (toPathP (coin-hd-transp-leftassoc t)) (incl-fun-equality (t × x) y) (inclP y)
          top-square t = toSquareP-comp (coin-hg-transp t) (coin-hd-transp-leftassoc t) (incl-fun-equality (t × x) y) ((fromPathP (inclP y))) transport-compose-top
            
            --SquareP'-from-transport transport-compose-top

------------- TOTAL SQUARE ---------------

          test : PathP 
            (λ i → PathP (λ j → code (incl-fun x y i j) → ⋆ ≡ (incl-fun x y i j)) incl (inclP x i))
            (inclP y)
            (inclP (y × x))
          test i = {!   !} -- toPathP {! compPathP' (compPathP' (symP right-face i) (incl-2-fun e x y)) (left-face i)  !}
            
            
            --funExt comp
            --          (λ { k (i = i0) → (left-face) j k
            --             ; k (i = i1) → (right-face) j k
            --             ; k (j = i0) → (bot-face) i k
            --             ; k (j = i1) → (top-face) i k
            --             }) ((λ t → incl-2-fun t x y) i j)