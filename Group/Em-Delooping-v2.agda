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

module Group.Em-Delooping-v2 where

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
  
      postulate
          subst-action-inv : (x y : X) → subst code (sym (incl x)) y ≡ y × (inv x)

      decode : (x : BG) → code x → ⋆ ≡ x
      decode = Delooping-2-ind
        incl
        inclP
        inclFunP
        {! λ x → isOfHLevelΠ   !} -- Un truc pas loin
        
        where

        path-family : (z : BG) → Type₁
        path-family z = ⋆ ≡ z

        partial-fiber : (z : BG) → Type₁
        partial-fiber z = code z → path-family z 

        inclP-subst : (x : X) → subst partial-fiber (incl x) incl ≡ incl
        inclP-subst x = 
          
          funExt (λ y →
                  cong (λ t → subst path-family (incl x) (incl t)) (subst-action-inv x y) ∙
                  substInPathsL (incl x) (incl (y × inv x)) ∙
                  incl-fun-equality (y × inv x) x ∙
                  cong incl ((×-assoc y (inv x) x)) ∙
                  cong (λ t → (incl (y × t))) (inv-left x) ∙
                  cong incl (e-right y)
                )

          -- (funExt (λ y → cong (λ t → subst path-family (incl x) (incl t)) (subst-action-inv x y))) ∙
          -- (funExt (λ y → substInPathsL (incl x) (incl (y × inv x)))) ∙
          -- (funExt (λ y → incl-fun-equality (y × inv x) x)) ∙
          -- (funExt (λ y → cong incl ((×-assoc y (inv x) x)))) ∙
          -- (funExt (λ y → cong (λ t → (incl (y × t))) (inv-left x))) ∙
          -- (funExt (λ y → cong incl (e-right y)))

          -- subst partial-fiber (incl x) incl ≡⟨ fromPathP (funTypeTransp code path-family (incl x) incl) ⟩
          -- (λ y → subst path-family (incl x) (incl (subst code (sym (incl x)) y))) ≡⟨ funExt (λ y → cong (λ t → subst path-family (incl x) (incl t)) (subst-action-inv x y)) ⟩ 
          -- (λ y → subst path-family (incl x) (incl ((y × inv x)))) ≡⟨ refl ⟩
          -- (λ y → subst path-family (incl x) (incl (y × inv x))) ≡⟨ funExt (λ y → substInPathsL (incl x) (incl (y × inv x))) ⟩
          -- (λ y → incl (y × inv x) ∙ incl x) ≡⟨ funExt (λ y → incl-fun-equality (y × inv x) x) ⟩
          -- (λ y → incl ((y × inv x) × x)) ≡⟨ funExt (λ y → cong incl ((×-assoc y (inv x) x))) ⟩
          -- (λ y → incl (y × ((inv x) × x))) ≡⟨ funExt (λ y → cong (λ t → (incl (y × t))) (inv-left x)) ⟩
          -- (λ y → incl (y × e)) ≡⟨ funExt (λ y → cong incl (e-right y)) ⟩
          -- incl ∎


        inclP : (x : X) → PathP (λ i → code ([ x ]₂ i) → ⋆ ≡ [ x ]₂ i) incl incl
        inclP x = toPathP (inclP-subst x)


        inclFunP : (x y : X) → SquareP (λ i j → code (incl-fun x y i j) → ⋆ ≡ incl-fun x y i j) (inclP y) (inclP (y × x)) (λ _ → incl) (inclP x)
        inclFunP x y i j = {!   !} where

          transport-over-composite : (x y : X) → subst partial-fiber ((incl x) ∙ (incl y)) incl ≡ incl
          transport-over-composite x y = 
              (substComposite partial-fiber (incl x) (incl y) incl)  ∙
              cong (subst partial-fiber (incl y)) (inclP-subst x) ∙
              (inclP-subst y)


          transport-over-2-fun : (x y : X) → subst partial-fiber ((incl x) ∙ (incl y)) incl ≡ incl
          transport-over-2-fun x y = 
              cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y) ∙
              (inclP-subst (x × y))


          2-coherence : (x y : X) → (transport-over-composite x y) ≡ (transport-over-2-fun x y)
          2-coherence x y = {!   !} where
            
            true-reduction : (x y : X) →  (transport-over-composite x y) ∙ (sym (transport-over-2-fun x y)) ≡ refl
            true-reduction x y = (
              ((substComposite partial-fiber (incl x) (incl y) incl)  ∙
              cong (subst partial-fiber (incl y)) (inclP-subst x) ∙
              (inclP-subst y)) ∙
              (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y) ∙ 
              (inclP-subst (x × y))))
              ≡⟨ cong (λ t → (transport-over-composite x y) ∙ t) 
                    (symDistr (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)) (inclP-subst (x × y)) ) ⟩
              
              ((substComposite partial-fiber (incl x) (incl y) incl)  ∙
              cong (subst partial-fiber (incl y)) (inclP-subst x) ∙
              (inclP-subst y)) ∙
              ((sym (inclP-subst (x × y))) ∙
              (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y))))
              ≡⟨ assoc-heavy-rewriting ⟩  -- de l'associativité

              (substComposite partial-fiber (incl x) (incl y) incl)  ∙
              (cong (subst partial-fiber (incl y)) (inclP-subst x) ∙
              (inclP-subst y) ∙
              (sym (inclP-subst (x × y)))) ∙
              (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)))
              ≡⟨ cong (λ t → (substComposite partial-fiber (incl x) (incl y) incl) ∙ t ∙ 
              (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)))) inclP-red ⟩

              (substComposite partial-fiber (incl x) (incl y) incl) ∙
              ((sym (substComposite partial-fiber (incl x) (incl y) incl)) ∙ 
              (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y))) ∙
              (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)))

              ≡⟨ cong (λ t → (substComposite partial-fiber (incl x) (incl y) incl) ∙ t) (sym (assoc
                      (sym (substComposite partial-fiber (incl x) (incl y) incl))
                      (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y))
                      (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y))))) ∙
                    (assoc 
                        (substComposite partial-fiber (incl x) (incl y) incl)
                        (sym (substComposite partial-fiber (incl x) (incl y) incl))
                        ((cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)) ∙ (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y))))) ⟩ -- de l'associativité
              
              ((substComposite partial-fiber (incl x) (incl y) incl) ∙ 
              (sym (substComposite partial-fiber (incl x) (incl y) incl))) ∙
              ((cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)) ∙
              (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y))))
              ≡⟨ (cong (λ t → t ∙ ((cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)) ∙
                                    (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y))))) 
                        (rCancel (substComposite partial-fiber (incl x) (incl y) incl))) ∙
                (cong (λ t → refl ∙ t) (rCancel ((cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y))))) ⟩ 
              
              refl ∙ refl
              ≡⟨ sym (lUnit refl) ⟩
              
              refl ∎) where

              inclP-red : 
                  (cong (subst partial-fiber (incl y)) (inclP-subst x)) ∙ 
                  (inclP-subst y) ∙ 
                  (sym (inclP-subst (x × y))) 
                  ≡ 
                  (sym (substComposite partial-fiber (incl x) (incl y) incl)) ∙ 
                  (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y))

              inclP-red = 
                (cong (subst partial-fiber (incl y)) (inclP-subst x)) ∙
                (inclP-subst y) ∙
                (sym (inclP-subst (x × y)))
                ≡⟨ {!  !} ⟩
                
                (sym (substComposite partial-fiber (incl x) (incl y) incl)) ∙
                (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)) ∎


              assoc-heavy-rewriting : 
                ((substComposite partial-fiber (incl x) (incl y) incl)  ∙
                cong (subst partial-fiber (incl y)) (inclP-subst x) ∙
                (inclP-subst y)) ∙
                ((sym (inclP-subst (x × y))) ∙
                (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y))))
                ≡
                (substComposite partial-fiber (incl x) (incl y) incl)  ∙
                (cong (subst partial-fiber (incl y)) (inclP-subst x) ∙
                (inclP-subst y) ∙
                (sym (inclP-subst (x × y)))) ∙
                (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)))

              assoc-heavy-rewriting = 
                (assoc 
                    (((substComposite partial-fiber (incl x) (incl y) incl)  ∙
                      cong (subst partial-fiber (incl y)) (inclP-subst x) ∙
                      (inclP-subst y))) 
                    (sym (inclP-subst (x × y))) 
                    (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)))) ∙
                (cong (λ t → t ∙ (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)))) 
                  (sym (assoc
                      (substComposite partial-fiber (incl x) (incl y) incl)
                        ((cong (subst partial-fiber (incl y)) (inclP-subst x)) ∙
                        (inclP-subst y))
                      (sym (inclP-subst (x × y))) 
                        ))) ∙
                (cong (λ t → ((substComposite partial-fiber (incl x) (incl y) incl) ∙ t) ∙ 
                            (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)))) 
                  (sym (assoc 
                        (cong (subst partial-fiber (incl y)) (inclP-subst x))
                        (inclP-subst y)
                        (sym (inclP-subst (x × y)))
                        ))) ∙
                (sym (assoc
                      (substComposite partial-fiber (incl x) (incl y) incl)
                      ((cong (subst partial-fiber (incl y)) (inclP-subst x)) ∙ 
                        (inclP-subst y) ∙
                        (sym (inclP-subst (x × y))))
                      (sym (cong (λ t → subst partial-fiber t incl) (incl-fun-equality x y)))
                      ))


          composite-path : (x y : X) → PathP (λ i → partial-fiber (((incl x) ∙ (incl y)) i)) incl incl
          composite-path x y = toPathP (transport-over-composite x y)
            --compPathP-transpComp' (inclP-subst x) (inclP-subst y)

          functorial-path : (x y : X) → PathP (λ i → partial-fiber (((incl x) ∙ (incl y)) i)) incl incl
          functorial-path x y = toPathP (transport-over-2-fun x y)
            --PathP (λ i → partial-fiber ((refl ∙ (incl (x × y)) i))) incl incl
            --compPathP-transpComp' refl (inclP-subst (x × y))