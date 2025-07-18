{-# OPTIONS --cubical #-}


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

open import Cellular.Square

open import Group.Em-Group

module Group.Em-Delooping-prelude (X : Type ℓ-zero) (G : Group X) where

    private
        variable
            ℓ ℓ' : Level


    postulate
        setIsGroupoid : isGroupoid (Type ℓ-zero)        

    BG = Delooping-2 G
    e = Group.1g G
    e-left = isGroup.l-neutral (Group.makes-group G) 
    e-right = isGroup.r-neutral (Group.makes-group G)
    _×_ = Group._×_ G
    ×-assoc = isGroup.×-assoc (Group.makes-group G) 
    inv = Group.inv G
    inv-left = isGroup.l-inv (Group.makes-group G)
    inv-right = isGroup.r-inv (Group.makes-group G)
    ⋆ = base₂ {g = G}
    incl = [_]₂ {g = G}
    incl-fun = incl-functorial-1₂ {g = G}      
    trunc = 2-trunc {g = G}



    incl-fun-equality : (x y : X) → incl x ∙ incl y ≡ incl (x × y)
    incl-fun-equality x y = (Square→compPath (Square-to-vertical (λ i j → (incl-fun y x) i j))) ∙ (sym (lUnit (incl (x × y))))


    -- La cohérence ajoutée
    postulate
        incl-2-fun : (x y z : X) → Square 
            (((assoc (incl x) (incl y) (incl z))) ∙ (cong (λ t → t ∙ incl z) (incl-fun-equality x y))) 
            (incl-fun-equality x (y × z)) 
            (cong (λ t → incl x ∙ t) (incl-fun-equality y z)) 
            ((incl-fun-equality (x × y) z) ∙ cong incl (×-assoc x y z))


    postulate
        incl-e : incl e ≡ refl
        incl-sym : (x : X) → sym (incl x) ≡ incl (inv x)
    
    -- incl-e = where
    --     ((sym rUnit (incl e)) ∙ lem)
    --     lem : incl e ≡ incl e ∙ incl e
    --     lem =
    --         incl e ≡⟨ cong incl (e-left e) ⟩
    --         incl (e × e) ≡⟨ sym (incl-fun-equality e e) ⟩
    --         incl e ∙ incl e ≡⟨ cong (λ t → incl e ∙ incl t) (sym (inv-right e)) ⟩
    --         incl e ∙ incl (e × (inv e)) ≡⟨ cong (λ t → incl e ∙ t) (sym (incl-fun-equality e (inv e))) ⟩
    --         incl e ∙ (incl e ∙ incl (inv e)) ≡⟨ assoc (incl e) (incl e) (incl (inv e)) ⟩
    --         (incl e ∙ incl e) ∙ incl (inv e) ≡⟨ cong (λ t → t ∙ incl (inv e)) (incl-fun-equality e e) ∙ (e-left e) ⟩
    --         incl e ∙ incl (inv e) ≡⟨ cong (λ t → incl e ∙ incl t) ⟩
    --         incl e ∙ incl e
    --         refl ∎

    action : X → X ≡ X
    action x = ua (isoToEquiv (iso f g sec ret)) where
        f : X → X
        f y = y × x

        g : X → X
        g y =  y × (inv x)

        sec : section f g
        sec y = f (g y) ≡⟨ (×-assoc y (inv x) x ) ⟩ y × ((inv x) × x) ≡⟨ cong (λ t → y × t) (inv-left x) ⟩ y × e ≡⟨ e-right y ⟩ y ∎

        ret : retract f g
        ret y = g (f y) ≡⟨ (×-assoc y x (inv x)) ⟩ y × (x × (inv x)) ≡⟨ cong (λ t → y × t) (inv-right x) ⟩ y × e ≡⟨ e-right y ⟩ y ∎

    -- subst-action-inv x y = {! (cong (λ t → subst code t y) (incl-sym x)) !}