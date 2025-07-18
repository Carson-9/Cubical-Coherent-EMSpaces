{-# OPTIONS --cubical #-}

module BZ2.Z2 where

    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.Univalence
    open import Cubical.Foundations.Function
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Foundations.Equiv
    open import Cubical.Data.Bool
    open import Agda.Builtin.Bool renaming (false to zero; true to one)
    open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

    ℤ₂ = Bool

    _+_ : ℤ₂ → ℤ₂ → ℤ₂
    _+_ = _⊕_ 

    -_ : ℤ₂ → ℤ₂
    - zero = zero
    - one = one

    boolean-double-negation : (x : Bool) → x ≡ not (not x)
    boolean-double-negation zero = refl
    boolean-double-negation true = refl

    -IsInv : (x : ℤ₂) → x + (- x) ≡ zero
    -IsInv zero = refl
    -IsInv true = refl

    g+g≡zero : (x : ℤ₂) → ((x + x) ≡ zero)
    g+g≡zero zero = refl
    g+g≡zero true = refl

    true-opposite : (x : ℤ₂) → (true + x) ≡ not x
    true-opposite zero = refl
    true-opposite true = refl

    -- Problème de contrainte de congruence ...
    zero-neutral-right : (x : ℤ₂) → x + zero ≡ x
    zero-neutral-right zero = refl
    zero-neutral-right true = refl

    zero-neutral-left : (x : ℤ₂) → zero + x ≡ x
    zero-neutral-left zero = refl
    zero-neutral-left true = refl

    +assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +assoc zero zero zero = refl
    +assoc zero zero true = refl
    +assoc zero true zero = refl
    +assoc zero true true = refl
    +assoc true zero zero = refl
    +assoc true zero true = refl
    +assoc true true zero = refl
    +assoc true true true = refl

    +comm : ∀ x y → (x + y) ≡ (y + x)
    +comm zero zero = refl
    +comm zero true = refl
    +comm true zero = refl
    +comm true true = refl

    ℤ₂EquivFun : ℤ₂ → ℤ₂ ≅ ℤ₂
    ℤ₂EquivFun g = (iso f localInv rInv lInv) where
            
        f : ℤ₂ → ℤ₂
        f x = g + x

        localInv : ℤ₂ → ℤ₂       -- Sur ℤ₂
        localInv x = g + x        

        rInv : section f localInv
        rInv zero = (
            f (localInv zero)
            ≡⟨ sym (+assoc g g zero) ⟩
            (g + g) + zero
            ≡⟨ cong (λ x → x + zero) (g+g≡zero g) ⟩
            zero + zero ∎
            ) 
        rInv one = (
            f (localInv one)
            ≡⟨ sym (+assoc g g one) ⟩
            (g + g) + one
            ≡⟨ cong (λ x → x + one) (g+g≡zero g) ⟩
            zero + one ∎
            )

        lInv : retract f localInv
        lInv = rInv

    ℤ₂EquivPath : ℤ₂ → ℤ₂ ≡ ℤ₂
    ℤ₂EquivPath g = ua (isoToEquiv (ℤ₂EquivFun g)) 


    -- Le case split est beaucoup plus simple ...

    ℤ₂EquivInvolution : (g : ℤ₂) (x : ℤ₂) → (_≅_.fun (compIso (ℤ₂EquivFun g)  (ℤ₂EquivFun g))) x ≡ x
    ℤ₂EquivInvolution zero x = refl
    ℤ₂EquivInvolution one x = (
        (_≅_.fun (compIso (ℤ₂EquivFun one)  (ℤ₂EquivFun one))) x
        ≡⟨ refl ⟩
        one + (one + x)
        ≡⟨ sym (+assoc one one x) ⟩
        (one + one) + x
        ≡⟨ cong (λ z → z + x) (g+g≡zero one) ⟩
        zero + x
        ≡⟨ refl ⟩
        x ∎)
        

    postulate
        ℤ₂EquivPathInvolution : (g : ℤ₂) → (ℤ₂EquivPath g) ∙ (ℤ₂EquivPath g) ≡ refl ∙ refl
    
    {-

    -- uaCompEquiv : ∀ {A B C : Type ℓ} → (e : A ≃ B) (f : B ≃ C) → ua (compEquiv e f) ≡ ua e ∙ ua f

    ℤ₂EquivPathInvolution g = (congruenceGives) ∙ (uaIdEquiv) where

        funcEq : compIso (ℤ₂EquivFun g)  (ℤ₂EquivFun g) ≡ (idIso {A = ℤ₂})
        funcEq x = {!   !}

        congruenceGives : ℤ₂EquivPath g ∙ ℤ₂EquivPath g ≡ (ua (idEquiv ℤ₂))
        congruenceGives = pathToEquiv (ℤ₂EquivPath g ∙ ℤ₂EquivPath g)
    -}


    ℤ₂isSet : isSet ℤ₂
    ℤ₂isSet = isSetBool
