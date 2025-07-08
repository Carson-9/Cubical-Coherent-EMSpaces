{-# OPTIONS --cubical #-}


open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)


open import Group.Em-Group

module Group.Em-Delooping where

    private
        variable
            ℓ ℓ' : Level



    


{- 
    B : {A : Type ℓ} → (Group A) → Pointed (ℓ-suc ℓ)
    B {A} X = (Delooping-2 X , base₂)

    Ω : (B : Pointed ℓ) → Type ℓ
    Ω (X , pt) = pt ≡ pt

    ΩB-inv : {A : Type ℓ} → (G : Group A) → (Ω (B {A = A} G)) ≅ G
    ΩB-inv G = ? 
    
-}