{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import BZ2.Delooping-Z2-Header
open import Cellular.Square


module BZ2.BZ2 where
    

    private
        variable 
            ℓ ℓ' : Level
            A : Type ℓ'

    data Bℤ₂ : Type where
        ⋆ : Bℤ₂
        loop : (⋆ ≡ ⋆)
        α : Square loop refl refl loop
        trunc : isGroupoid Bℤ₂
    
    α' : loop ∙ loop ≡ refl
    α' = sym (Square→compPath α) ∙ (sym (lUnit _))


    Bℤ₂-elim : ∀ {ℓ} → {B : Type ℓ} → (⋆-img : B)
        → (loop-im : ⋆-img ≡ ⋆-img)
        → (loop-coh : Square loop-im refl refl loop-im )
        → isGroupoid B
        → Bℤ₂
        → B

    Bℤ₂-elim a p c g ⋆ = a
    Bℤ₂-elim a p c g (loop i) = p i
    Bℤ₂-elim a p c g (α i j) = c i j
    Bℤ₂-elim a p c g (trunc x y p' q' r s i j k) = g 
        (Bℤ₂-elim a p c g x) 
        (Bℤ₂-elim a p c g y) 
        (λ i → Bℤ₂-elim a p c g (p' i)) 
        ((λ i → Bℤ₂-elim a p c g (q' i))) 
        ((λ i j → Bℤ₂-elim a p c g (r i j))) 
        (λ i j → Bℤ₂-elim a p c g (s i j)) 
        i j k 

    Bℤ₂-elim-⋆ : ∀ {ℓ} {A : Type ℓ} (a : A) (p : a ≡ a) (c : Square p refl refl p) (g : isGroupoid A) → Bℤ₂-elim a p c g ⋆ ≡ a     
    Bℤ₂-elim-⋆ a p c g = refl

    Bℤ₂-elim-loop : (a : A) (p : a ≡ a) (c : Square p refl refl p) (g : isGroupoid A) → (cong (Bℤ₂-elim a p c g) loop) ≡ p 
    Bℤ₂-elim-loop a p c g = refl
    
    Bℤ₂-ind : (P : Bℤ₂ → Type ℓ)
        → (x : P ⋆)
        → (over-loop : PathP (λ i → P (loop i)) x x)
        → (over-square : SquareP' {A = Bℤ₂} P α over-loop refl refl over-loop)
        → isOfHLevelDep 3 P
        → (z : Bℤ₂) → P z

    Bℤ₂-ind P x ol os h-l-dep ⋆ = x
    Bℤ₂-ind P x ol os h-l-dep (loop i) = ol i
    Bℤ₂-ind P x ol os h-l-dep (α i j) = os i j 
    Bℤ₂-ind P x ol os h-l-dep (trunc a b p q r s i j k) = h-l-dep 
        (Bℤ₂-ind P x ol os h-l-dep a)
        (Bℤ₂-ind P x ol os h-l-dep b)
        (λ i → Bℤ₂-ind P x ol os h-l-dep (p i))
        (λ i → Bℤ₂-ind P x ol os h-l-dep (q i))
        (λ i j → Bℤ₂-ind P x ol os h-l-dep (r i j))
        (λ i j → Bℤ₂-ind P x ol os h-l-dep (s i j))
        (λ i j k → (trunc a b p q r s i j k )) 
        i j k

    Bℤ₂-ind-prop : (P : Bℤ₂ → Type ℓ) (prop : (x : Bℤ₂) → isProp (P x))
        → (x : P ⋆)
        → (z : Bℤ₂) → P z
        
    Bℤ₂-ind-prop P prop x z = Bℤ₂-ind P x (toPathP (prop ⋆ _ _)) {!   !} {!   !} z

    Bℤ₂-ind-⋆ : (P : Bℤ₂ → Type ℓ) 
        → (x : P ⋆)
        → (o-l : PathP (λ i → P (loop i)) x x)
        → (o-s : SquareP' P α o-l refl refl o-l)
        → (hyp : isOfHLevelDep 3 P)
        → Bℤ₂-ind P x o-l o-s hyp ⋆ ≡ x

    Bℤ₂-ind-⋆ P x ol os hyp = refl   
            
