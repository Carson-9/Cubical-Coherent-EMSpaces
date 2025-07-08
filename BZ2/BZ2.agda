{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import BZ2.Delooping-Z2-Header
open import BZ2.Z2
open import Cellular.Square

-- {-# NO_POSITIVITY_CHECK #-}
module BZ2.BZ2 where
    

    private
        variable 
            ℓ : Level
            A : Type ℓ

    data Bℤ₂ : Type where
        ⋆ : Bℤ₂
        loop : (⋆ ≡ ⋆)
        α : Square loop refl refl loop
        trunc : is2Groupoid Bℤ₂

    α' : loop ∙ loop ≡ refl
    α' = {!!} -- roughly, by Square≃doubleComp
    
    Bℤ₂-elim : ∀ {ℓ} → {B : Type ℓ} → (⋆-img : B)
        → (loop-im : ⋆-img ≡ ⋆-img)
        → (loop-coh : Square loop-im refl refl loop-im )
        → is2Groupoid B
        → Bℤ₂
        → B


    Bℤ₂-elim a p c g ⋆ = a
    Bℤ₂-elim a p c g (loop i) = p i
    Bℤ₂-elim a p c g (α i j) = c i j
    Bℤ₂-elim a p c g (trunc x y p' q' r s t u i j k l) = g 
        (Bℤ₂-elim a p c g x) 
        (Bℤ₂-elim a p c g y) 
        (λ i → Bℤ₂-elim a p c g (p' i)) 
        ((λ i → Bℤ₂-elim a p c g (q' i))) 
        ((λ i j → Bℤ₂-elim a p c g (r i j))) 
        (λ i j → Bℤ₂-elim a p c g (s i j)) 
        (λ i j k → Bℤ₂-elim a p c g (t i j k)) 
        (λ i j k → Bℤ₂-elim a p c g (u i j k)) 
        i j k l 

    Bℤ₂-elim-⋆ : ∀ {ℓ} {A : Type ℓ} (a : A) (p : a ≡ a) (c : Square p refl refl p) (g : is2Groupoid A) → Bℤ₂-elim a p c g ⋆ ≡ a     
    Bℤ₂-elim-⋆ a p c g = refl

    Bℤ₂-elim-loop : (a : A) (p : a ≡ a) (c : Square p refl refl p) (g : is2Groupoid A) → (cong (Bℤ₂-elim a p c g) loop) ≡ p 
    Bℤ₂-elim-loop a p c g = refl
    
    Bℤ₂-ind : (P : Bℤ₂ → Type ℓ)
        → (x : P ⋆)
        → (over-loop : PathP (λ i → P (loop i)) x x)
        → (over-square : SquareP (λ i j → P (α i j)) over-loop (λ i → x) (λ i → x) over-loop)
        → isOfHLevelDep 4 P
        → (z : Bℤ₂) → P z

    Bℤ₂-ind P x ol os h-l-dep ⋆ = x
    Bℤ₂-ind P x ol os h-l-dep (loop i) = ol i
    Bℤ₂-ind P x ol os h-l-dep (α i j) = os i j 
    Bℤ₂-ind P x ol os h-l-dep (trunc a b p q r s t u i j k l) = h-l-dep 
        (Bℤ₂-ind P x ol os h-l-dep a)
        (Bℤ₂-ind P x ol os h-l-dep b)
        (λ i → Bℤ₂-ind P x ol os h-l-dep (p i))
        (λ i → Bℤ₂-ind P x ol os h-l-dep (q i))
        (λ i j → Bℤ₂-ind P x ol os h-l-dep (r i j))
        (λ i j → Bℤ₂-ind P x ol os h-l-dep (s i j))
        (λ i j k → Bℤ₂-ind P x ol os h-l-dep (t i j k))
        (λ i j k → Bℤ₂-ind P x ol os h-l-dep (u i j k)) 
        (λ i j k l → (trunc a b p q r s t u i j k l)) 
        i j k l

    Bℤ₂-ind-prop : (P : Bℤ₂ → Type ℓ) (prop : (x : Bℤ₂) → isProp (P x))
        → (x : P ⋆)
        → (z : Bℤ₂) → P z
        
    Bℤ₂-ind-prop P prop x z = Bℤ₂-ind P x (toPathP (prop ⋆ _ _)) {!isPropDep→isSetDep ? ? ? ? ? ?!} {!!} z

    Bℤ₂-ind' : (P : Bℤ₂ → Type ℓ)
        → (x : P ⋆)
        → (over-loop : PathP (λ i → cong P loop i) x x)
        → (over-square : PathP (λ i → PathP (λ j → P (α' i j)) x x) (compPathP' {B = P} over-loop over-loop) refl)
        → isOfHLevelDep 4 P
        → (z : Bℤ₂) → P z
    Bℤ₂-ind' = {!!}

    Bℤ₂-ind-⋆ : (P : Bℤ₂ → Type ℓ) 
        → (x : P ⋆)
        → (o-l : PathP (λ i → P (loop i)) x x)
        → (o-s : SquareP (λ i j → P (α i j)) o-l (λ i → x) (λ i → x) o-l)
        → (hyp : isOfHLevelDep 4 P)
        → Bℤ₂-ind P x o-l o-s hyp ⋆ ≡ x

    Bℤ₂-ind-⋆ P x ol os hyp = refl   
            
    --{-# REWRITE Bℤ₂-ind-⋆ #-}
