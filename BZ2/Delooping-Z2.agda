-- Facts about the EM-model for Bℤ₂

{-# OPTIONS --cubical --allow-unsolved-metas #-}


module BZ2.Delooping-Z2 where

    open import BZ2.Delooping-Z2-Header public
    open import BZ2.Delooping-Z2-Def public


    ℤ₂EquivFun : ℤ₂ → ℤ₂ ≡ ℤ₂
    ℤ₂EquivFun g = isoToPath (iso f inv rInv lInv) where
            
        f : ℤ₂ → ℤ₂
        f x = g + x

        inv : ℤ₂ → ℤ₂       -- Sur ℤ₂
        inv x = g + x        

        rInv : section f inv
        rInv zero = (
            f (inv zero)
            ≡⟨ sym (+assoc g g zero) ⟩
            (g + g) + zero
            ≡⟨ cong (λ x → x + zero) (g+g≡zero g) ⟩
            zero + zero ∎
            ) 
        rInv one = (
            f (inv one)
            ≡⟨ sym (+assoc g g one) ⟩
            (g + g) + one
            ≡⟨ cong (λ x → x + one) (g+g≡zero g) ⟩
            zero + one ∎
            )

        lInv : retract f inv
        lInv = rInv



    code : Bℤ₂ → Type
    
    code ⋆ = ℤ₂
    code (loop i) = (ℤ₂EquivFun one) i
    code (α i i₁) = {!   !} --{!   !} code(loop ∙ loop) = λ x → 1 + 1 + x ≡ (1 + 1) + x ≡ x 
    code (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) = {!   !} -- ℤ₂ est un 1Groupoide (en tant que set)

    encode : (z : Bℤ₂) → (⋆ ≡ z) → (code z)
    encode x p = subst code p zero 

    decode : (z : Bℤ₂) → (code z) → (⋆ ≡ z)
    decode ⋆ = incl where 
        incl : ℤ₂ → (⋆ ≡ ⋆) 
        incl zero = refl 
        incl one = loop

    decode (loop i) = {!   !} {-

        transp (λ x ↦ code(x) → (⋆ ≡ x)) (loop, incl) ≡ incl
        transp (λ x ↦ (⋆ ≡ x)) (loop) ∘ incl ∘ transp (λ x → code(x)) (loop ⁻¹)
        (— ∙ loop) ∘ incl ∘ ((λ x ↦ (-1) + x))
        λ x ↦ (incl(-1 + x) ∙ loop)
        λ x ↦ (incl(x) ∙ loop ∙ loop) // Prop d'inversion de incl, 
                                        // évidente ici par commutativité sinon postulat de finster likata
        λ x ↦ incl x
        incl
        -}

    decode (α i i₁) = {!   !} -- ℤ₂ est un groupe
    decode (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) = {!   !} -- ℤ₂ est un groupe


    enc∘dec≡id : (x : Bℤ₂) → (c : code x) → encode x (decode x c) ≡ c
    enc∘dec≡id ⋆ zero = refl
    enc∘dec≡id ⋆ true = refl  
    enc∘dec≡id (loop i) c = {!   !}
    enc∘dec≡id (α i i₁) c = {!   !} -- ℤ₂ est un set
    enc∘dec≡id (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) c = {!   !} -- ℤ₂ est un set

    dec∘enc≡id : {x : Bℤ₂} → (p : ⋆ ≡ x) → decode x (encode x p) ≡ p
    dec∘enc≡id p = (J (λ x p → decode x (encode x p) ≡ p) refl) p

    ΩBℤ₂≡ℤ₂ : ΩBℤ₂ ≡ ℤ₂
    ΩBℤ₂≡ℤ₂ = isoToPath (iso fibEquiv inv sec ret) where 
        fibEquiv : ΩBℤ₂ → ℤ₂
        fibEquiv p = encode ⋆ p

        inv : ℤ₂ → ΩBℤ₂
        inv x = decode ⋆ x

        sec : section fibEquiv inv
        sec x = enc∘dec≡id ⋆ x

        ret : retract fibEquiv inv
        ret p = dec∘enc≡id p
