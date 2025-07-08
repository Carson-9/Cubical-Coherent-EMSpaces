{-# OPTIONS --cubical --allow-unsolved-metas  #-}

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import BZ2.Delooping-Z2-Header
open import BZ2.Z2
open import BZ2.BZ2
open import Cellular.Square


open import Cellular.Dependent-Path
open import Cellular.Square


module BZ2.Delooping-Z2-Incoherent where

    postulate
        SetIs1Grp : isGroupoid (Type ℓ-zero)

    code : Bℤ₂ → Type ℓ-zero
    code = Bℤ₂-elim ℤ₂ (ℤ₂EquivPath true) (compPath→Square (sym (ℤ₂EquivPathInvolution true))) (isGroupoid→is2Groupoid SetIs1Grp)

    code-isSet : (x : Bℤ₂) → isSet (code x)
    code-isSet = Bℤ₂-ind-prop (λ x → isSet (code x)) (λ _ → isPropIsSet) ℤ₂isSet

    encode : (x : Bℤ₂) → ⋆ ≡ x → code x
    encode x p = subst code p false

    incl : code ⋆ → ⋆ ≡ ⋆
    incl zero = refl
    incl true = loop

    α-rewrite : loop ∙ loop ≡ refl ∙ refl
    α-rewrite = sym (Square→compPath α)

    α-rewrite' : loop ∙ loop ≡ refl
    α-rewrite' = α-rewrite ∙ sym (lUnit _)

    -- α-rewrite'' : sym loop ≡ loop
    -- α-rewrite'' = {!!}

    incl-is-functorial : (x y : code ⋆) → incl (x + y) ≡ incl x ∙ incl y
    incl-is-functorial zero zero = (incl (zero + zero) ≡⟨ cong incl (g+g≡zero zero) ⟩ (incl zero) ≡⟨ refl ⟩ refl ≡⟨ rUnit refl ⟩ refl ∙ refl ≡⟨ refl ⟩ (incl zero) ∙ (incl zero) ∎)
    incl-is-functorial zero true = (incl (zero + one) ≡⟨ cong incl (zero-neutral-left one) ⟩ incl one ≡⟨ refl ⟩ loop ≡⟨ lUnit loop ⟩ refl ∙ loop ≡⟨ refl ⟩ incl zero ∙ incl one ∎)
    incl-is-functorial true zero = (incl (one + zero) ≡⟨ cong incl (zero-neutral-right one) ⟩ incl one ≡⟨ refl ⟩ loop ≡⟨ rUnit loop ⟩ loop ∙ refl ≡⟨ refl ⟩ incl one ∙ incl zero ∎)
    incl-is-functorial true true = (incl (one + one) ≡⟨ cong incl (g+g≡zero zero) ⟩ (incl zero) ≡⟨ refl ⟩ refl ≡⟨ (rUnit refl) ⟩ refl ∙ refl ≡⟨ sym α-rewrite ⟩ loop ∙ loop ≡⟨ refl ⟩ (incl one) ∙ (incl one) ∎)

    -- TODO
    -- Là que ça bloque
     
    postulate
        coherence-order-2 : (x y z : code ⋆) → Square 
            (incl-is-functorial (x + y) z)
            ((cong (λ t → (incl x) ∙ t) (incl-is-functorial y z)))
            ((cong incl (+assoc x y z)) ∙ (incl-is-functorial x (y + z)))
            ((cong (λ t → t ∙ (incl z)) (incl-is-functorial x y)) ∙ (sym (assoc (incl x) (incl y) (incl z))))

     

    decode : (x : Bℤ₂) → code x → ⋆ ≡ x
    decode x = Bℤ₂-ind partial-fiber incl transpLoop transpSquare ofGoodLevel x where
        
        partial-code : Bℤ₂ → Type
        partial-code = code

        partial-loop : Bℤ₂ → Type
        partial-loop z = ⋆ ≡ z

        partial-fiber : Bℤ₂ → Type
        partial-fiber z = ((partial-code z) → (partial-loop z))

        compwiseEqual : (x : ℤ₂) → (subst partial-loop loop ∘ incl ∘ subst partial-code (sym loop)) x ≡ incl x
        compwiseEqual zero = α-rewrite'
              -- subst partial-loop loop (incl (subst partial-code (sym loop) zero)) ≡⟨ {!refl!} ⟩
              -- subst partial-loop loop (incl one) ≡⟨ refl ⟩
              -- subst partial-loop loop loop ≡⟨ refl ⟩
              -- loop ∙ loop ≡⟨ α' ⟩
              -- incl zero ∎
        compwiseEqual one  = sym (lUnit loop)
              -- subst partial-loop loop (incl (subst partial-code (sym loop) one)) ≡⟨ refl ⟩
              -- subst partial-loop loop (incl zero) ≡⟨ refl ⟩
              -- subst partial-loop loop refl ≡⟨ refl ⟩
              -- refl ∙ loop ≡⟨ sym (lUnit loop) ⟩
              -- incl one ∎


        rightCoherence : subst partial-loop loop ∘ incl ∘ subst partial-code (sym loop) ≡ incl
        rightCoherence = funExt compwiseEqual

            -- -- subst partial-loop loop (incl x) ≡ incl (subst partial-code loop x)
            -- -- incl x ∙ loop ≡ incl (swap x)
            --
            -- incl (swap x) ∙ loop ≡ incl x
            -- pour x=0 c'est α, pour x=0 c'est lunit
            --
            -- quand on double :
            -- incl x ≡ incl (swap x) ∙ loop ≡ incl (swap (swap x)) ∙ loop ∙ loop
            -- pour x=0 c'est α'∙lunit∙α yes
            -- pour x=1 c'est lunit'∙(α'∙loop)∙(loop∙α)
            --

        transpLoop : PathP (λ i → partial-fiber (loop i)) incl incl -- preuve de transp incl = incl
        transpLoop = toPathP rightCoherence

        double-path' : (x : ℤ₂) → incl x ≡ incl x
        double-path' x =
          -- incl x ≡⟨ sym (substRefl {B = partial-loop} (incl x)) ⟩
          -- subst partial-loop refl (incl x) ≡⟨ {!!} ⟩
          -- subst partial-loop (loop ∙ loop) (incl x) ≡⟨ {!!} ⟩
          -- subst partial-loop loop (subst partial-loop loop (incl x)) ≡⟨ {!!} ⟩
          incl x ≡⟨ cong {x = x} incl (sym (substRefl {B = partial-code} {x = ⋆} x)) ⟩
          --incl (subst {x = ⋆} partial-code refl x) ≡⟨ refl ⟩
          incl (subst {x = ⋆} partial-code (sym refl) x) ≡⟨ cong (λ t → incl (subst partial-code (sym t) x)) (sym α-rewrite') ⟩
          --incl (subst {x = ⋆} partial-code (sym (loop ∙ loop)) x) ≡⟨ refl ⟩
          --incl (subst {x = ⋆} partial-code (sym loop ∙ sym loop) x) ≡⟨ refl ⟩
          incl (subst {x = ⋆} partial-code (sym loop) (subst partial-code (sym loop) x)) ≡⟨ sym (substRefl {B = partial-loop} (incl (subst partial-code (sym loop) (subst partial-code (sym loop) x)))) ⟩
          subst partial-loop refl (incl (subst {x = ⋆} partial-code (sym loop) (subst partial-code (sym loop) x))) ≡⟨ cong (λ t → subst partial-loop t (incl (subst {x = ⋆} partial-code (sym loop) (subst partial-code (sym loop) x)))) (sym α-rewrite') ⟩
          subst partial-loop (loop ∙ loop) (incl (subst {x = ⋆} partial-code (sym loop) (subst partial-code (sym loop) x))) ≡⟨ substComposite partial-loop loop loop (incl (subst {x = ⋆} partial-code (sym loop) (subst partial-code (sym loop) x))) ⟩
          subst partial-loop loop (subst partial-loop loop (incl (subst partial-code (sym loop) (subst partial-code (sym loop) x)))) ≡⟨ cong (subst partial-loop loop) (compwiseEqual (subst partial-code (sym loop) x)) ⟩
          subst partial-loop loop (incl (subst partial-code (sym loop) x)) ≡⟨ compwiseEqual x ⟩
          incl x ∎

        double-path'-trivial : (x : ℤ₂) → double-path' x ≡ refl
        double-path'-trivial zero = {!   !}
        
          -- compwiseEqual (subst partial-code (sym loop) zero) ≡ sym (lUnit loop)
          -- compwiseEqual zero ≡ α-rewrite'

        double-path'-trivial true = {!  !}

        double-path : incl ≡ incl
        double-path = funExt double-path'

        double-path-trivial : double-path ≡ refl
        double-path-trivial = cong funExt (funExt double-path'-trivial)


        loop-own-inverse : loop ≡ sym loop
        loop-own-inverse = (
            loop                        ≡⟨ rUnit loop ⟩ 
            loop ∙ refl                 ≡⟨ cong (λ t → loop ∙ t) (sym (rCancel loop)) ⟩ 
            loop ∙ (loop ∙ (sym loop))  ≡⟨ assoc loop loop (sym loop) ⟩ 
            (loop ∙ loop) ∙ (sym loop)  ≡⟨ (cong (λ t → t ∙ (sym loop)) α-rewrite) ⟩
            (refl ∙ refl) ∙ (sym loop)  ≡⟨ (cong (λ t → t ∙ (sym loop)) (sym (rUnit refl))) ⟩
            refl ∙ (sym loop)           ≡⟨ sym (lUnit (sym loop)) ⟩
            sym loop ∎)

        transpSquare : SquareP (λ i j → partial-fiber (α i j)) transpLoop (λ i → incl) (λ i → incl) transpLoop
        transpSquare = final-square where

            overPathPFunct :
              ∀ {ℓ ℓ'}
              {A : Type ℓ} {B : A → Type ℓ'}
              {x y : A} {x' : B x} {y' : B y}
              (p q : x ≡ x)
              (p' : PathP (λ i → B (p i)) x' x')
              (q' : PathP (λ i → B (q i)) x' x')
              (P : x ≡ y)
              (P' : PathP (λ i → B (P i)) x' y')
              → PathP (λ i → PathP (λ j → B (overPathFunct p q P i j)) y' y')
                (transport (λ i → PathP (λ j → B (transport-filler (λ i → P i ≡ P i) (p ∙ q) i j)) (P' i) (P' i)) (compPathP' {B = B} p' q'))
                (compPathP' {B = B}
                  (transport (λ i → PathP (λ j → B (transport-filler (λ i → P i ≡ P i) p i j)) (P' i) (P' i)) p')
                  (transport (λ i → PathP (λ j → B (transport-filler (λ i → P i ≡ P i) q i j)) (P' i) (P' i)) q'))
            overPathPFunct p q = {!!}
              -- J (λ y P → transport (λ i → P i ≡ P i) (p ∙ q) ≡ transport (λ i → P i ≡ P i) p ∙ transport (λ i → P i ≡ P i) q)
              -- (transportRefl (p ∙ q) ∙ cong₂ _∙_ (sym (transportRefl p)) (sym (transportRefl q)))

            overPathPFunct' :
              ∀ {ℓ ℓ'}
              {A : Type ℓ} {B : A → Type ℓ'}
              {x : A} {x' : B x}
              (p q : x ≡ x)
              (p' : PathP (λ i → B (p i)) x' x')
              (q' : PathP (λ i → B (q i)) x' x')
              →
              PathP
                (λ i → PathP (λ j → B (overPathFunct p q refl i j)) x' x')
                (transport (λ i → PathP (λ j → B (transport-filler (λ i → x ≡ x) (p ∙ q) i j)) x' x') (compPathP' {B = B} p' q'))
                (compPathP' {B = B}
                  (transport (λ i → PathP (λ j → B (transport-filler (λ i → x ≡ x) p i j)) x' x') p')
                  (transport (λ i → PathP (λ j → B (transport-filler (λ i → x ≡ x) q i j)) x' x') q'))
            overPathPFunct' {B = B} p q p' q' = overPathPFunct {B = B} p q p' q' refl refl

            -- test : PathP (λ i → PathP (λ j → partial-fiber (α-rewrite'' i j)) incl incl) (symP transpLoop) transpLoop
            -- test = cong toPathP {!funExt ?!}
              -- where
              -- lem : {!(x : ℤ₂) → ?!}

            -- PathP
              -- (λ i → PathP (λ j → partial-fiber (α-rewrite'' i j)) incl incl)
              -- (symP transpLoop) transpLoop

            core-proof : PathP (λ i → PathP (λ j → partial-fiber (α-rewrite' i j)) incl incl) (compPathP' {B = partial-fiber} transpLoop transpLoop) refl
            core-proof = toPathP (compPathP' {B = {!!}}
              (overPathPFunct' {A = Bℤ₂} {B = partial-fiber} {x = ⋆} {x' = incl} loop loop transpLoop transpLoop)
              {!!}
              )
              -- where
              -- lem : transport (λ i → PathP (λ j → partial-fiber (α-rewrite' i j)) incl incl) (compPathP' {B = partial-fiber} transpLoop transpLoop) ≡ {!!}

              -- transport (λ i → PathP (λ j → partial-fiber (α-rewrite i j)) incl incl) transpLoop
              -- transport (λ i → PathP (λ j → partial-fiber ((sym (lUnit _ )  i j)) incl incl)) transpLoop


            --test : PathP (λ i → ?) transpLoop (symP transpLoop)
            --test = cong (λ t → transport (λ i → partial-fiber (t i)) incl incl) loop-own-inverse

            lid-glue : dep-doublecomp (λ i j → partial-fiber (α i j)) (symP transpLoop) refl refl ≡ transpLoop
            lid-glue = {!   !}
    
            final-square : SquareP (λ i j → partial-fiber (α i j)) transpLoop (λ i → incl) (λ i → incl) transpLoop
            final-square = toSquareP' transpLoop (λ i → incl) (λ i → incl) transpLoop ?


        ofGoodLevel : isOfHLevelDep 4 partial-fiber
        ofGoodLevel = {! !}




    enc∘dec≡Id : (x : Bℤ₂) → (c : code x) → encode x (decode x c) ≡ c
    enc∘dec≡Id = Bℤ₂-ind proofType proofOnℤ₂ pathOver squareOver ofGoodLevel where

        proofType : Bℤ₂ → Type
        proofType x =  (c : code x) → encode x (decode x c) ≡ c

        proofOnℤ₂ : (z : ℤ₂) → encode ⋆ (decode ⋆ z) ≡ z
        proofOnℤ₂ zero = cong {A = ⋆ ≡ ⋆} {x = decode ⋆ zero} {y = incl zero} (λ t → encode ⋆ t) refl
        proofOnℤ₂ true = cong {A = ⋆ ≡ ⋆} {x = decode ⋆ one} {y = incl one} (λ t → encode ⋆ t) refl 


        pathOver : PathP (λ i → proofType (loop i)) proofOnℤ₂ proofOnℤ₂
        pathOver = toPathP (funExt compwiseEqual)  where 
            compwiseEqual : (c : ℤ₂) → (transport (λ i → proofType (loop i)) (proofOnℤ₂)) c ≡ proofOnℤ₂ c
            compwiseEqual c = ℤ₂isSet _ _ ((transport (λ i → proofType (loop i)) (proofOnℤ₂)) c) (proofOnℤ₂ c)


        squareOver : SquareP (λ i j → proofType (α i j)) pathOver (λ i → proofOnℤ₂) (λ i → proofOnℤ₂) pathOver
        squareOver = isPropDep→isSetDep' {B = proofType} (isOfHLevel→isOfHLevelDep 1 (λ n → isPropΠ λ _ → code-isSet n _ _)) α pathOver (λ i → proofOnℤ₂) (λ i → proofOnℤ₂) pathOver

        ofGoodLevel : isOfHLevelDep 4 proofType
        ofGoodLevel = {!   !}
                
                {-
                isOfHLevelDepSuc 3 (isOfHLevelDepSuc 2 (isOfHLevelDepSuc 1 propProof)) where
                propProof : isOfHLevelDep 1 proofType
                propProof a b p = {! toPathP transpOfProp !} where

                    transpOfProp : transport (λ i → proofType (p i)) a ≡ b
                    transpOfProp = funExt compwiseEqual where 
                        compwiseEqual : (c : ℤ₂) → (transport (λ i → proofType (p i)) (a)) c ≡ b c
                        compwiseEqual c = ℤ₂isSet _ _ ((transport (λ i → proofType (p i)) (a)) c) (b c)
                -}

                        
    dec∘enc≡Id : (x : Bℤ₂) → (p : ⋆ ≡ x) → decode x (encode x p) ≡ p
    dec∘enc≡Id x = J (λ y q → decode y (encode y q) ≡ q) (
        decode ⋆ (encode ⋆ refl)    ≡⟨ cong (λ t → decode ⋆ t) (subComp) ⟩            
        decode ⋆ zero               ≡⟨ refl ⟩
        refl ∎) where
        
        subComp : encode ⋆ refl ≡ zero
        subComp = refl


    ΩBℤ₂ : Type
    ΩBℤ₂ = (⋆ ≡ ⋆)

    ΩBℤ₂≡ℤ₂ : ΩBℤ₂ ≡ ℤ₂
    ΩBℤ₂≡ℤ₂ = isoToPath (iso enc dec lInv rInv) where
        
        enc : ΩBℤ₂ → ℤ₂
        enc p = encode ⋆ p

        dec : ℤ₂ → ΩBℤ₂
        dec c = decode ⋆ c

        lInv : section enc dec
        lInv = enc∘dec≡Id ⋆

        rInv : retract enc dec
        rInv = dec∘enc≡Id ⋆
