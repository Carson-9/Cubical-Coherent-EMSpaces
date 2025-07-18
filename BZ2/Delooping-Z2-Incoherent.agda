{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import BZ2.Delooping-Z2-Header
open import BZ2.Z2
open import BZ2.B2Z2


open import Cellular.Square
open import Cellular.Dependent-Path
open import Cellular.Path-Properties


module BZ2.Delooping-Z2-Incoherent where

    
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


        -- ce truc c'est l'égalité entre incl x (à droite) et incl (swap x) ∙ loop (à gauche)
        rightCoherence : subst partial-loop loop ∘ incl ∘ subst partial-code (sym loop) ≡ incl
        rightCoherence = funExt compwiseEqual

            -- -- subst partial-loop loop (incl x) ≡ incl (subst partial-code loop x)
            -- -- incl x ∙ loop ≡ incl (swap x)
            --
            -- incl (swap x) ∙ loop ≡ incl x
            -- pour x=0 c'est α, pour x=0 c'est lunit
            --
            -- quand on double :
            -- on vuet montrer que le chemin composé incl x ≡ incl (swap x) ∙ loop ≡ incl (swap (swap x)) ∙ loop ∙ loop est "refl"
            --
            -- pour x=0 c'est r ≡α⁻ l∙l ≡[lunit] r∙l∙l (c'est-à-dire α⁻∙lunit∙α⁻ = refl => yes)
            --    
            -- pour x=1 c'est loop ≡[lunit] refl ∙ loop ≡[α⁻∙loop] loop ∙ loop ∙ loop ≡[loop∙α] loop (c'est-à-dire lunit'∙(α'∙loop)∙(loop∙α') = refl => yes)
            --

        transpLoop : PathP (λ i → partial-fiber (loop i)) incl incl -- preuve de transp incl = incl
        transpLoop = toPathP rightCoherence


        double-path' : (x : ℤ₂) → incl x ≡ incl x
        double-path' x ={- 
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
          incl x ∎ -}

          (cong {x = x} incl (sym (substRefl {B = partial-code} {x = ⋆} x))) ∙
          (cong (λ t → incl (subst partial-code (sym t) x)) (sym α-rewrite')) ∙
          (sym (substRefl {B = partial-loop} (incl (subst partial-code (sym loop) (subst partial-code (sym loop) x))))) ∙
          (cong (λ t → subst partial-loop t (incl (subst {x = ⋆} partial-code (sym loop) (subst partial-code (sym loop) x)))) (sym α-rewrite')) ∙
          -- Ici : subst pl (loop loop) (incl (subst pc (loop loop) x))
          (substComposite partial-loop loop loop (incl (subst {x = ⋆} partial-code (sym loop) (subst partial-code (sym loop) x)))) ∙
          (cong (subst partial-loop loop) (compwiseEqual (subst partial-code (sym loop) x))) ∙
          (compwiseEqual x)


        double-path'-trivial : (x : ℤ₂) → double-path' x ≡ refl {x = incl x}
        double-path'-trivial zero =
            cong {x = zero} incl (sym (substRefl {B = partial-code} {x = ⋆} zero)) ∙
            cong (λ t → incl (subst partial-code (sym t) zero)) (sym α-rewrite') ∙
            sym (substRefl {B = partial-loop} (incl (subst partial-code (sym loop) (subst partial-code (sym loop) zero)))) ∙
            cong (λ t → subst partial-loop t (incl (subst {x = ⋆} partial-code (sym loop) (subst partial-code (sym loop) zero)))) (sym α-rewrite') ∙ 
            substComposite partial-loop loop loop (incl (subst {x = ⋆} partial-code (sym loop) (subst partial-code (sym loop) zero))) ∙ 
            cong (subst partial-loop loop) (compwiseEqual (subst partial-code (sym loop) zero)) ∙ compwiseEqual zero 
          ≡⟨ refl ⟩
            cong {x = zero} incl (sym (substRefl {B = partial-code} {x = ⋆} zero)) ∙ 
            cong (λ t → incl (subst partial-code (sym t) zero)) (sym α-rewrite') ∙ 
            sym (substRefl {B = partial-loop} refl) ∙ 
            cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
            substComposite partial-loop loop loop refl ∙ 
            cong (subst partial-loop loop) (sym (lUnit loop)) ∙ α-rewrite'
          ≡⟨ (cong (λ t → t ∙ cong (λ t → incl (subst partial-code (sym t) zero)) (sym α-rewrite') ∙ 
              sym (substRefl {B = partial-loop} refl) ∙ 
              cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
              substComposite partial-loop loop loop refl ∙ 
              cong (subst partial-loop loop) (sym (lUnit loop)) ∙ α-rewrite') lem1) ∙ (sym (lUnit (cong (λ t → incl (subst partial-code (sym t) zero)) (sym α-rewrite') ∙ 
                sym (substRefl {B = partial-loop} refl) ∙ 
              cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
              substComposite partial-loop loop loop refl ∙ 
              cong (subst partial-loop loop) (sym (lUnit loop)) ∙ α-rewrite')))  ⟩ -- lem1
            
            cong (λ t → incl (subst partial-code (sym t) zero)) (sym α-rewrite') ∙ 
            sym (substRefl {B = partial-loop} refl) ∙ 
            cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
            substComposite partial-loop loop loop refl ∙ 
            cong (subst partial-loop loop) (sym (lUnit loop)) ∙ α-rewrite'
          ≡⟨ (cong (λ t → t ∙ sym (substRefl {B = partial-loop} refl) ∙ 
              cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
              substComposite partial-loop loop loop refl ∙ 
              cong (subst partial-loop loop) (sym (lUnit loop)) ∙
              α-rewrite') lem2) ∙ (sym (lUnit (sym (substRefl {B = partial-loop} refl) ∙ 
                cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
                substComposite partial-loop loop loop refl ∙ 
                cong (subst partial-loop loop) (sym (lUnit loop)) ∙
                α-rewrite'))) ⟩ -- lem2
            
            sym (substRefl {B = partial-loop} refl) ∙ 
            cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
            substComposite partial-loop loop loop refl ∙ 
            cong (subst partial-loop loop) (sym (lUnit loop)) ∙
            α-rewrite'
          ≡⟨ cong (λ t → t ∙ cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
              substComposite partial-loop loop loop refl ∙ 
              cong (subst partial-loop loop) (sym (lUnit loop)) ∙
              α-rewrite') lem3 ⟩ -- lem3
            
            lUnit _ ∙ 
            cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
            substComposite partial-loop loop loop refl ∙ 
            cong (subst partial-loop loop) (sym (lUnit loop)) ∙
            α-rewrite'
          ≡⟨ cong (λ t → lUnit _ ∙ 
                  cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ t ∙ cong (subst partial-loop loop) (sym (lUnit loop)) ∙
                  α-rewrite') lem4 ⟩ -- lem4
            
            lUnit _ ∙ 
            cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
            assoc _ _ _ ∙ 
            cong (subst partial-loop loop) (sym (lUnit loop)) ∙
            α-rewrite'
          ≡⟨ cong (λ t → lUnit _ ∙ 
                cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
                assoc _ _ _ ∙ t ∙ α-rewrite') lem5 ⟩ -- lem5
            
            lUnit _ ∙ 
            cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
            assoc _ _ _ ∙ 
            sym (lUnit _ ∙ assoc _ _ _) ∙
            α-rewrite'
          ≡⟨ (cong  (λ t → lUnit _ ∙ 
                cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
                assoc _ _ _ ∙ t ∙ α-rewrite') (symDistr (lUnit _) (assoc _ _ _))) ∙ 
                {! (cong (λ t → lUnit _ ∙ 
                        cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
                        assoc _ _ _ ∙ t ) (sym (assoc (sym assoc _ _ _) (sym (lUnit _) (α-rewrite'))))) !} ⟩
            
            lUnit _ ∙ 
            cong (λ t → subst partial-loop t refl) (sym α-rewrite') ∙ 
            assoc _ _ _ ∙ 
            sym (assoc _ _ _) ∙ sym (lUnit _) ∙
            α-rewrite'
          ≡⟨ (cong _ (rCancel (assoc _ _ _) )) ∙ (cong _ (lUnit (sym (lUnit _)))) ⟩ -- subst partial-loop...
            lUnit _ ∙ 
            cong (λ t → refl ∙ t) (sym α-rewrite') ∙ 
            sym (lUnit _) ∙
            α-rewrite'
          ≡⟨ cong _ (lUnit-nat (sym α-rewrite')) ⟩ -- lUnit-nat
            sym α-rewrite' ∙
            lUnit _ ∙
            sym (lUnit _) ∙
            α-rewrite'
          ≡⟨ cong _ (rCancel (lUnit _)) ⟩
            sym α-rewrite' ∙
            α-rewrite'
          ≡⟨ lCancel _ ⟩
          refl ∎ 
          
          where
          lem1 : cong {x = zero} incl (sym (substRefl {B = partial-code} {x = ⋆} zero)) ≡ refl
          lem1 =
            cong {x = zero} incl (sym (substRefl {B = partial-code} {x = ⋆} zero)) ≡⟨ refl ⟩
            sym (cong {x = zero} incl (substRefl {B = partial-code} {x = ⋆} zero)) ≡⟨ refl ⟩
            sym (cong {x = zero} incl refl) ≡⟨ refl ⟩
            refl ∎

          lem2' : (t : ⋆ ≡ ⋆) → incl (subst partial-code (sym t) zero) ≡ t
          lem2' t = {!!}

          lem2 : cong (λ t → incl (subst partial-code (sym t) zero)) (sym α-rewrite') ≡ refl
          lem2 =
            cong (λ t → incl (subst partial-code (sym t) zero)) (sym α-rewrite') ≡⟨ refl ⟩
            sym (cong (λ t → incl (subst partial-code (sym t) zero)) α-rewrite') ≡⟨ {!!} ⟩ -- lem2'
            sym (cong (λ t → {!t!}) α-rewrite') ≡⟨ {!!} ⟩            
            refl ∎

          lem3 : sym (substRefl {B = partial-loop} refl) ≡ lUnit _
          lem3 = refl

          lem4 : substComposite partial-loop loop loop refl ≡ assoc _ _ _
          lem4 = refl

          -- lem5' : subst partial-loop loop (refl ∙ loop) ≡ subst partial-loop loop loop
          lem5' : (refl ∙ loop) ∙ loop ≡ loop ∙ loop          
          lem5' = sym (lUnit _ ∙ assoc _ _ _)

          lem5 : cong (subst partial-loop loop) (sym (lUnit loop)) ≡ sym (lUnit _ ∙ assoc _ _ _) -- lem5'
          lem5 =
            cong (subst partial-loop loop) (sym (lUnit loop)) ≡⟨ refl ⟩
            sym (cong (subst partial-loop loop) (lUnit loop)) ≡⟨ cong sym {!!} ⟩
            sym (cong (λ p → p ∙ loop) (lUnit loop)) ≡⟨ {!!} ⟩
            lem5' ∎

          lUnit-nat : ∀ {ℓ} {A : Type ℓ} {x y : A} {p q : x ≡ y} (P : p ≡ q) → P ∙ lUnit q ≡ lUnit p ∙ cong (λ p → refl ∙ p) P
          lUnit-nat {p = p} {q = q} P = J (λ q P → P ∙ lUnit q ≡ lUnit p ∙ cong (λ p → refl ∙ p) P) (sym (lUnit (lUnit p)) ∙ {!!}) P -- rUnit / assoc



        double-path'-trivial true = {!   !} {- 
            cong {x = one} incl (sym (substRefl {B = partial-code} {x = ⋆} one)) ∙
            cong (λ t → incl (subst partial-code (sym t) one)) (sym α-rewrite') ∙
            sym (substRefl {B = partial-loop} (incl (subst partial-code (sym loop) (subst partial-code (sym loop) one)))) ∙
            cong (λ t → subst partial-loop t (incl (subst {x = ⋆} partial-code (sym loop) (subst partial-code (sym loop) one)))) (sym α-rewrite') ∙ 
            substComposite partial-loop loop loop (incl (subst {x = ⋆} partial-code (sym loop) (subst partial-code (sym loop) one))) ∙ 
            cong (subst partial-loop loop) (compwiseEqual (subst partial-code (sym loop) one)) ∙ compwiseEqual one 
          ≡⟨ refl ⟩
            cong {x = one} incl (sym (substRefl {B = partial-code} {x = ⋆} one)) ∙
            cong (λ t → incl (subst partial-code (sym t) one)) (sym α-rewrite') ∙
            sym (substRefl {B = partial-loop} (loop)) ∙
            cong (λ t → subst partial-loop t (loop)) (sym α-rewrite') ∙ 
            substComposite partial-loop loop loop (loop) ∙ 
            cong (subst partial-loop loop) (α-rewrite') ∙ (sym (lUnit loop)) 
          ≡⟨ {!!} ⟩
            cong {x = one} incl (sym (substRefl {B = partial-code} {x = ⋆} one)) ∙
            cong (λ t → incl (subst partial-code (sym t) one)) (sym α-rewrite') ∙
            sym (substRefl {B = partial-loop} (loop)) ∙
            cong (λ t → subst partial-loop t (loop)) (sym α-rewrite') ∙ 
            substComposite partial-loop loop loop (loop) ∙ 
            cong (subst partial-loop loop) (α-rewrite') ∙ (sym (lUnit loop)) 
          ≡⟨ {!   !} ⟩
          refl ∎ -}

        double-path : incl ≡ incl
        double-path = funExt double-path'

        double-path-trivial : double-path ≡ refl
        double-path-trivial = cong funExt (funExt double-path'-trivial)

        transpSquare : SquareP (λ i j → partial-fiber (α i j)) transpLoop (λ _ → incl) (λ _ → incl) transpLoop
        transpSquare = SquareP'-to-SquareP {B = partial-fiber} (SquareP'-from-comp-equality  
          {B = partial-fiber} {glue-a = (sym α'-complete)} 
          transpLoop 
          refl 
          refl 
          transpLoop 
          glue-compositions) where

            double-transport : subst partial-fiber (loop ∙ loop) incl ≡ incl
            double-transport = 
                (substComposite partial-fiber loop loop incl) ∙ 
                (cong (subst partial-fiber loop) rightCoherence) ∙ 
                (rightCoherence)


            double-transport-with-coherence : subst partial-fiber (loop ∙ loop) incl ≡ incl
            double-transport-with-coherence = 
                (cong (λ t → subst partial-fiber t incl) (α-rewrite')) ∙ 
                (substRefl {B = partial-fiber} incl)

            double-transport-is-trivial : double-transport ≡ double-transport-with-coherence
            double-transport-is-trivial = {!   !} where
              double-path'' : sym (double-transport-with-coherence) ∙ double-transport ≡ refl
              double-path'' = {! double-path-trivial  !}


            -- Inutile, sera plus utile dans l'autre sens !
            top-comp : PathP (λ i → partial-fiber ((loop ∙ loop) i)) incl incl
            top-comp = compPathP' {B = partial-fiber} transpLoop transpLoop
            
            top-comp' : PathP (λ i → partial-fiber ((loop ∙ loop) i)) incl incl
            top-comp' = toPathP (double-transport)
            
            refl-path-transport : PathP (λ i → PathP (λ j → partial-fiber (α'-complete i j)) incl incl) 
                                    (toPathP double-transport-with-coherence)
                                    (compPathP' {B = partial-fiber} (refl {x = incl}) (refl {x = incl}))
            refl-path-transport = toPathP ({!   !}) 

            top-path : top-comp ≡ top-comp'
            top-path = compPathP-transpComp' {B = partial-fiber} {x' = incl} {p = loop} {q = loop}  rightCoherence rightCoherence


            glue-compositions : PathP (λ i → PathP (λ j → partial-fiber (sym (α'-complete) i j)) incl incl) 
              (compPathP' {B = partial-fiber} (refl {x = incl}) (refl {x = incl}))
              (compPathP' {B = partial-fiber} transpLoop transpLoop)
            glue-compositions = {!   !}


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
