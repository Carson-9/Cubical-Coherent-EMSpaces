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

module BZ2.Delooping-Z2 where


    decode : (x : Bℤ₂) → code x → ⋆ ≡ x
    decode x = Bℤ₂-ind partial-fiber incl inclP inclFunP ofGoodLevel x where
        
        partial-code : Bℤ₂ → Type
        partial-code = code

        partial-loop : Bℤ₂ → Type
        partial-loop z = ⋆ ≡ z

        partial-fiber : Bℤ₂ → Type
        partial-fiber z = ((partial-code z) → (partial-loop z))

        inclP-subst-compwise : (x : ℤ₂) → subst partial-fiber loop incl x ≡ incl x
        inclP-subst-compwise zero = α-rewrite'
        inclP-subst-compwise true = sym (lUnit loop)

        inclP-subst : subst partial-fiber loop incl  ≡ incl 
        inclP-subst = funExt inclP-subst-compwise
        
        inclP : PathP (λ i → partial-fiber (loop i)) incl incl
        inclP = toPathP inclP-subst


        inclFunP : SquareP' partial-fiber α inclP refl refl inclP
        inclFunP = SquareP'-replace-base-square {B = partial-fiber} total-square α-conversion where


            -- INVALIDE : On doit intuitivement rewrite en subst partial-loop (incl (partial-code ...)
            
            inclP-over-doubleloop : subst partial-fiber (loop ∙ loop) incl ≡ incl
            inclP-over-doubleloop = 
                (substComposite partial-fiber loop loop incl) ∙
                (cong (subst partial-fiber loop) inclP-subst) ∙
                inclP-subst

            inclP-over-functorial : subst partial-fiber (loop ∙ loop) incl ≡ incl
            inclP-over-functorial = 
                (cong (λ t → subst partial-fiber t incl) α-rewrite') ∙
                (substRefl {B = partial-fiber} incl)

            inclP-over-functorial' : subst partial-fiber (loop ∙ loop) incl ≡ incl
            inclP-over-functorial' = 
                (cong (λ t → subst partial-fiber t incl) (α'-complete)) ∙
                (substComposite partial-fiber refl refl incl) ∙
                (cong (subst partial-fiber refl) (substRefl {B = partial-fiber} incl)) ∙
                (substRefl {B = partial-fiber} incl)

            -----------------------------------------------------------------------------------------

            inclP-over-doubleloop-compwise : (x : ℤ₂) → subst partial-fiber (loop ∙ loop) incl x ≡ incl x
            inclP-over-doubleloop-compwise x = 
                
                (substComposite partial-loop loop loop (incl (subst partial-code (sym loop) (subst partial-code (sym loop) x)))) ∙
                (cong (subst partial-loop loop) (inclP-subst-compwise (subst partial-code (sym loop) x))) ∙
                (inclP-subst-compwise x)
                

                -- subst partial-loop (loop ∙ loop) (incl (subst partial-code (sym loop) (subst partial-code (sym loop) x)))
                -- ≡⟨ substComposite partial-loop loop loop (incl (subst partial-code (sym loop) (subst partial-code (sym loop) x))) ⟩
                -- subst partial-loop loop (subst partial-loop loop (incl (subst partial-code (sym loop) (subst partial-code (sym loop) x))))
                -- ≡⟨ cong (subst partial-loop loop) (inclP-subst-compwise (subst partial-code (sym loop) x)) ⟩
                -- subst partial-loop loop (incl (subst partial-code loop x))
                -- ≡⟨ inclP-subst-compwise x ⟩
                -- incl x ∎

            inclP-over-functorial-compwise : (x : ℤ₂) → subst partial-fiber (loop ∙ loop) incl x ≡ incl x
            inclP-over-functorial-compwise x = 
                
                (cong (λ t → subst partial-loop (loop ∙ loop) (incl (subst partial-code (sym t) x))) (α-rewrite')) ∙
                (cong (λ t → subst partial-loop t (incl x)) (α-rewrite')) ∙
                (substRefl {B = partial-loop} (incl x))
                
                
                -- subst partial-loop (loop ∙ loop) (incl (subst partial-code (sym (loop ∙ loop)) x))
                -- ≡⟨ cong (λ t → subst partial-loop (loop ∙ loop) (incl (subst partial-code (sym t) x))) (α-rewrite') ⟩
                -- subst partial-loop (loop ∙ loop) (incl x)
                -- ≡⟨ cong (λ t → subst partial-loop t (incl x)) (α-rewrite') ⟩
                -- subst partial-loop refl (incl x)
                -- ≡⟨ substRefl {B = partial-loop} (incl x) ⟩
                -- incl x ∎
                
                --(cong (λ t → subst partial-fiber t incl x) α-rewrite') ∙
                --(cong (λ t → t x) (substRefl {B = partial-fiber} incl)) 


            inclP-over-functorial-compwise' : (x : ℤ₂) → subst partial-fiber (loop ∙ loop) incl x ≡ incl x
            inclP-over-functorial-compwise' x = 
                

                (cong (λ t → subst partial-loop t (incl (subst partial-code t x))) (α'-complete ∙ (sym (lUnit refl)))) ∙
                (substRefl {B = partial-loop} (incl (subst partial-code refl x))) ∙              
                (cong incl (substRefl {B = partial-code} x))

                ----subst partial-fiber (loop ∙ loop) incl x
                ----≡⟨ refl ⟩
                --subst partial-loop (loop ∙ loop) (incl (subst partial-code (loop ∙ loop) x))
                --≡⟨ cong (λ t → subst partial-loop t (incl (subst partial-code t x))) (α'-complete ∙ (sym (lUnit refl))) ⟩                
                --subst partial-loop refl (incl (subst partial-code refl x))
                --≡⟨ substRefl {B = partial-loop} (incl (subst partial-code refl x)) ⟩
                --(incl (subst partial-code refl x))
                --≡⟨ cong incl (substRefl {B = partial-code} x) ⟩ 
                --incl x ∎



            2-coherence : inclP-over-doubleloop ≡ inclP-over-functorial
            2-coherence = total-glue where

                
                glue-compwise : (x : ℤ₂) → (inclP-over-doubleloop-compwise) x ≡ (inclP-over-functorial-compwise) x
                glue-compwise zero = reduce-left ∙ (sym reduce-right) where

                        step-1 : (substComposite partial-loop loop loop refl) ≡ assoc refl loop loop
                        step-1 = refl

                        step-2 : (cong (subst partial-loop loop) (sym (lUnit loop))) ≡ (sym (assoc refl loop loop)) ∙ (sym (lUnit (loop ∙ loop)))
                        step-2 = 
                            (cong (subst partial-loop loop) (sym (lUnit loop)) ≡⟨ refl ⟩
                            sym (cong (subst partial-loop loop) (lUnit loop)) ≡⟨ cong sym {!   !} ⟩
                            sym (lUnit (loop ∙ loop) ∙ assoc refl loop loop) ∎)
                            ∙ (symDistr (lUnit (loop ∙ loop)) (assoc refl loop loop))


                        step-3 : (substRefl {B = partial-loop} refl) ≡ sym (lUnit refl)
                        step-3 = refl

                        step-4' : (cong (λ t → subst partial-loop t refl) (α-rewrite')) ≡ sym (lUnit (loop ∙ loop)) ∙ α-rewrite' ∙ (lUnit refl)
                        step-4' = {! refl  !}

                        step-4 : (cong (λ t → subst partial-loop t refl) (α-rewrite')) ∙ (substRefl {B = partial-loop} refl)  ≡ sym (lUnit (loop ∙ loop)) ∙ α-rewrite'
                        step-4 = {!   !}

                        step-5' : (t : ⋆ ≡ ⋆) → (incl (subst partial-code (sym t) zero)) ≡ t
                        step-5' = {!   !}

                        step-5 : (cong (λ t → subst partial-loop (loop ∙ loop) (incl (subst partial-code (sym t) zero))) (α-rewrite')) ≡ refl
                        step-5 = {!   !}
                            -- ( 
                            -- (cong (λ t → subst partial-loop (loop ∙ loop) (incl (subst partial-code (sym t) zero))) (α-rewrite')) 
                            -- ≡⟨ ? ⟩
                            -- (cong (λ t → subst partial-loop (loop ∙ loop) t) (α-rewrite'))
                            -- ≡⟨ ? ⟩
                            -- (refl) ∎ )

                        reduce-left : inclP-over-doubleloop-compwise zero ≡ (sym (lUnit (loop ∙ loop))) ∙ α-rewrite'
                        reduce-left = 
                            (substComposite partial-loop loop loop refl) ∙
                            (cong (subst partial-loop loop) (sym (lUnit loop))) ∙
                            α-rewrite'
                            ≡⟨ cong (λ t → t ∙ (cong (subst partial-loop loop) (sym (lUnit loop))) ∙ α-rewrite') step-1 ⟩

                            (assoc refl loop loop) ∙
                            (cong (subst partial-loop loop) (sym (lUnit loop))) ∙
                            α-rewrite'
                            ≡⟨ cong (λ t →  (assoc refl loop loop) ∙ t ∙ α-rewrite') step-2 ⟩

                            (assoc refl loop loop) ∙
                            ((sym (assoc refl loop loop)) ∙ (sym (lUnit (loop ∙ loop)))) ∙
                            α-rewrite'
                            ≡⟨ (assoc (assoc refl loop loop) ((sym (assoc refl loop loop)) ∙ (sym (lUnit (loop ∙ loop)))) (α-rewrite')) ∙
                                (cong (λ t → t ∙ α-rewrite') (assoc (assoc refl loop loop) (sym (assoc refl loop loop)) (sym (lUnit (loop ∙ loop))))) ⟩

                            ( ((assoc refl loop loop) ∙ (sym (assoc refl loop loop))) ∙ (sym (lUnit (loop ∙ loop))) ) ∙ 
                            α-rewrite'
                            ≡⟨ (cong (λ t → (t ∙ (sym (lUnit (loop ∙ loop)))) ∙ α-rewrite') (rCancel (assoc refl loop loop))) ⟩

                            (refl ∙ (sym (lUnit (loop ∙ loop)))) ∙
                            α-rewrite'
                            ≡⟨ (cong (λ t → t ∙ α-rewrite') (sym (lUnit (sym (lUnit (loop ∙ loop)))))) ⟩

                            (sym (lUnit (loop ∙ loop))) ∙
                            α-rewrite' ∎

                        reduce-right : inclP-over-functorial-compwise zero ≡ (sym (lUnit (loop ∙ loop))) ∙ α-rewrite'
                        reduce-right = 
                            (cong (λ t → subst partial-loop (loop ∙ loop) (incl (subst partial-code (sym t) zero))) (α-rewrite')) ∙
                            (cong (λ t → subst partial-loop t refl) (α-rewrite')) ∙
                            (substRefl {B = partial-loop} refl)
                            ≡⟨ (cong (λ t → t ∙ 
                                               (cong (λ t' → subst partial-loop t' refl) (α-rewrite')) ∙
                                               (substRefl {B = partial-loop} refl)) step-5) ⟩

                            refl ∙
                            (cong (λ t → subst partial-loop t refl) (α-rewrite')) ∙
                            (substRefl {B = partial-loop} refl)
                            ≡⟨ (assoc refl (cong (λ t → subst partial-loop t refl) (α-rewrite')) (substRefl {B = partial-loop} refl))
                                ∙ (cong (λ t → t ∙ (substRefl {B = partial-loop} refl)) (sym (lUnit (cong (λ t → subst partial-loop t refl) (α-rewrite'))))) ⟩

                            (cong (λ t → subst partial-loop t refl) (α-rewrite')) ∙
                            (substRefl {B = partial-loop} refl)
                            ≡⟨ step-4 ⟩

                            (sym (lUnit (loop ∙ loop))) ∙
                            α-rewrite' ∎
    



                glue-compwise true = {!   !}


                funExt-hyp-left : funExt (inclP-over-doubleloop-compwise) ≡ inclP-over-doubleloop
                funExt-hyp-left = {!   !}

                funExt-hyp-right : funExt (inclP-over-functorial-compwise) ≡ inclP-over-functorial
                funExt-hyp-right = {!   !}

                total-glue : inclP-over-doubleloop ≡ inclP-over-functorial
                total-glue = 
                    (sym funExt-hyp-left) ∙ 
                    (funExt-over-path' inclP-over-doubleloop-compwise inclP-over-functorial-compwise glue-compwise) ∙ 
                    funExt-hyp-right



            path-glue : PathP (λ i → PathP (λ j → partial-fiber ((sym α'-complete) i j)) incl incl) 
                (compPathP' {B = partial-fiber} refl refl)
                (compPathP' {B = partial-fiber} inclP inclP)
            path-glue = compPathP' (path-transport-hyp) (cong toPathP (sym temp-hyp)) where
                
                path-over-inclP : PathP (λ i → partial-fiber ((loop ∙ loop) i)) incl incl
                path-over-inclP = toPathP inclP-over-doubleloop
                
                path-over-refl : PathP (λ i → partial-fiber ((loop ∙ loop) i)) incl incl
                path-over-refl = toPathP inclP-over-functorial'

                path-transport-hyp :  PathP (λ i → PathP (λ j → partial-fiber ((sym α'-complete) i j)) incl incl) 
                    (compPathP' {B = partial-fiber} refl refl) 
                    path-over-refl 
                path-transport-hyp = congP (λ i t → toPathP t) (toPathP transp-of-proof) where
                    comp-refl-reduced : subst partial-fiber (refl ∙ refl) incl ≡ incl
                    comp-refl-reduced = 
                        (substComposite partial-fiber refl refl incl) ∙
                        (cong (subst partial-fiber refl) (substRefl {B = partial-fiber} incl)) ∙
                        (substRefl {B = partial-fiber} incl)

                    transp-of-proof : transport (λ i → (subst partial-fiber ((sym (α'-complete)) i) incl) ≡ incl) 
                                        comp-refl-reduced ≡ inclP-over-functorial'
                    transp-of-proof = substInPathsR (cong (λ t → subst partial-fiber t incl) (sym α'-complete)) comp-refl-reduced


                temp-hyp : inclP-over-doubleloop ≡ inclP-over-functorial'
                temp-hyp = {!   !}

                
            total-square : SquareP' partial-fiber (compPath→Square (sym α'-complete)) inclP refl refl inclP
            total-square = SquareP'-from-comp-equality {B = partial-fiber} inclP refl refl inclP path-glue

        ofGoodLevel : isOfHLevelDep 4 partial-fiber
        ofGoodLevel = {!   !}