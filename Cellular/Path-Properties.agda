{-# OPTIONS --cubical --allow-unsolved-metas  #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport

open import Cellular.Square hiding (SquareP'-from-comp-equality)


module Cellular.Path-Properties where
    private
        variable
            ℓ ℓ' : Level


    cong-of-sym-simple : {A : Type ℓ} {B : Type ℓ'} {a b : A} (f : A → B) (p : a ≡ b)
     → cong f (sym p) ≡ sym (cong f p)

    cong-of-sym-simple {a = a} f p = J (λ b p → cong f (sym p) ≡ symP (cong f p)) refl p

    -- module _ where
      -- -- try proving compPathP' with JDep
      -- compPathP'' : {A : Type ℓ} {x y z : A} {B : A → Type ℓ'} {x' : B x} {y' : B y} {z' : B z} {p : x ≡ y} {q : y ≡ z}
                   -- (P : PathP (λ i → B (p i)) x' y') (Q : PathP (λ i → B (q i)) y' z')
                   -- → PathP (λ i → B ((p ∙ q) i)) x' z'
      -- compPathP'' {B = B} {x' = x'} {p = p} {q = q} P Q = JDep
        -- (λ z q z' Q → PathP (λ i → B ((p ∙ q) i)) x' z' )
        -- {!!}
        -- q
        -- Q

    -- compPath≡Square : {A : Type ℓ} {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
      -- → (p ∙ s ≡ r ∙ q) ≡ (Square r s p q)
    -- compPath≡Square = {!!}

    -- Dependent version of compPath→Square
    -- The proof should be similar to compPathP'
    SquareP'-from-comp-equality : {A : Type ℓ} {B : A → Type ℓ'}
      {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
      {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
      {glue-a : a₋₀ ∙ a₁₋ ≡ a₀₋ ∙ a₋₁}
      (b₀₋ : PathP (λ i → B (a₀₋ i)) b₀₀ b₀₁)
      (b₁₋ : PathP (λ i → B (a₁₋ i)) b₁₀ b₁₁)
      (b₋₀ : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀) 
      (b₋₁ : PathP (λ i → B (a₋₁ i)) b₀₁ b₁₁)
      (glue : PathP (λ i → PathP (λ j → B (glue-a i j)) b₀₀ b₁₁) (compPathP' {B = B} b₋₀ b₁₋) (compPathP' {B = B} b₀₋ b₋₁))
      → SquareP' B (compPath→Square glue-a) b₀₋ b₁₋ b₋₀ b₋₁
    SquareP'-from-comp-equality {A = A} {B = B} {b₀₀ = b₀₀} {b₁₁ = b₁₁} {glue-a = glue-a} b₀₋ b₁₋ b₋₀ b₋₁ glue i j =
      comp
        (λ k → {!B ?!}) -- (λ i → subst-filler (λ s → {!SquareP' B s ? ? ? ?!}) {!!} {!!} i)
        {!!}
        {!!}
        {!!}
      where
        bla : SquareP' B (compPath→Square glue-a) b₀₋ b₁₋ b₋₀ b₋₁ ≡ SquareP' B (compPath→Square glue-a) b₀₋ b₁₋ b₋₀ b₋₁
        bla = {!!}
        

      -- -- JDep (λ a₀₁ a₀₋ b₀₁ b₋₀ → {!(glue : PathP (λ i → PathP (λ j → B (glue-a i j)) b₀₀ b₁₁) (compPathP' {B = B} b₋₀ b₁₋) (compPathP' {B = B} b₀₋ b₋₁)) → SquareP' B (compPath→Square glue-a) b₀₋ b₁₋ b₋₀ b₋₁!}) {!!} {!!} {!!}
      -- {!!}
      -- where
      -- -- the following should be enough by JDep
      -- lem :
        -- {a₀₀ a₁₀ : A} {b₀₀ : B a₀₀} {b₁₀ : B a₁₀}
        -- {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₀ ≡ a₁₀}
        -- {glue-a : a₋₀ ∙ refl ≡ refl ∙ a₋₁}
        -- (b₋₀ : PathP (λ i → B (a₋₀ i)) b₀₀ b₁₀) 
        -- (b₋₁ : PathP (λ i → B (a₋₁ i)) b₀₀ b₁₀)
        -- (glue : PathP (λ i → PathP (λ j → B (glue-a i j)) b₀₀ b₁₀) (compPathP' {B = B} b₋₀ refl) (compPathP' {B = B} refl b₋₁))
        -- → SquareP' B (compPath→Square glue-a) refl refl b₋₀ b₋₁
      -- lem {b₀₀ = b₀₀} {b₁₀ = b₁₀} {a₋₀ = a₋₀} {a₋₁ = a₋₁} {glue-a = glue-a} b₋₀ b₋₁ glue = glue3
        -- where
        -- glue-a' : a₋₀ ≡ a₋₁
        -- glue-a' = rUnit _ ∙ glue-a ∙ sym (lUnit _)
        -- glue1 : PathP (λ i → PathP (λ j → B (glue-a' i j)) b₀₀ b₁₀) b₋₀ b₋₁
        -- glue1 = {!!} -- from glue
        -- glue2 : SquareP' B (λ i j → glue-a' j i) refl refl b₋₀ b₋₁
        -- glue2 i j = glue1 j i
        -- glue3 : SquareP' B (compPath→Square glue-a) refl refl b₋₀ b₋₁
        -- glue3 i j = {!!}
        
    

    
    -- PathP (compPathP' P Q) (compPathP' P' Q')  


    {- independent-transport-to-compPath : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁: A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        (Q : PathP (λ i → B (q i)) y' z')
        (glue : transport (λ i → B (q i)) (subst B p x) ≡ z')
        → PathP () (compPathP' (subst-filler)) (compPathP' ) 

    independent-transport-to-compPath P Q = ? -}


    SquareP'-from-transport :  ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
        {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
        {a₀₋ : a₀₀ ≡ a₀₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₁ : a₀₁ ≡ a₁₁}
        {glue-a : a₋₀ ∙ a₁₋ ≡ a₀₋ ∙ a₋₁} 
        (glue-b : transport ((λ i → B (a₁₋ i))) (transport (λ i → B (a₋₀ i)) b₀₀)
            ≡ transport ((λ i → B (a₋₁ i))) (transport (λ i → B (a₀₋ i)) b₀₀))
        → SquareP' {A = A} B (compPath→Square glue-a) 
            (transport-filler (λ i → B (a₀₋ i)) b₀₀)
            (transport-filler (λ i → B (a₁₋ i)) (transport (λ i → B (a₋₀ i)) b₀₀))
            (transport-filler (λ i → B (a₋₀ i)) b₀₀)
            (compPathP' {A = A} (transport-filler (λ i → B (a₋₁ i)) (transport (λ i → B (a₀₋ i)) b₀₀)) (sym glue-b))

    SquareP'-from-transport glue-b = {!   !}

    --transp-composite-to-pathP : ∀ {ℓ} {A B C : Type ℓ} (p : A ≡ B) (q : B ≡ C) (x : A)
    --    → toPathP (transportComposite p q x) ≡ compPathP' {! toPathP ?   !} {! toPathP ?  !}

    --transp-composite-to-pathP p q x = {!   !} 

--------- comp shenanigans


    -- comp' : ∀ {ℓ} (A : (i : I) → Set ℓ) {φ : I} (u : ∀ i → Partial φ (A i)) (a : A i0 [ φ ↦ u i0 ]) → A i1
    -- comp' A {φ = φ} u a = hcomp (λ i → λ { (φ = i1) → transp (λ j → A (i ∨ j)) i (u _ 1=1) }) (inS (transport (λ i → A i) (outS a)))

    -- https://staff.math.su.se/anders.mortberg/papers/cubicalagda2.pdf
    -- comp est Défini par hcomp ∘ transport


    compPath : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    compPath {x = x} p q i =
      hcomp
        (λ{ j (i = i0) → x
          ; j (i = i1) → q j })
        (p i)

    comp-PathComp : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → (x ≡ z)
    comp-PathComp {A = A} {x = x} p q i = 
      comp (λ _ → A)
        (λ{j (i = i0) → x 
          ;j (i = i1) → q j }) 
        (p i) 

    pathComp-hom-eq : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → comp-PathComp p q ≡ compPath p q

    pathComp-hom-eq {A = A} {x = x} p q =
        comp-PathComp p q
          ≡⟨ refl ⟩
        (λ i → comp (λ _ → A) (λ {j (i = i0) → x; j (i = i1) → q j }) (p i))
          ≡⟨ refl ⟩
        -- (λ i → hcomp (λ {j (i = i0) → {!transp (λ i → A) i ?!}; j (i = i1) → q j }) (p i))
        -- (λ r → {!hcomp (λ i → λ { (r = i1) → transp (λ j → A) i (? _ 1=1) }) (inS (transport (λ i → A) (outS ?)))!})
        (λ r → hcomp {!λ i → λ { (r = i1) → transp (λ j → A) i (? _ 1=1) }!} {!inS (transport (λ i → A) (outS ?))!})
          ≡⟨ {!refl!} ⟩
        (λ i → hcomp (λ {j (i = i0) → x; j (i = i1) → q j }) (p i))
          ≡⟨ refl ⟩
        compPath p q
        ∎

    postulate
      compPathP-transpComp : ∀ {ℓ} {A : Type ℓ} {B : A → Type} {x y z : A} {x' : B x} {y' : B y} {z' : B z}
          {p : x ≡ y} {q : y ≡ z}
          (α : transport (λ i → B (p i)) x' ≡ y') -- subst B p x' ≡ y'
          (β : transport (λ i → B (q i)) y' ≡ z') -- subst B q y' ≡ z
          -- (P : PathP (λ i → B (p i)) x' y') (Q : PathP (λ i → B (q i)) y' z')
          -- (transport-acts-well : transport (λ i → B ((p ∙ q) i)) x' ≡ z')
          → fromPathP (compPathP' {B = B} (toPathP α) (toPathP β)) ≡ 
              (substComposite B p q x') ∙ (cong (subst B q) α) ∙ β

            -- (subst B (p ∙ q) x' ≡⟨ substComposite B p q x' ⟩
            --  subst B q (subst B p x') ≡⟨ cong (subst B q) α ⟩
            --  subst B q y' ≡⟨ β ⟩
            --  z' ∎)

    {- compPathP-to-transpComp {B = B} {x' = x'} {p = p} {q = q} α β = sym (
        (substComposite B p q x') ∙ (cong (subst B q) α) ∙ β
        ≡⟨ cong (λ t → t ∙ (cong (subst B q) α) ∙ β) refl ⟩
        (λ i → transport (cong B (compPath-filler' p q (~ i))) (transport-fillerExt (cong B p) i x')) ∙ (cong (subst B q) α) ∙ β
        ≡⟨ cong (λ t → t ∙ (cong (subst B q) α) ∙ β) refl ⟩
        (λ i → transp (λ j → ((cong B (compPath-filler' p q (~ i))) j)) i0 (transport-fillerExt (cong B p) i x'))
          ∙ (cong (subst B q) α) ∙ β
        ≡⟨ {!   !} ⟩
        fromPathP (compPathP' {B = B} (toPathP α) (toPathP β)) ∎) -}

    

    -- Voir fill, substComposite = compPathP'-filler etc 

    --postulate
    compPathP-transpComp' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y z : A} {x' : B x} {y' : B y} {z' : B z}
          {p : x ≡ y} {q : y ≡ z}
          (α : transport (λ i → B (p i)) x' ≡ y') -- subst B p x' ≡ y'
          (β : transport (λ i → B (q i)) y' ≡ z') -- subst B q y' ≡ z
          → (compPathP' {B = B} (toPathP α) (toPathP β)) ≡ 
              toPathP ((substComposite B p q x') ∙ (cong (subst B q) α) ∙ β)

    compPathP-transpComp' {B = B} {x = x} {y = y} {z = z} {x' = x'} {y' = y'} {z' = z'} {p = p} {q = q} α β = 
      (λ i → comp (λ j → B (compPath-filler p q j i))
        (λ j → λ { (i = i0) → x'  ;
                   (i = i1) → (toPathP {A = λ i → B (q i)} β) j })
        ((toPathP {A = λ i → B (p i)} α) i))
      ≡⟨ {!   !} ⟩
       (λ i → hcomp (λ j → λ { (i = i0) → x'
                           ; (i = i1) → ((substComposite B p q x') ∙ (cong (subst B q) α) ∙ β) j })
                      (transp (λ j → (λ i' → B ((p ∙ q) i')) (i ∧ j)) (~ i) x')) ∎



-- Helper to convert equalities between functions 

    funExt-over-path : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f g : A → B}
      (p : f ≡ g) (q : f ≡ g) (glue-comp : (x : A) → (funExt⁻ p) x ≡ (funExt⁻ q) x)
      → p ≡ q

    funExt-over-path p q glue = refl ∙ (cong funExt (funExt glue)) ∙ refl

    funExt-over-path' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f g : A → B}
      (p q : (x : A) → f x ≡ g x) (glue-comp : (x : A) → p x ≡ q x)
      → funExt p ≡ funExt q

    funExt-over-path' p q glue = cong funExt (funExt glue)

    postulate
      funExt-composite : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f g h : A → B}
        (p : (x : A) → f x ≡ g x) (q : (x : A) → g x ≡ h x)
        → funExt p ∙ funExt q ≡ funExt (λ x → p x ∙ q x)

      funExt⁻-composite : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f g h : A → B}
        (p : f ≡ g) (q : g ≡ h)
        → (λ x → (funExt⁻ p) x ∙ (funExt⁻ q) x) ≡ funExt⁻ (p ∙ q)

      funExt-sym : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f g : A → B}
        (p : (x : A) → f x ≡ g x)
        → sym (funExt p) ≡ funExt (λ x → sym (p x))


    -- funExt-composite p q = funExt-over-path {!   !} {!   !} {!   !}

