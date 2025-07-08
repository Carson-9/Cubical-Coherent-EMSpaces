{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Unit renaming ( Unit to ⊤ )
open import Cellular.Square

module Group.Em-Group where

    private
        variable
            ℓ : Level

    --infixl 30 _×_

    record isGroup 
        {ob-set : Type ℓ} (1g : ob-set) (_×_ : ob-set → ob-set → ob-set) (inv : ob-set → ob-set) : Type ℓ where
            constructor is-group
            field 

                setOb : isSet ob-set

                ×-assoc : (x y z : ob-set) → (x × y) × z ≡ x × (y × z)
                
                l-neutral : (x : ob-set) → 1g × x ≡ x
                r-neutral : (x : ob-set) → x × 1g ≡ x

                l-inv : (x : ob-set) → (inv x) × x ≡ 1g
                r-inv : (x : ob-set) → x × (inv x) ≡ 1g



    record Group (ob-set : Type ℓ) : Type ℓ where
        constructor group
        field
            1g : ob-set
            _×_ : ob-set → ob-set → ob-set
            inv : ob-set → ob-set
            makes-group : isGroup {ob-set = ob-set} 1g _×_ inv
            trunc : isSet ob-set


    -- Usual EM construction

    data Delooping-1 {ob-set : Type ℓ} (g : Group ob-set) : (Type (ℓ-suc ℓ)) where
        base : Delooping-1 g
        [_] : ob-set → base ≡ base
        [0] : [ Group.1g g ] ≡ refl
        incl-functorial-1 : (x y : ob-set) → PathP (λ j → base ≡ ([ x ] j)) [ y ] [ (Group._×_ g x y) ]  -- [ (Group._×_ g x y) ] ≡ [ y ] ∙ [ x ]
        1-trunc : isGroupoid (Delooping-1 g) 


    Delooping-1-elim : {ℓ : Level} {A : Type (ℓ-suc ℓ)} {ob-set  : Type ℓ} {g : Group ob-set}
        (a : A)
        (incl : ob-set → a ≡ a)
        (zero-incl : incl (Group.1g g) ≡ refl)
        (incl-fun : (x y : ob-set) → PathP (λ j → a ≡ (incl x) j) (incl y) (incl (Group._×_ g x y)))
        (trunc : isGroupoid A)
        → (Delooping-1 g) → A

    Delooping-1-elim {A = A} {ob-set = ob-set} {g = g} a incl zero-incl incl-fun trunc base = a
    Delooping-1-elim {A = A} {ob-set = ob-set} {g = g} a incl zero-incl incl-fun trunc ([ x ] i) = (incl x) i
    Delooping-1-elim {A = A} {ob-set = ob-set} {g = g} a incl zero-incl incl-fun trunc ([0] i j) = zero-incl i j
    Delooping-1-elim {A = A} {ob-set = ob-set} {g = g} a incl zero-incl incl-fun trunc (incl-functorial-1 x y i j) = incl-fun x y i j
    Delooping-1-elim {A = A} {ob-set = ob-set} {g = g} a incl zero-incl incl-fun trunc (1-trunc x y p q r s i j k) = 
        trunc
        (Delooping-1-elim a incl zero-incl incl-fun trunc x)
        (Delooping-1-elim a incl zero-incl incl-fun trunc y)
        (λ i → Delooping-1-elim a incl zero-incl incl-fun trunc (p i))
        (λ i → Delooping-1-elim a incl zero-incl incl-fun trunc (q i))
        (λ i j → Delooping-1-elim a incl zero-incl incl-fun trunc (r i j))
        (λ i j → Delooping-1-elim a incl zero-incl incl-fun trunc (s i j))
        i j k 
        

    Delooping-1-ind : {ℓ : Level} {ob-set  : Type ℓ} {g : Group ob-set} {P : (Delooping-1 g) → Type (ℓ-suc ℓ)}
        (a : P base)
        (over-incl : (x : ob-set) → PathP (λ i → P ([ x ] i) ) a a)
        (over-incl-zero : PathP (λ i → PathP (λ j → P ([0] i j)) a a) (over-incl (Group.1g g)) refl)
        (over-incl-fun : (x y : ob-set) → PathP (λ i → PathP (λ j → P (incl-functorial-1 x y i j)) a (over-incl x i)) (over-incl y) (over-incl (Group._×_ g x y)))
        (trunc : isOfHLevelDep 3 P)
        → (x : Delooping-1 g) → P x

    Delooping-1-ind {ob-set = ob-set} {g = g} {P = P} a ol olz olf trunc base = a
    Delooping-1-ind {ob-set = ob-set} {g = g} {P = P} a ol olz olf trunc ([ x ] i) = (ol x) i
    Delooping-1-ind {ob-set = ob-set} {g = g} {P = P} a ol olz olf trunc ([0] i j) = olz i j
    Delooping-1-ind {ob-set = ob-set} {g = g} {P = P} a ol olz olf trunc (incl-functorial-1 x y j i) = (olf x y) j i
    Delooping-1-ind {ob-set = ob-set} {g = g} {P = P} a ol olz olf trunc (1-trunc x y p q r s i j k) = trunc
        (Delooping-1-ind a ol olz olf trunc x)
        (Delooping-1-ind a ol olz olf trunc y)
        (λ i → Delooping-1-ind a ol olz olf trunc (p i))
        (λ i → Delooping-1-ind a ol olz olf trunc (q i))
        (λ i j → Delooping-1-ind a ol olz olf trunc (r i j))
        (λ i j → Delooping-1-ind a ol olz olf trunc (s i j))
        (λ i j k → 1-trunc x y p q r s i j k)
        i j k


    -- EM-Space as a 2-groupoid

    data Delooping-2 {ob-set : Type ℓ} (g : Group ob-set) : Type (ℓ-suc ℓ) where
        base₂ : Delooping-2 g
        [_]₂ : ob-set → base₂ ≡ base₂
        [0]₂ : [ Group.1g g ]₂ ≡ refl
        incl-functorial-1₂ : (x y : ob-set) → PathP (λ j → base₂ ≡ ([ x ]₂ j)) [ y ]₂ [ (Group._×_ g x y) ]₂
        {- incl-functorial-2₂ : (x y z : ob-set) → Square
            (incl-functorial-1₂ (Group._×_ g x y) z)
            ((cong (λ t → [ x ]₂ ∙ t) (incl-functorial-1₂ y z)) ∙ (assoc [ x ]₂ [ y ]₂ [ z ]₂))
            ((cong (λ t → [ t ]₂) (isGroup.×-assoc (Group.makes-group g) x y z)) ∙ (incl-functorial-1₂ x (Group._×_ g y z)))
            (cong (λ t → t ∙ [ z ]₂) (incl-functorial-1₂ x y)) -}
        2-trunc : is2Groupoid (Delooping-2 g)

    Delooping-2-elim : {ℓ : Level} {A : Type (ℓ-suc ℓ)} {ob-set  : Type ℓ} {g : Group ob-set}
        (a : A)
        (incl : ob-set → a ≡ a)
        (zero-incl : incl (Group.1g g) ≡ refl)
        (incl-fun : (x y : ob-set) → PathP (λ j → a ≡ (incl x) j) (incl y) (incl (Group._×_ g x y)))
        (trunc : is2Groupoid A)
        → (Delooping-2 g) → A

    Delooping-2-elim {A = A} {ob-set = ob-set} {g = g} a incl zero-incl incl-fun trunc base₂ = a
    Delooping-2-elim {A = A} {ob-set = ob-set} {g = g} a incl zero-incl incl-fun trunc ([ x ]₂ i) = (incl x) i
    Delooping-2-elim {A = A} {ob-set = ob-set} {g = g} a incl zero-incl incl-fun trunc ([0]₂ i j) = zero-incl i j
    Delooping-2-elim {A = A} {ob-set = ob-set} {g = g} a incl zero-incl incl-fun trunc (incl-functorial-1₂ x y i j) = incl-fun x y i j
    Delooping-2-elim {A = A} {ob-set = ob-set} {g = g} a incl zero-incl incl-fun trunc (2-trunc x y p q r s t u i j k l) = 
        trunc
        (Delooping-2-elim a incl zero-incl incl-fun trunc x)
        (Delooping-2-elim a incl zero-incl incl-fun trunc y)
        (λ i → Delooping-2-elim a incl zero-incl incl-fun trunc (p i))
        (λ i → Delooping-2-elim a incl zero-incl incl-fun trunc (q i))
        (λ i j → Delooping-2-elim a incl zero-incl incl-fun trunc (r i j))
        (λ i j → Delooping-2-elim a incl zero-incl incl-fun trunc (s i j))
        (λ i j k → Delooping-2-elim a incl zero-incl incl-fun trunc (t i j k))
        (λ i j k → Delooping-2-elim a incl zero-incl incl-fun trunc (u i j k))
        i j k l
        

    Delooping-2-ind : {ℓ : Level} {ob-set  : Type ℓ} {g : Group ob-set} {P : (Delooping-2 g) → Type (ℓ-suc ℓ)}
        (a : P base₂)
        (over-incl : (x : ob-set) → PathP (λ i → P ([ x ]₂ i) ) a a)
        (over-incl-zero : PathP (λ i → PathP (λ j → P ([0]₂ i j)) a a) (over-incl (Group.1g g)) refl)
        (over-incl-fun : (x y : ob-set) → PathP (λ i → PathP (λ j → P (incl-functorial-1₂ x y i j)) a (over-incl x i)) (over-incl y) (over-incl (Group._×_ g x y)))
        (trunc : isOfHLevelDep 4 P)
        → (x : Delooping-2 g) → P x

    Delooping-2-ind {ob-set = ob-set} {g = g} {P = P} a ol olz olf trunc base₂ = a
    Delooping-2-ind {ob-set = ob-set} {g = g} {P = P} a ol olz olf trunc ([ x ]₂ i) = (ol x) i
    Delooping-2-ind {ob-set = ob-set} {g = g} {P = P} a ol olz olf trunc ([0]₂ i j) = olz i j
    Delooping-2-ind {ob-set = ob-set} {g = g} {P = P} a ol olz olf trunc (incl-functorial-1₂ x y j i) = (olf x y) j i
    Delooping-2-ind {ob-set = ob-set} {g = g} {P = P} a ol olz olf trunc (2-trunc x y p q r s t u i j k l) = trunc
        (Delooping-2-ind a ol olz olf trunc x)
        (Delooping-2-ind a ol olz olf trunc y)
        (λ i → Delooping-2-ind a ol olz olf trunc (p i))
        (λ i → Delooping-2-ind a ol olz olf trunc (q i))
        (λ i j → Delooping-2-ind a ol olz olf trunc (r i j))
        (λ i j → Delooping-2-ind a ol olz olf trunc (s i j))
        (λ i j k → Delooping-2-ind a ol olz olf trunc (t i j k))
        (λ i j k → Delooping-2-ind a ol olz olf trunc (u i j k))
        (λ i j k l → 2-trunc x y p q r s t u i j k l)
        i j k l
