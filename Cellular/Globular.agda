{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import coh

open import Agda.

module Cellular.Globular where

    Glob : ∀ {ℓ} {A : Type ℓ} {x y : A} (p q : x ≡ y) → Type ℓ
    Glob p q = p ≡ q

    GlobP : ∀ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {x : A} {y : A} {p q : x ≡ y} {x' : B x} {y' : B y}
        {g : Glob p q} (P : PathP (λ i → B (p i)) x' y') (Q : PathP (λ i → B (q i)) x' y') → Type ℓ
    GlobP {A = A} {B = B} {x = x} {y = y} {x' = x'} {y' = y'} {g = g} P Q = 
        PathP (λ i → PathP (λ j → B (g i j)) x' y') P Q 

    glob-compose-horizontal : {A : Type} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} (lCell : p ≡ q) (rCell : r ≡ s)
        → (p ∙ r ≡ q ∙ s)

    glob-compose-horizontal {A} {a} {b} {c} {p} {q} {r} {s} lCell rCell =
        (whisker-right {A = A} p r s rCell) ∙ (whisker-left {A = A} p q s lCell)

    glob-compose-vertical : {A : Type} {a b : A} {p q r : a ≡ b} (tCell : p ≡ q) (bCell : q ≡ r)
        → (p ≡ r)

    glob-compose-vertical {A} {a} {b} {p} {q} {r} tCell bCell =
        tCell ∙ bCell 

    _▿_ : {A : Type} {a b : A} {p q r : a ≡ b} → (p ≡ q) → (q ≡ r) → (p ≡ r)
    _▿_ = glob-compose-vertical

    infixr 40 _▿_ 

    _▹_ : {A : Type} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} → (p ≡ q) → (r ≡ s) → (p ∙ r ≡ q ∙ s)
    _▹_ {A} {a} {b} {c} {p} {q} {r} {s} = glob-compose-horizontal {A} {a} {b} {c} {p} {q} {r} {s}

    infixr 40 _▹_ 

    l-id-glob : {A : Type} {b c : A} (p : b ≡ c) → (refl ∙ p ≡ p)
    l-id-glob {A} p = left-id {A = A} p

    r-id-glob : {A : Type} {a b : A} (p : a ≡ b) → (p ∙ refl ≡ p)
    r-id-glob {A} p = right-id {A = A} p

    -- ▹-assoc : {A : Type} {a b c d : A} {p q : a ≡ b} {r s : b ≡ c} {t u : c ≡ d} (lCell : (p ≡ q)) (midCell : (r ≡ s)) (rCell : (t ≡ u)) 
    --    → (lCell ▹ midCell) ▹ rCell ≡ lCell ▹ midCell ▹ rCell

    -- transport dépendant ?

    -- ▹-assoc lCell midCell rCell = ?

    -- ▿-assoc
    -- exchange-law