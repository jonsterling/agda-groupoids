{-# OPTIONS --sized-types --without-K #-}

module Groupoid.Base where

open import Agda.Primitive

import Setoid as S
open import Type as T
  using (_,_)

record t ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) : Set (lsuc (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ)) where
  open S.Π
  field
    obj   : Set ℓᵒ
    homˢ  : obj T.∐.⊗ obj T.Π.⇒₀ S.t ℓˢᵒ ℓˢʰ
    idnˢᵐ : ∀ {a} → S.𝟙.s S.Π.⇒₀ᵗ homˢ (a , a)
    cmpˢᵐ : ∀ {a b c} → homˢ (b , c) S.∐.⊗ homˢ (a , b) S.Π.⇒₀ᵗ homˢ (a , c)
    invˢᵐ : ∀ {a b} → homˢ (a , b) S.Π.⇒₀ᵗ homˢ (b , a)
  field
    .idn-lhs
      : ∀ {a b}
      → (f : S.obj (homˢ (a , b)))
      → S.homᵗ (homˢ (a , b))
          ( cmpˢᵐ $₀ (idnˢᵐ $₀ T.𝟙.* , f)
          , f
          )
    .idn-rhs
      : ∀ {a b}
      → (f : S.obj (homˢ (a , b)))
      → S.homᵗ (homˢ (a , b))
          ( f
          , cmpˢᵐ $₀ (f , idnˢᵐ $₀ T.𝟙.*)
          )
    .cmp-ass
      : ∀ {a b c d}
      → (f : S.obj (homˢ (a , b)))
      → (g : S.obj (homˢ (b , c)))
      → (h : S.obj (homˢ (c , d)))
      → S.homᵗ (homˢ (a , d))
          ( cmpˢᵐ $₀ (cmpˢᵐ $₀ (h , g) , f)
          , cmpˢᵐ $₀ (h , cmpˢᵐ $₀ (g , f))
          )
    .inv-lhs
      : ∀ {a b}
      → (f : S.obj (homˢ (a , b)))
      → S.homᵗ (homˢ (a , a))
          ( cmpˢᵐ $₀ (invˢᵐ $₀ f , f)
          , idnˢᵐ $₀ T.𝟙.*
          )
    .inv-rhs
      : ∀ {a b}
      → (f : S.obj (homˢ (a , b)))
      → S.homᵗ (homˢ (b , b))
          ( idnˢᵐ $₀ T.𝟙.*
          , cmpˢᵐ $₀ (f , invˢᵐ $₀ f)
          )
{-# NO_ETA t #-}
open t public
