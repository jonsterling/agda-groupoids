{-# OPTIONS --without-K #-}

module Groupoid.Core.Base where

open import Agda.Primitive
open import Common public
import Setoid as S
open import Type as T
  using (_,_)

record t d ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) : Set (lsuc (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ)) where
  no-eta-equality
  open S.Π
  field
    obj
      : Set ℓᵒ
    homˢ
      : obj T.∐.⊗ obj T.Π.⇒₀ S.t Dir.≈ ℓˢᵒ ℓˢʰ
    idnˢᵐ
      : ∀ {a}
      → S.𝟙.s S.Π.⇒₀ᵗ homˢ (a , a)
    cmpˢᵐ
      : ∀ {a b c}
      → homˢ (b , c) S.∐.⊗ homˢ (a , b) S.Π.⇒₀ᵗ homˢ (a , c)
    {invˢᵐ}
      : ∀ {a b}
      → Dir.el d T.𝟙.t (homˢ (a , b) S.Π.⇒₀ᵗ homˢ (b , a))

  private
    invˢᵐ≡
      : ∀ {a b}
      → (ϕ : d T.≡.t S.Dir.≈)
      → homˢ (a , b) ⇒₀ᵗ homˢ (b , a)
    invˢᵐ≡ {a}{b} ϕ =
      T.≡.subst
        (λ d′ → Dir.el d′ T.𝟙.t (homˢ (a , b) S.Π.⇒₀ᵗ homˢ (b , a))) ϕ
        invˢᵐ

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
    .{inv-lhs}
      : ∀ {a b}
      → (f : S.obj (homˢ (a , b)))
      → Dir.el {Φ = λ d′ → d T.≡.t d′ → Set _} d (T.Π.! T.𝟙.t) (λ ϕ →
          S.homᵗ (homˢ (a , a))
            ( cmpˢᵐ $₀ (invˢᵐ≡ ϕ $₀ f , f)
            , idnˢᵐ $₀ T.𝟙.*
            ))
        T.≡.refl
    .{inv-rhs}
      : ∀ {a b}
      → (f : S.obj (homˢ (a , b)))
      → Dir.el {Φ = λ d′ → d T.≡.t d′ → Set _} d (T.Π.! T.𝟙.t) (λ ϕ →
          S.homᵗ (homˢ (b , b))
            ( idnˢᵐ $₀ T.𝟙.*
            , cmpˢᵐ $₀ (f , invˢᵐ≡ ϕ $₀ f)
            ))
        T.≡.refl
open t public
