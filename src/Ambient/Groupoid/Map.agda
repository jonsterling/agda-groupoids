{-# OPTIONS --without-K #-}

module Ambient.Groupoid.Map where

open import Agda.Primitive
import Ambient.Groupoid.Base as G
import Ambient.Groupoid.Map.Boot as Map
import Ambient.Groupoid.Tensor.Boot as Ten
import Ambient.Groupoid.Terminal as 𝟙
import Setoid as S
open import Type as T
  using (_,_)

infixr 2 _⇒₀ᵍ_
infixr 0 _⇒₁ᵗ_
infix 0 _⇔₁ᵗ_

record _⇒₁ᵗ_
  {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  (F G : A Map.⇒₀ᵗ B)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ˢᵒ) ⊔ (ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  field
    com₁
      : ∀ {a}
      → S.obj (G.homˢ B (F Map.$₀ a , G Map.$₀ a))
  field
    .nat₁
      : ∀ {a b}
      → (f : S.obj (G.homˢ A (a , b)))
      → S.homᵗ (G.homˢ B (F Map.$₀ _ , G Map.$₀ _))
          ( G.cmpˢ B S.Map.$₀ (com₁ , F Map.$₁ f)
          , G.cmpˢ B S.Map.$₀ (G Map.$₁ f , com₁)
          )
open _⇒₁ᵗ_ public

record _⇒₂_
  {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {F G : A Map.⇒₀ᵗ B}
  (α β : F ⇒₁ᵗ G)
    : Set (ℓ₀ᵒ ⊔ (ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  field
    .com₂
      : ∀ {a}
      → S.homᵗ (G.homˢ B (F Map.$₀ a , G Map.$₀ a)) (com₁ α {a} , com₁ β {a})
open _⇒₂_ public

_⇒₁ˢ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (F G : A Map.⇒₀ᵗ B)
  → S.t S.Dir.≈ _ _
S.obj (_⇒₁ˢ_ F G) =
  F ⇒₁ᵗ G
S.homᵗ (_⇒₁ˢ_ F G) =
  λ {(α , β) → α ⇒₂ β}
com₂ (S.idnᵗ (_⇒₁ˢ_ {B = B} F G) _) =
  S.idnᵗ (G.homˢ B (F Map.$₀ _ , G Map.$₀ _)) _
com₂ (S.cmpᵗ (_⇒₁ˢ_ {B = B} F G) (g⇒₂ , f⇒₂)) =
  S.cmpᵗ (G.homˢ B (F Map.$₀ _ , G Map.$₀ _))
    (com₂ g⇒₂ , com₂ f⇒₂)
com₂ (S.invᵗ (_⇒₁ˢ_ {B = B} F G) f⇒₂) =
  S.invᵗ (G.homˢ B (F Map.$₀ _ , G Map.$₀ _))
    (com₂ f⇒₂)

idn₁ˢ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (F : A Map.⇒₀ᵗ B)
  → S.𝟙.s⁰ S.Map.⇒₀ᵗ (F ⇒₁ˢ F)
com₁ (S.Map._$₀_ (idn₁ˢ {B = B} F) _) =
  G.idnˢ B S.Map.$₀ _
nat₁ (S.Map._$₀_ (idn₁ˢ {B = B} F) _) _ =
  S.cmpᵗ (G.homˢ B (F Map.$₀ _ , F Map.$₀ _))
    ( S.invᵗ (G.homˢ B _) (G.idn-rhs B (F Map.$₁ _))
    , G.idn-lhs B (F Map.$₁ _) )
com₂ (S.Map._$₁_ (idn₁ˢ {B = B} F) _) =
  G.idnˢ B S.Map.$₁ _

cmp₁ˢ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G H : A Map.⇒₀ᵗ B}
  → ((G ⇒₁ˢ H) S.Ten.⊗ (F ⇒₁ˢ G)) S.Map.⇒₀ᵗ (F ⇒₁ˢ H)
com₁ (S.Map._$₀_ (cmp₁ˢ {B = B}) (β , α)) =
  G.cmpˢ B S.Map.$₀ (com₁ β , com₁ α)
nat₁ (S.Map._$₀_ (cmp₁ˢ {B = B}) (β , α)) _ =
  S.cmpᵗ (G.homˢ B _)
  ( G.cmp-ass B _ _ _
  , S.cmpᵗ (G.homˢ B _)
    ( G.cmpˢ B S.Map.$₁
      ( nat₁ β _
      , S.idnᵗ (G.homˢ B _) _ )
    , S.cmpᵗ (G.homˢ B _)
      ( S.invᵗ (G.homˢ B _) (G.cmp-ass B _ _ _)
      , S.cmpᵗ (G.homˢ B _)
        ( G.cmpˢ B S.Map.$₁
          ( S.idnᵗ (G.homˢ B _) _
          , nat₁ α _ )
        , G.cmp-ass B _ _ _ ))))
com₂ (S.Map._$₁_ (cmp₁ˢ {B = B}) (β , α)) =
  G.cmpˢ B S.Map.$₁ (com₂ β , com₂ α)

inv₁ˢ
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t S.Dir.≈ ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t S.Dir.≈ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G : A Map.⇒₀ᵗ B}
  → (F ⇒₁ˢ G) S.Map.⇒₀ᵗ (G ⇒₁ˢ F)
com₁ (S.Map._$₀_ (inv₁ˢ {B = B}) α) =
  G.invˢ B S.Map.$₀ (com₁ α)
com₂ (S.Map._$₁_ (inv₁ˢ {B = B}) α) =
  G.invˢ B S.Map.$₁ (com₂ α)
nat₁ (S.Map._$₀_ (inv₁ˢ {A = A}{B = B}) α) _ =
  S.cmpᵗ (G.homˢ B _)
    ( S.cmpᵗ (G.homˢ B _)
      ( S.cmpᵗ (G.homˢ B _)
        ( S.cmpᵗ (G.homˢ B _)
          ( S.cmpᵗ (G.homˢ B _)
            ( G.cmpˢ B S.Map.$₁
              ( S.cmpᵗ (G.homˢ B _)
                ( S.cmpᵗ (G.homˢ B _)
                  ( S.cmpᵗ (G.homˢ B _)
                    ( G.idn-lhs B _
                    , G.cmpˢ B S.Map.$₁
                      ( G.inv-lhs B _
                      , S.idnᵗ (G.homˢ B _) _ ) )
                  , S.invᵗ (G.homˢ B _) (G.cmp-ass B _ _ _) )
                , G.cmpˢ B S.Map.$₁
                  ( S.idnᵗ (G.homˢ B _) _
                  , S.invᵗ (G.homˢ B _) (nat₁ α _) ))
              , S.idnᵗ (G.homˢ B _) _ )
            , S.invᵗ (G.homˢ B _) (G.cmp-ass B _ _ _) )
          , G.cmpˢ B S.Map.$₁
            ( S.idnᵗ (G.homˢ B _) _
            , S.invᵗ (G.homˢ B _) (G.cmp-ass B _ _ _) ) )
        , G.cmp-ass B _ _ _)
      , G.cmpˢ B S.Map.$₁ (S.idnᵗ (G.homˢ B _) _ , G.inv-rhs B _))
    , S.invᵗ (G.homˢ B _) (G.idn-rhs B _) )

record _⇔₁ᵗ_
  {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  (F G : A Map.⇒₀ᵗ B)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ˢᵒ) ⊔ (ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  field
    fwd : F ⇒₁ᵗ G
    bwd : G ⇒₁ᵗ F
  field
    .iso-fwd : S.homᵗ (F ⇒₁ˢ F) (cmp₁ˢ S.Map.$₀ (bwd , fwd) , idn₁ˢ F S.Map.$₀ _)
    .iso-bwd : S.homᵗ (G ⇒₁ˢ G) (cmp₁ˢ S.Map.$₀ (fwd , bwd) , idn₁ˢ G S.Map.$₀ _)

  ⟨_⇔⟩₁ : ∀ {a} → G.hom₀ B (F Map.$₀ a) (G Map.$₀ a)
  ⟨_⇔⟩₁ = com₁ fwd

  ⟨⇔_⟩₁ : ∀ {a} → G.hom₀ B (G Map.$₀ a) (F Map.$₀ a)
  ⟨⇔_⟩₁ = com₁ bwd
open _⇔₁ᵗ_ public

-- FIXME: cmp-w₀ and cmp-w₀ are problematic because of Hα/βF dependency

cmp₁ᵗ-w₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Map.⇒₀ᵗ B}
  → (Hα : (B Map.⇒₀ᵗ C) T.Ten.⊗ (F ⇒₁ᵗ G))
  → (T.Ten.π₀ Hα Map.∘₀ᵗ F) ⇒₁ᵗ (T.Ten.π₀ Hα Map.∘₀ᵗ G)
com₁ (cmp₁ᵗ-w₀ (H , α)) =
  H Map.$₁ com₁ α
nat₁ (cmp₁ᵗ-w₀ {C = C} (H , α)) f =
  S.cmpᵗ (G.homˢ C _)
  ( Map.cmp H _ _
  , S.cmpᵗ (G.homˢ C _)
    ( H Map.$₂ (nat₁ α f)
    , S.invᵗ (G.homˢ C _) (Map.cmp H _ _)))

cmp₁ᵗ-w₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {G H : B Map.⇒₀ᵗ C}
  → (βF : (G ⇒₁ᵗ H) T.Ten.⊗ (A Map.⇒₀ᵗ B))
  → (G Map.∘₀ᵗ T.Ten.π₁ βF) ⇒₁ᵗ (H Map.∘₀ᵗ T.Ten.π₁ βF)
com₁ (cmp₁ᵗ-w₁ (β , F)) = com₁ β
nat₁ (cmp₁ᵗ-w₁ (β , F)) f = nat₁ β (F Map.$₁ f)

cmp₀ˢ-h₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Map.⇒₀ᵗ B}
  → {H K : B Map.⇒₀ᵗ C}
  → ((H ⇒₁ˢ K) S.Ten.⊗ (F ⇒₁ˢ G)) S.Map.⇒₀ᵗ ((H Map.∘₀ᵗ F) ⇒₁ˢ (K Map.∘₀ᵗ G))
com₁ (S.Map._$₀_ (cmp₀ˢ-h₀ {C = C} {K = K}) (β , α)) =
  G.cmpˢ C S.Map.$₀ (K Map.$₁ com₁ α , com₁ β)
com₂ (S.Map._$₁_ (cmp₀ˢ-h₀ {C = C} {K = K}) (β , α)) =
  G.cmpˢ C S.Map.$₁ (K Map.$₂ com₂ α , com₂ β)
nat₁ (S.Map._$₀_ (cmp₀ˢ-h₀ {C = C}{K = K}) (β , α)) _ =
  S.cmpᵗ (G.homˢ C _)
    ( S.cmpᵗ (G.homˢ C _)
      ( S.cmpᵗ (G.homˢ C _)
        ( S.cmpᵗ (G.homˢ C _)
          ( G.cmp-ass C _ _ _
          , G.cmpˢ C S.Map.$₁
            ( S.cmpᵗ (G.homˢ C _)
              ( S.cmpᵗ (G.homˢ C _)
                ( Map.cmp K _ _
                , K Map.$₂ nat₁ α _ )
              , S.invᵗ (G.homˢ C _) (Map.cmp K _ _) )
            , S.idnᵗ (G.homˢ C _) _) )
        , S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _) )
      , G.cmpˢ C S.Map.$₁ (S.idnᵗ (G.homˢ C _) _ , nat₁ β _) )
    , G.cmp-ass C _ _ _ )

cmp₀ˢ-h₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Map.⇒₀ᵗ B}
  → {H K : B Map.⇒₀ᵗ C}
  → ((H ⇒₁ˢ K) S.Ten.⊗ (F ⇒₁ˢ G)) S.Map.⇒₀ᵗ ((H Map.∘₀ᵗ F) ⇒₁ˢ (K Map.∘₀ᵗ G))
com₁ (S.Map._$₀_ (cmp₀ˢ-h₁ {C = C}{H = H}) (β , α)) =
  G.cmpˢ C S.Map.$₀ (com₁ β , H Map.$₁ com₁ α)
com₂ (S.Map._$₁_ (cmp₀ˢ-h₁ {C = C}{H = H}) (β , α)) =
  G.cmpˢ C S.Map.$₁ (com₂ β , H Map.$₂ com₂ α)
nat₁ (S.Map._$₀_ (cmp₀ˢ-h₁ {C = C}{H = H}) (β , α)) _ =
  S.cmpᵗ (G.homˢ C _)
    ( S.cmpᵗ (G.homˢ C _)
      ( S.cmpᵗ (G.homˢ C _)
        ( S.cmpᵗ (G.homˢ C _)
          ( G.cmp-ass C _ _ _
          , G.cmpˢ C S.Map.$₁
            ( nat₁ β _
            , S.idnᵗ (G.homˢ C _) _ ) )
        , S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _) )
      , G.cmpˢ C S.Map.$₁
        ( S.idnᵗ (G.homˢ C _) _
        , S.cmpᵗ (G.homˢ C _)
          ( S.cmpᵗ (G.homˢ C _)
            ( Map.cmp H _ _
            , H Map.$₂ nat₁ α _ )
          , S.invᵗ (G.homˢ C _) (Map.cmp H _ _) ) ) )
    , G.cmp-ass C _ _ _ )

_⇒₀ᵍ_ : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  → (B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
  → G.t d _ _ _
G.obj (A ⇒₀ᵍ B) =
  A Map.⇒₀ᵗ B
G.homˢ (A ⇒₀ᵍ B) =
  λ {(F , G) → F ⇒₁ˢ G}
G.idnˢ (A ⇒₀ᵍ B) =
  λ {F} → idn₁ˢ F
G.cmpˢ (A ⇒₀ᵍ B) =
  cmp₁ˢ
G.invˢ (_⇒₀ᵍ_ {G.Dir.≤} A B) =
  _
G.invˢ (_⇒₀ᵍ_ {G.Dir.≈} A B) =
  inv₁ˢ
com₂ (G.idn-lhs (A ⇒₀ᵍ B) α) =
  G.idn-lhs B (com₁ α)
com₂ (G.idn-rhs (A ⇒₀ᵍ B) α) =
  G.idn-rhs B (com₁ α)
com₂ (G.cmp-ass (A ⇒₀ᵍ B) α β γ) =
  G.cmp-ass B (com₁ α) (com₁ β) (com₁ γ)
G.inv-lhs (_⇒₀ᵍ_ {G.Dir.≤} A B) =
  _
com₂ (G.inv-lhs (_⇒₀ᵍ_ {G.Dir.≈} A B) α) =
  G.inv-lhs B (com₁ α)
G.inv-rhs (_⇒₀ᵍ_ {G.Dir.≤} A B) f =
  _
com₂ (G.inv-rhs (_⇒₀ᵍ_ {G.Dir.≈} A B) α) =
  G.inv-rhs B (com₁ α)

idn₀ᵍ
  : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ}
  → 𝟙.g Map.⇒₀ᵗ (A ⇒₀ᵍ A)
Map._$₀_ idn₀ᵍ =
  Map.idn₀ᵗ
Map.-$₁ˢ- (idn₀ᵍ {A = A}) =
  G.idnˢ (A ⇒₀ᵍ A)
com₂ (Map.idn (idn₀ᵍ {A = A})) =
  S.idnᵗ (G.homˢ A _) _
com₂ (Map.cmp (idn₀ᵍ {A = A}) g f) =
  S.invᵗ (G.homˢ A _) (G.idn-rhs A (G.idnˢ A S.Map.$₀ _))

cmp₀ᵍ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → ((B ⇒₀ᵍ C) Ten.⊗ (A ⇒₀ᵍ B)) Map.⇒₀ᵗ (A ⇒₀ᵍ C)
Map._$₀_ cmp₀ᵍ =
  Map.cmp₀ᵗ
Map.-$₁ˢ- cmp₀ᵍ =
  cmp₀ˢ-h₀
com₂ (Map.idn (cmp₀ᵍ {B = B}{C}) {g , _}) =
  S.cmpᵗ (G.homˢ C _)
    ( Map.idn g
    , G.idn-rhs C (g Map.$₁ (G.idnˢ B S.Map.$₀ T.𝟙.*)) )
com₂ (Map.cmp (cmp₀ᵍ {C = C}) {c = h₁ , _} (β₁ , _) _) =
  S.cmpᵗ (G.homˢ C _)
    ( S.cmpᵗ (G.homˢ C _)
      ( S.cmpᵗ (G.homˢ C _)
        ( S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _)
        , G.cmpˢ C S.Map.$₁
          ( S.idnᵗ (G.homˢ C _) _
          , S.cmpᵗ (G.homˢ C _)
            ( S.cmpᵗ (G.homˢ C _)
              ( G.cmp-ass C _ _ _
              , G.cmpˢ C S.Map.$₁
                ( S.invᵗ (G.homˢ C _) (nat₁ β₁ _)
                , S.idnᵗ (G.homˢ C _) _ ) )
            , S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _) ) ) )
      , G.cmp-ass C _ _ _ )
    , G.cmpˢ C S.Map.$₁ (Map.cmp h₁ _ _ , S.idnᵗ (G.homˢ C _) _) )

!ᵍ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → G.obj A → (B Map.⇒₀ᵗ A)
Map._$₀_ (!ᵍ a) _ = a
Map.-$₁ˢ- (!ᵍ {A = A} a) = S.Map.!ˢ (G.idnˢ A S.Map.$₀ _)
Map.idn (!ᵍ {A = A} a) = S.idnᵗ (G.homˢ A _) _
Map.cmp (!ᵍ {A = A} a) g f = S.invᵗ (G.homˢ A _) (G.idn-rhs A (G.idnˢ A S.Map.$₀ _))

curry
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (F : (A Ten.⊗ B) Map.⇒₀ᵗ C)
  → A Map.⇒₀ᵗ (B ⇒₀ᵍ C)
curry {A = A}{B = B}{C = C} F = record
  { _$₀_ = λ a → record
    { _$₀_ = λ b → F Map.$₀ (a , b)
    ; -$₁ˢ- = λ {b₀}{b₁} → record
      { _$₀_ = λ f → F Map.$₁ (G.idn₀ A , f)
      ; _$₁_ = λ {f₀}{f₁} p → F Map.$₂ (S.idnᵗ (G.homˢ A _) _ , p) }
    ; idn = λ {b} → Map.idn F
    ; cmp = λ {b₀}{b₁}{b₂} g f →
      S.cmpᵗ (G.homˢ C _)
        ( Map.cmp F _ _
        , F Map.$₂ (S.invᵗ (G.homˢ A _) (G.idn-rhs A (G.idn₀ A)) , S.idnᵗ (G.homˢ B _) _) )
    }
  ; -$₁ˢ- = λ {a₀}{a₁} → record
    { _$₀_ = λ f → record
      { com₁ = λ {b} → F Map.$₁ (f , G.idn₀ B)
      ; nat₁ = λ {b₀}{b₁} g →
        S.cmpᵗ (G.homˢ C _)
          ( S.cmpᵗ (G.homˢ C _)
            ( Map.cmp F _ _
            , F Map.$₂
              ( S.cmpᵗ (G.homˢ A _) (S.invᵗ (G.homˢ A _) (G.idn-lhs A _) , G.idn-rhs A _)
              , S.cmpᵗ (G.homˢ B _) (S.invᵗ (G.homˢ B _) (G.idn-rhs B _) , G.idn-lhs B _) ) )
          , S.invᵗ (G.homˢ C _) (Map.cmp F _ _) )
      }
    ; _$₁_ = λ {f₀}{f₁} p → record
      { com₂ = λ {b} → F Map.$₂ (p , S.idnᵗ (G.homˢ B _) _) }
    }
  ; idn = λ {a} → record
    { com₂ = λ {b} → Map.idn F }
  ; cmp = λ {a₀}{a₁}{a₂} g f → record
    { com₂ = λ {b} →
      S.cmpᵗ (G.homˢ C _)
        ( Map.cmp F _ _
        , F Map.$₂ (S.idnᵗ (G.homˢ A _) _ , S.invᵗ (G.homˢ B _) (G.idn-rhs B _)) )
    }
  }

open import Ambient.Groupoid.Map.Boot public
