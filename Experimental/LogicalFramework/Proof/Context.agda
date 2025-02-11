module Experimental.LogicalFramework.Proof.Context where

open import Data.String as Str
open import Function using (id)
import Relation.Binary.PropositionalEquality as Ag
open import Relation.Nullary

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
import Model.Modality as M

open import Experimental.LogicalFramework.MSTT
open import Experimental.LogicalFramework.Formula
open import Experimental.LogicalFramework.Proof.CheckingMonad
open import Experimental.LogicalFramework.Proof.Equality

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : Formula Γ
  x y : String


-- A proof context can, apart from MSTT variables, also consist of formulas (assumptions).
data ProofCtx (m : Mode) : Set
to-ctx : ProofCtx m → Ctx m

infixl 2 _,,ᵛ_∣_∈_ _,,ᶠ_∣_∈_
data ProofCtx m where
  [] : ProofCtx m
  _,,ᵛ_∣_∈_ : (Ξ : ProofCtx m) (μ : Modality n m) (x : String) (T : Ty n) → ProofCtx m
  _,,ᶠ_∣_∈_ : (Ξ : ProofCtx m) (μ : Modality n m) (x : String) (φ : Formula ((to-ctx Ξ) ,lock⟨ μ ⟩)) → ProofCtx m
  _,lock⟨_⟩ : (Ξ : ProofCtx n) (μ : Modality m n) → ProofCtx m

to-ctx []               = ◇
to-ctx (Ξ ,,ᵛ μ ∣ x ∈ T) = (to-ctx Ξ) ,, μ ∣ x ∈ T
to-ctx (Ξ ,,ᶠ _ ∣ _ ∈ _) = to-ctx Ξ
to-ctx (Ξ ,lock⟨ μ ⟩)   = (to-ctx Ξ) ,lock⟨ μ ⟩

private variable
  Ξ : ProofCtx m


-- In the same way as variables in MSTT, assumptions are internally
--  referred to using De Bruijn indices, but we keep track of their
--  names. The (proof-relevant) predicate Assumption x μ κ Ξ expresses
--  that an assumption with name x is present in proof context Ξ under
--  modality μ and with κ the composition of all locks to the right of
--  x. Note that we do not keep track of the formula in the Assumption
--  type (in contrast to the type of variables in MSTT).
data Assumption (x : String) (μ : Modality n o) : Modality m o → ProofCtx m → Set where
  azero : Assumption x μ 𝟙 (Ξ ,,ᶠ μ ∣ x ∈ φ)
  asuc  : Assumption x μ κ Ξ → Assumption x μ κ (Ξ ,,ᶠ ρ ∣ y ∈ ψ)
  skip-var : Assumption x μ κ Ξ → Assumption x μ κ (Ξ ,,ᵛ ρ ∣ y ∈ T)
  skip-lock : (ρ : Modality m p) → Assumption x μ κ Ξ → Assumption x μ (κ ⓜ ρ) (Ξ ,lock⟨ ρ ⟩)

lookup-assumption' : Assumption x μ κ Ξ → (ρ : Modality _ _) →
                     TwoCell μ (κ ⓜ ρ) → Formula ((to-ctx Ξ) ,lock⟨ ρ ⟩)
lookup-assumption' (azero {φ = φ}) ρ α = φ [ key-sub (◇ ,lock⟨ ρ ⟩) (◇ ,lock⟨ _ ⟩) α ]frm
lookup-assumption' (asuc a) ρ α = lookup-assumption' a ρ α
lookup-assumption' (skip-var a) ρ α = (lookup-assumption' a ρ α) [ π ,slock⟨ ρ ⟩ ]frm
lookup-assumption' (skip-lock {κ = κ} ρ' a) ρ α = unfuselocks-frm (lookup-assumption' a (ρ' ⓜ ρ) (transp-cellʳ (mod-assoc κ) α))

lookup-assumption : Assumption x μ κ Ξ → TwoCell μ κ → Formula (to-ctx Ξ)
lookup-assumption a α = unlock𝟙-frm (lookup-assumption' a 𝟙 (transp-cellʳ (Ag.sym mod-unitʳ) α))

record ContainsAssumption (x : String) (μ : Modality n o) (Ξ : ProofCtx m) : Set where
  constructor contains-assumption
  field
    locks : Modality m o
    as : Assumption x μ locks Ξ

map-contains : {m m' : Mode} {x : String} {μ : Modality n o}
               {Ξ : ProofCtx m} {Ξ' : ProofCtx m'}
               (F : Modality m o → Modality m' o) →
               (∀ {κ} → Assumption x μ κ Ξ → Assumption x μ (F κ) Ξ') →
               ContainsAssumption x μ Ξ → ContainsAssumption x μ Ξ'
map-contains F G (contains-assumption locks as) = contains-assumption (F locks) (G as)

contains-assumption? : (x : String) (μ : Modality n o) (Ξ : ProofCtx m) →
                       PCM (ContainsAssumption x μ Ξ)
contains-assumption? x μ [] = throw-error "Assumption not found in context."
contains-assumption? x μ (Ξ ,,ᵛ ρ ∣ y ∈ T) = map-contains id skip-var <$> contains-assumption? x μ Ξ
contains-assumption? x μ (Ξ ,,ᶠ ρ ∣ y ∈ φ) with x Str.≟ y
contains-assumption? {n = n} {o} {m} x μ (_,,ᶠ_∣_∈_ {n = n'} Ξ ρ .x φ) | yes refl = do
  refl ← m =m? o
  refl ← n =m? n'
  refl ← μ =mod? ρ
  return (contains-assumption 𝟙 azero)
contains-assumption? x μ (Ξ ,,ᶠ ρ ∣ y ∈ φ) | no ¬x=y = map-contains id asuc <$> contains-assumption? x μ Ξ
contains-assumption? x μ (Ξ ,lock⟨ ρ ⟩) = map-contains (_ⓜ ρ) (skip-lock ρ) <$> contains-assumption? x μ Ξ


⟦_⟧pctx : ProofCtx m → SemCtx ⟦ m ⟧mode
to-ctx-subst : (Ξ : ProofCtx m) → ⟦ Ξ ⟧pctx M.⇒ ⟦ to-ctx Ξ ⟧ctx

⟦ [] ⟧pctx = M.◇
⟦ Ξ ,,ᵛ μ ∣ _ ∈ T ⟧pctx = ⟦ Ξ ⟧pctx M.,, M.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩
⟦ Ξ ,,ᶠ μ ∣ _ ∈ φ ⟧pctx = ⟦ Ξ ⟧pctx M.,, (M.⟨ ⟦ μ ⟧mod ∣ ⟦ φ ⟧frm ⟩ M.[ to-ctx-subst Ξ ])
⟦ Ξ ,lock⟨ μ ⟩ ⟧pctx = M.lock ⟦ μ ⟧mod ⟦ Ξ ⟧pctx

to-ctx-subst [] = M.id-subst M.◇
to-ctx-subst (Ξ ,,ᵛ μ ∣ _ ∈ T) = ((to-ctx-subst Ξ) M.⊹) M.⊚ M._≅ᶜ_.to (M.,,-cong (ty-natural ⟨ μ ∣ T ⟩))
to-ctx-subst (Ξ ,,ᶠ _ ∣ _ ∈ _) = to-ctx-subst Ξ M.⊚ M.π
to-ctx-subst (Ξ ,lock⟨ μ ⟩) = M.lock-fmap ⟦ μ ⟧mod (to-ctx-subst Ξ)
