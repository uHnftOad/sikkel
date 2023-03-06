--------------------------------------------------
-- Reexporting the syntax for terms in parametric type theory
--   + definition of some synonyms.
--------------------------------------------------

open import Applications.UnaryParametricity.MSTT.TypeExtension.PredExtension

module Applications.UnaryParametricity.MSTT.Syntax.Term (pred-ext : PredExt) where

open import Data.Unit

open import Applications.UnaryParametricity.MSTT.ModeTheory
open import Applications.UnaryParametricity.MSTT.TypeExtension pred-ext
open import Applications.UnaryParametricity.MSTT.TermExtension pred-ext


import MSTT.Syntax.Term unary-par-mode-theory par-ty-ext par-tm-ext as ParTerm
open ParTerm using (ext)
open ParTerm public hiding (ext)

pattern from-pred c a p = ext (from-pred-code c a p) tt
pattern from-pred1 c1 c2 f p = ext (from-pred1-code c1 c2 f p) tt
pattern from-pred2 c1 c2 c3 f p = ext (from-pred2-code c1 c2 c3 f p) tt
