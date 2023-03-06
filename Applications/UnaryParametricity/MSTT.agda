--------------------------------------------------
-- Reexporting the instance of MSTT for parametricity
--------------------------------------------------

open import Applications.UnaryParametricity.MSTT.TypeExtension.PredExtension

module Applications.UnaryParametricity.MSTT (pred-ext : PredExt) where

open import Applications.UnaryParametricity.MSTT.TypeExtension pred-ext
open import Applications.UnaryParametricity.MSTT.TermExtension pred-ext

open import Applications.UnaryParametricity.MSTT.ModeTheory public
open import Applications.UnaryParametricity.MSTT.Syntax.Type pred-ext public
open import MSTT.Syntax.Context unary-par-mode-theory par-ty-ext public
open import Applications.UnaryParametricity.MSTT.Syntax.Term pred-ext public
open import MSTT.InterpretTypes unary-par-mode-theory par-ty-ext public
open import MSTT.TCMonad public using (type-error ; ok)
open import MSTT.TypeChecker.ResultType unary-par-mode-theory par-ty-ext public
open import MSTT.TypeChecker unary-par-mode-theory par-ty-ext par-tm-ext public
open import MSTT.BasicOperations unary-par-mode-theory par-ty-ext par-tm-ext public
