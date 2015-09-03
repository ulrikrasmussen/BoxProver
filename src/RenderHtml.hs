{-# LANGUAGE OverloadedStrings #-}
module RenderHtml where

import           Data.String
import           Data.List (intercalate)

import           Control.Monad

import           Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import qualified Data.Set as S

import           LinearProof
import           Syntax

render :: OpenLineProof -> Html
render (OpenLineProof hyps frags) = do
  renderHyps hyps
  renderFrags frags

renderHyps :: [HypBinding] -> Html
renderHyps hyps =
  H.table ! A.class_ "hypotheses" $ mapM_ renderHyp hyps
  where
    renderHyp (HypBinding mx typ) = H.tr $ do
      H.td $ fromString $ maybe "_" id mx
      H.td $ " : "
      H.td $ fromString $ show typ

renderFrags :: [ProofFragment] -> Html
renderFrags frags =
  H.table ! A.class_ "boxproof" $ mapM_ (renderFrag 0 S.empty S.empty) frags
  where
    nboxcols = depth frags
    renderFrag d open close frag =
      let ocClass l = if S.member l open then "open" else
                        if S.member l close then "close" else
                          ""
          boxcols l inner = forM_ [1 .. nboxcols] $ \i ->
            let classes = unwords $ ["box"] ++ ["active" | i <= d]
                                    ++ [ocClass l | i >= d]
            in H.td ! A.class_ (fromString classes) $ if i == d then inner else ""
          line l lineLabel varLabel concLabel refLabel = do
            H.td ! A.class_ "line" $ fromString lineLabel
            boxcols l $ fromString varLabel
            H.td ! A.class_ (fromString $ unwords ["conc", ocClass l])
              $ fromString concLabel
            H.td ! A.class_ (fromString $ unwords ["rule", ocClass l])
              $ fromString refLabel
      in case frag of
         VarIntroduction l x -> H.tr $ line l (show l) x "" "var"
         Line l phi rule refs ->
           let showRef ref =
                 case ref of
                 LineRefSingle l' -> show l'
                 LineRefMulti l1 l2 -> concat [show l1, "-", show l2]
                 LineRefHole h -> concat ["(", h, ")"]
               refLabel = rule ++ " " ++ intercalate ", " (map showRef refs)
            in H.tr $ line l (show l) "" (prettyFormula phi) refLabel
         HoleLine l pt h -> H.tr $ line l (show l) "" (show pt) (fromString h)
         Box _ _ frags' ->
           let open' = S.insert (firstLine frags') open
               close' = S.insert (lastLine frags') close
            in mapM_ (renderFrag (d+1) open' close') frags'

type Precedence = Int

data Fixity = FixPrefix | FixInfix Assoc | FixPostfix
  deriving (Eq)

data Assoc = AssocLeft | AssocRight | AssocNone
  deriving (Show, Eq)

data Position = PosLeft | PosRight
  deriving (Show, Eq)

type OpSpec = (Precedence, Fixity)

type CtxShowS = (OpSpec, ShowS)

par :: OpSpec -> Position -> CtxShowS -> ShowS
par (pprec, pfix) cpos ((cprec, cfix), s)
  = showParen (not isUnambiguous) s
  where
    isUnambiguous =
      (cprec > pprec) || and [cprec == pprec, cfix == pfix, posCompatible]
    posCompatible =
      case cfix of
      FixInfix AssocLeft  -> cpos == PosLeft
      FixInfix AssocRight -> cpos == PosRight
      FixInfix AssocNone  -> False
      _                   -> True
      
showInfixOp :: OpSpec -> String -> CtxShowS -> CtxShowS -> CtxShowS
showInfixOp spec op t1 t2 =
  (spec, par spec PosLeft t1 . showString op . par spec PosRight t2)

showPrefixOp :: OpSpec -> String -> CtxShowS -> CtxShowS
showPrefixOp spec op t1 =
  (spec, showString op . par spec PosRight t1)

showConst :: String -> CtxShowS
showConst cnst = ((maxBound, FixPrefix), showString cnst)

prettyFormula :: Formula -> String
prettyFormula phi = let (_, s) = go phi in s ""
  where
    go p =
      case p of
      Top -> showConst "⊤"
      Bot -> showConst "⊥"
      Conj p1 p2 -> showInfixOp (3, FixInfix AssocNone) " ∧ " (go p1) (go p2)
      Disj p1 p2 -> showInfixOp (3, FixInfix AssocNone) " ∨ " (go p1) (go p2)
      Imp p1 p2  -> showInfixOp (1, FixInfix AssocRight) " → " (go p1) (go p2)
      Neg p'     -> showPrefixOp (4, FixPrefix) "¬" (go p')
      Pred q ts  -> showConst $ q ++ termsString
                    where
                      termsString = if null ts then "" else
                                      "(" ++ intercalate ", " (map prettyTerm ts) ++ ")"
      Eq t1 t2   -> showConst $ prettyTerm t1 ++ " = " ++ prettyTerm t2
      All x phi' -> showPrefixOp (2, FixPrefix) ("∀" ++ x ++ ". ") (go phi')
      Exi x phi' -> showPrefixOp (2, FixPrefix) ("∃" ++ x ++ ". ") (go phi')

prettyTerm :: Term -> String
prettyTerm (Var x) = x
prettyTerm (App f ts) =
  f ++ "(" ++ intercalate ", " (map prettyTerm ts) ++ ")"

form1 :: Formula
form1 = (Pred "p" [] `Conj` Pred "q" []) `Imp` (Pred "q" [] `Imp` (Neg (Neg (Pred "p" []))))

form2 :: Formula
form2 = Neg (form1 `Imp` Top)

form3 :: Formula
form3 = (Pred "p" []) `Conj` (Pred "q" []) `Conj` (Pred "r" [])
