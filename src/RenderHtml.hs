{-# LANGUAGE OverloadedStrings #-}
module RenderHtml where

import           Data.String
import           Data.List (intersperse, intercalate)

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
      H.td $ prettyObjType typ

prettyObjType :: ObjType -> Html
prettyObjType (TermTy k) = fromString $ "term(" ++ show k ++ ")"
prettyObjType (PropTy k) = fromString $ "prop(" ++ show k ++ ")"
prettyObjType (RefTy (Open _ (RefType bt))) = (fromString $ "reference to ")
                                      >> prettyBoxType bt
prettyObjType (BoxTy (Open hyps BoxConst)) = fromString "sequent"
prettyObjType (ProofTy (Open hyps (ProofType pt))) =
  (fromString "proof of ") >> prettyBoxType pt

renderFrags :: [ProofFragment] -> Html
renderFrags frags =
  H.table ! A.class_ "boxproof" $ mapM_ (renderFrag 0 S.empty S.empty) frags
  where
    nboxcols = depth frags
    renderFrag d open close frag =
      let ocClass l = if S.member l open then "open" else
                        if S.member l close then "close" else
                          ""
          boxcols emptyLine rev l inner =
            forM_ ((if rev then reverse else id) [1 .. nboxcols]) $ \i ->
            let classes = unwords $ ["box"]
                                    ++ ["active" | or [i <= d && not (emptyLine && S.member l close)
                                                      ,i < d] ]
                                    ++ [ocClass l | or [i >= d && not (emptyLine || rev)
                                                       ,i > d && not emptyLine]]
            in H.td ! A.class_ (fromString classes) $ if i == d then inner else ""
          line l lineLabel varLabel concLabel refLabel = do
            H.tr $ do
              H.td ! A.class_ "line" $ fromString lineLabel
              boxcols False False l $ fromString varLabel
              H.td ! A.class_ (fromString $ unwords ["conc", ocClass l])
                $ concLabel
              H.td ! A.class_ (fromString $ unwords ["rule", ocClass l])
                $ fromString refLabel
              boxcols False True l ""
            H.tr ! A.class_ "empty" $ do
              H.td ! A.class_ "line" $ " "
              boxcols True False l " "
              H.td ! A.class_ (fromString $ unwords ["conc"]) $ " "
              H.td ! A.class_ (fromString $ unwords ["rule"]) $ " "
              boxcols True True l " "
      in case frag of
         VarIntroduction l x -> line l (show l) x "" "var"
         Line l phi rule refs ->
           let showRef ref =
                 case ref of
                 LineRefSingle l' -> show l'
                 LineRefMulti l1 l2 -> concat [show l1, "-", show l2]
                 LineRefHole h -> concat ["(", h, ")"]
               refLabel = rule ++ " " ++ intercalate ", " (map showRef refs)
            in line l (show l) "" (prettyFormula phi) refLabel
         HoleLine l (ProofType bt) h ->
           line l (show l) "" (prettyBoxType bt) (fromString h)
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

type CtxHtml = (OpSpec, Html)

metaSpan :: String -> Html
metaSpan = (H.span ! A.class_ "metasym") . fromString

varSpan :: String -> Html
varSpan = (H.span ! A.class_ "var") . fromString

parSpan :: String -> Html
parSpan = (H.span ! A.class_ "par") . fromString

opSpan :: String -> Html
opSpan = (H.span ! A.class_ "op") . fromString

predSpan :: String -> Html
predSpan = (H.span ! A.class_ "pred") . fromString

funcSpan :: String -> Html
funcSpan = (H.span ! A.class_ "func") . fromString

par :: OpSpec -> Position -> CtxHtml -> Html
par (pprec, pfix) cpos ((cprec, cfix), s)
  = htmlPar (not isUnambiguous) s
  where
    htmlPar False h = h
    htmlPar True h = parSpan "(" >> h >> parSpan ")"
    isUnambiguous =
      (cprec > pprec) || and [cprec == pprec, cfix == pfix, posCompatible]
    posCompatible =
      case cfix of
      FixInfix AssocLeft  -> cpos == PosLeft
      FixInfix AssocRight -> cpos == PosRight
      FixInfix AssocNone  -> False
      _                   -> True
      
showInfixOp :: OpSpec -> Html -> CtxHtml -> CtxHtml -> CtxHtml
showInfixOp spec op t1 t2 =
  (spec, par spec PosLeft t1 >> op >> par spec PosRight t2)

showPrefixOp :: OpSpec -> Html -> CtxHtml -> CtxHtml
showPrefixOp spec op t1 =
  (spec, op >> par spec PosRight t1)

showConst :: Html -> CtxHtml
showConst cnst = ((maxBound, FixPrefix), cnst)

prettyFormula :: Formula -> Html
prettyFormula phi = let (_, s) = go phi in s
  where
    go p =
      case p of
      Top -> showConst "⊤"
      Bot -> showConst "⊥"
      Conj p1 p2 -> showInfixOp (3, FixInfix AssocNone) (opSpan " ∧ ") (go p1) (go p2)
      Disj p1 p2 -> showInfixOp (3, FixInfix AssocNone) (opSpan " ∨ ") (go p1) (go p2)
      Imp p1 p2  -> showInfixOp (1, FixInfix AssocRight) (opSpan " → ") (go p1) (go p2)
      Neg p'     -> showPrefixOp (4, FixPrefix) (opSpan "¬") (go p')
      Pred q ts  -> showConst $ predSpan q >> termsListHtml ts
      Eq t1 t2   -> showConst $ prettyTerm t1 >> predSpan " = " >> prettyTerm t2
      All x phi' -> showPrefixOp (2, FixPrefix)
                                 (opSpan "∀" >> varSpan x >> fromString " ") (go phi')
      Exi x phi' -> showPrefixOp (2, FixPrefix)
                                 (opSpan "∃" >> varSpan x >> fromString " ") (go phi')

termsListHtml :: [Term] -> Html
termsListHtml ts = appList (map prettyTerm ts)

-- Given a list [h1, ..., hn], renders nothing if n = 0 and otherwise renders
-- the sequence enclosed in parameters and separated by commas.
appList :: [Html] -> Html
appList [] = return ()
appList hs =
  parSpan "(" >> sequence_ (intersperse (fromString ", ") hs) >> parSpan ")"

prettyTerm :: Term -> Html
prettyTerm (Var x) = varSpan x
prettyTerm (App f ts) = funcSpan f >> termsListHtml ts

prettyBoxType :: BoxType -> Html
prettyBoxType (BoxType [] (Left (x, ys))) =
  metaSpan " ⊢ " >> varSpan x >> appList (map varSpan ys)
prettyBoxType (BoxType [] (Right phi)) = metaSpan " ⊢ " >> prettyFormula phi
prettyBoxType (BoxType as c) =
  sequence_ (intersperse (fromString ", ") (map aux as))
  >> prettyBoxType (BoxType [] c)
  where
    aux (Left x) = varSpan x >> fromString " : term"
    aux (Right phi) = prettyFormula phi

form1 :: Formula
form1 = (Pred "p" [] `Conj` Pred "q" []) `Imp` (Pred "q" [] `Imp` (Neg (Neg (Pred "p" []))))

form2 :: Formula
form2 = Neg (form1 `Imp` Top)

form3 :: Formula
form3 = (Pred "p" []) `Conj` (Pred "q" []) `Conj` (Pred "r" [])
