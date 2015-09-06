{-# LANGUAGE OverloadedStrings #-}
module RenderHtml where

import           Data.String
import           Data.List (intersperse)

import           Control.Monad

import           Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import qualified Data.Set as S

import           LinearProof
import           Syntax

metaSpan :: String -> Html
metaSpan = (H.span ! A.class_ "metasym") . fromString

metaKindSpan :: String -> Html
metaKindSpan = (H.span ! A.class_ "metakind") . fromString

varSpan :: String -> Html
varSpan = (H.span ! A.class_ "var") . fromString

termIntroSpan :: String -> Html
termIntroSpan = (H.span ! A.class_ "termIntro") . fromString
          
parSpan :: String -> Html
parSpan = (H.span ! A.class_ "par") . fromString

opSpan :: String -> Html
opSpan = (H.span ! A.class_ "op") . fromString

predSpan :: String -> Html
predSpan = (H.span ! A.class_ "pred") . fromString

funcSpan :: String -> Html
funcSpan = (H.span ! A.class_ "func") . fromString

contextSpan :: Html -> Html
contextSpan = H.span ! A.class_ "context"

exoticSpan :: String -> Html -> Html
exoticSpan hint = H.span ! A.class_ "exotic" ! A.title (fromString hint)

holeSpan :: Html -> Html
holeSpan = H.span ! A.class_ "hole"

render :: OpenLineProof -> Html
render (OpenLineProof hyps frags) = do
--  H.h1 $ fromString "Proof body"
  renderFrags frags
  H.h1 $ fromString "Proof context"
  renderProofHypotheses hyps

parens :: Html -> Html
parens h = parSpan "(" >> h >> parSpan ")"

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
                $ refLabel
              boxcols False True l ""
            H.tr ! A.class_ "empty" $ do
              H.td ! A.class_ "line" $ " "
              boxcols True False l " "
              H.td ! A.class_ (fromString $ unwords ["conc"]) $ " "
              H.td ! A.class_ (fromString $ unwords ["rule"]) $ " "
              boxcols True True l " "
      in case frag of
         VarIntroduction l x -> line l (show l) x "" (renderReference "var" [])
         Line l phi rule refs ->
           line l (show l) "" (renderFormula phi) (renderReference rule refs)
         HoleLine l (ProofType bt) h ->
           line l (show l) "" (holeSpan $ renderBoxType bt) (holeSpan $ fromString h)
         Box l1 l2 frags' ->
           let open' = S.insert l1 open
               close' = S.insert l2 close
            in mapM_ (renderFrag (d+1) open' close') frags'

renderReference :: String -> [LineRef] -> Html
renderReference rule refs = do
  let ruleTable = (map (\(x,y) -> (x, fromString y))
                  [ ("top_i", "⊤i"), ("con_i", "∧i"), ("con_e1", "∧e₁"), ("con_e2", "∧e₂")
                  , ("dis_i1", "∨i₁"), ("dis_i2", "∨i₂"), ("dis_e","∨e"), ("imp_i","→i")
                  , ("imp_e","→e"), ("neg_i","¬i"), ("neg_e","¬e"), ("bot_e","⊥e")
                  , ("all_i","∀i"), ("all_e","∀e"), ("exi_i","∃i"), ("exi_e","∃e")
                  , ("eq_i","=i"), ("eq_e","=e"), ("lem", "LEM"), ("nne", "¬¬e")
                  ]) ++ [("var", termIntroSpan "variable")]
  let renderRef r = case r of
                    LineRefSingle l' -> fromString $ show l'
                    LineRefMulti l1 l2 -> fromString $ concat [show l1, "-", show l2]
                    LineRefHole h -> holeSpan $ fromString $ concat ["(",h,")"]
  _ <- (maybe (fromString rule) id (lookup rule ruleTable))
  _ <- fromString " "
  sequence_ (intersperse (fromString ", ") $ map renderRef refs)

renderProofHypotheses :: [HypBinding] -> Html
renderProofHypotheses hyps =
  H.table ! A.class_ "hypotheses" $ mapM_ renderHyp hyps
  where
    renderHyp (HypBinding mx typ) = H.tr $ do
      H.td $ varDecoration typ $ fromString $ maybe "_" id mx
      H.td $ " : "
      H.td $ renderObjType typ
    varDecoration typ
        | isExoticTermTy typ =
            exoticSpan ("This term has non-term dependencies and "
                        ++ "is not a valid first-order object.")
        | isExoticPropTy typ =
            exoticSpan ("This proposition has non-term dependencies and "
                             ++ "is not a valid first-order object.")
        | isHoleTy typ = holeSpan
        | otherwise = id
    isExoticTermTy (TermTy (Open termHyps TermConst)) =
                   any (not . isClosedTermTy . bindTy) termHyps
    isExoticTermTy _ = False
    isExoticPropTy (PropTy (Open propHyps PropConst)) =
                   any (not . isClosedTermTy . bindTy) propHyps
    isExoticPropTy _ = False
    isHoleTy (RefTy _) = True
    isHoleTy (BoxTy _) = True
    isHoleTy (ProofTy _) = True
    isHoleTy _ = False

renderObjType :: ObjType -> Html
renderObjType (TermTy c@(Open hyps TermConst))
    | all (isClosedTermTy . bindTy) hyps =
        let arity = length hyps in
        if arity == 0 then metaKindSpan "Constant" else
            metaKindSpan "Term" >> parens (fromString $ show arity)
    | otherwise = renderContextual (const (metaKindSpan "Term")) c
renderObjType (PropTy c@(Open hyps PropConst))
    | all (isClosedTermTy . bindTy) hyps =
        let arity = length hyps in
        if arity == 0 then metaKindSpan "Proposition" else
            metaKindSpan "Predicate" >> parens (fromString $ show arity)
    | otherwise = renderContextual (const (metaKindSpan "Proposition")) c
renderObjType (RefTy c) =
    renderContextual
      (\(RefType bt) -> metaKindSpan "Ref to " >> (renderBoxType bt))
      c
renderObjType (BoxTy c) =
    renderContextual (const (metaKindSpan "Sequent")) c
renderObjType (ProofTy c) =
    flip renderContextual c $
      \(ProofType bt) -> metaKindSpan "Proof of " >> (renderBoxType bt)

renderContextual :: (a -> Html) -> Open a -> Html
renderContextual f (Open [] a) = f a
renderContextual f (Open bindings a) = do
  f a
  H.div ! A.class_ "context-separator" $ "with context"
  H.div ! A.class_ "context" $ renderProofHypotheses bindings

type Precedence = Int
data Fixity = FixPrefix | FixInfix Assoc | FixPostfix
  deriving (Eq)
data Assoc = AssocLeft | AssocRight | AssocNone
  deriving (Show, Eq)
data Position = PosLeft | PosRight
  deriving (Show, Eq)
type OpSpec = (Precedence, Fixity)
type CtxHtml = (OpSpec, Html)

par :: OpSpec -> Position -> CtxHtml -> Html
par (pprec, pfix) cpos ((cprec, cfix), s)
  = if not isUnambiguous then parens s else s
  where
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

renderFormula :: Formula -> Html
renderFormula phi = let (_, s) = go phi in s
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
      Eq t1 t2   -> showConst $ renderTerm t1 >> predSpan " = " >> renderTerm t2
      All x phi' -> showPrefixOp (2, FixPrefix)
                                 (opSpan "∀" >> varSpan x >> fromString " ") (go phi')
      Exi x phi' -> showPrefixOp (2, FixPrefix)
                                 (opSpan "∃" >> varSpan x >> fromString " ") (go phi')

termsListHtml :: [Term] -> Html
termsListHtml ts = appList (map renderTerm ts)

-- Given a list [h1, ..., hn], renders nothing if n = 0 and otherwise renders
-- the sequence enclosed in parameters and separated by commas.
appList :: [Html] -> Html
appList [] = return ()
appList hs =
  parSpan "(" >> sequence_ (intersperse (fromString ", ") hs) >> parSpan ")"

renderTerm :: Term -> Html
renderTerm (Var x) = varSpan x
renderTerm (App f ts) = funcSpan f >> termsListHtml ts

renderBoxType :: BoxType -> Html
renderBoxType (BoxType [] (Left (x, ys))) =
  metaSpan " ⊢ " >> varSpan x >> appList (map varSpan ys)
renderBoxType (BoxType [] (Right phi)) = metaSpan " ⊢ " >> renderFormula phi
renderBoxType (BoxType as c) =
  sequence_ (intersperse (fromString ", ") (map aux as))
  >> renderBoxType (BoxType [] c)
  where
    aux (Left x) = varSpan x >> fromString " : term"
    aux (Right phi) = renderFormula phi

form1 :: Formula
form1 = (Pred "p" [] `Conj` Pred "q" []) `Imp` (Pred "q" [] `Imp` (Neg (Neg (Pred "p" []))))

form2 :: Formula
form2 = Neg (form1 `Imp` Top)

form3 :: Formula
form3 = (Pred "p" []) `Conj` (Pred "q" []) `Conj` (Pred "r" [])
