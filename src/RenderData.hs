{-# LANGUAGE OverloadedStrings #-}
module RenderData where

import Control.Monad.Except
import Data.Text

import Syntax
import LinearProof

ctor :: Text -> [Text] -> Text
ctor c ps = c `append` "(" `append` (intercalate "," ps) `append` ")"

lst :: [Text] -> Text
lst xs = "[" `append` (intercalate "," xs) `append` "]"

int :: Int -> Text
int = pack . show

str :: Text -> Text
str x = "\"" `append` x `append` "\""

renderLinearProof :: Sequent -> [ProofFragment] -> Either String Text
renderLinearProof seq' frags = do
  seqT <- renderSequent seq'
  fragsT <- lst <$> mapM renderFragment frags
  return $ ctor "" ["boxproof", seqT, fragsT]

renderSequent :: Sequent -> Either String Text
renderSequent (Sequent ant con) = do
  antFormulas <- catchError (sequence ant) (\_ -> Left "Cannot export sequent with free term variables")
  conFormula <- either (const $ Left "Cannot export sequent with hole in it") Right con
  antT <- lst <$> mapM renderFormula antFormulas
  conT <- renderFormula conFormula
  return $ ctor "" [antT, conT]

renderFragment :: ProofFragment -> Either String Text
renderFragment (Line i (Sequent _ con) ruleName refs) = do
  conFormula <- either (const $ Left "Cannot export sequent with hole in it") Right con
  conT <- ctor "SOME" . (:[]) <$> renderFormula conFormula
  ruleNameT <- renderRuleName ruleName
  refsT <- lst <$> mapM renderLineRef refs
  return $ ctor "" [conT, ruleNameT, refsT, str . int $ i]
renderFragment (Box i j frags) = do
  fragTs <- mapM renderFragment frags
  let discharge = ctor "" ["NONE", "Dis", lst [ctor "Line" [str . int $ i]], str ""]
  let ls = fragTs ++ [discharge]
  return $ intercalate "," ls
renderFragment (HoleLine _ _ _ _) = throwError "Cannt export line holes"
renderFragment (VarIntroduction _ _) = throwError "Cannot export variable introduction"

renderRuleName :: RuleName -> Either String Text
renderRuleName rn =
  case rn of
    "assumption" -> return "Ass"
    "premise" -> return "Prm"
    "copy" -> return "Cpy"
    "con_i" -> return "Ain"
    "con_e1" -> return "Ae1"
    "con_e2" -> return "Ae2"
    "dis_i1" -> return "Oi1"
    "dis_i2" -> return "Oi2"
    "dis_e" -> return "Oel"
    "imp_i" -> return "Iin"
    "imp_e" -> return "Iel"
    "neg_i" -> return "Nin"
    "neg_e" -> return "Nel"
    "nne" -> return "Del"
    "nni" -> return "Din"
    "bot_e" -> return "Bel"
    "pbc" -> return "Pbc"
    "mt" -> return "Mod"
    "lem" -> return "Lem"
    _ -> throwError $ "Cannot export rule name: " ++ show rn

renderLineRef :: LineRef -> Either String Text
renderLineRef (LineRefSingle i) = return $ ctor "Line" [str . int $ i]
renderLineRef (LineRefMulti i j) = return $ ctor "Box" [str . int $ i, str . int $ j]
renderLineRef (LineRefHole _) = throwError "Cannot export reference hole"

renderFormula :: Formula -> Either String Text
renderFormula = go
  where
    go Top = return "TOP"
    go Bot = return "BOT"
    go (Conj phi1 phi2) = return . ctor "AND" =<< mapM go [phi1, phi2]
    go (Disj phi1 phi2) = return . ctor "OR" =<< mapM go [phi1, phi2]
    go (Imp phi1 phi2) = return . ctor "IMP" =<< mapM go [phi1, phi2]
    go (Neg phi) = return . ctor "NEG" . (:[]) =<< go phi
    go (Pred p []) = return $ ctor "Atom" [pack p]
    go (Pred _ _) = throwError "Cannot export predicates"
    go (Eq _ _) = throwError "Cannot export equality predicates"
    go (All _ _) = throwError "Cannot export universal quantifiers"
    go (Exi _ _) = throwError "Cannot export existential quantifiers"
