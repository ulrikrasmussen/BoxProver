{-# LANGUAGE FlexibleContexts #-}
module LinearProof where

import           Control.Monad.State
import qualified Data.Map as M

import           Syntax

type RuleName = String

data LineRef
  = LineRefSingle Int
  | LineRefMulti Int Int
  | LineRefHole VarName
  deriving (Eq, Ord, Show)

data ProofFragment
  = VarIntroduction Int VarName
  | Line Int Formula RuleName [LineRef]
  | HoleLine Int ProofType VarName
  | Box Int Int [ProofFragment]
  deriving (Eq, Ord, Show)

data OpenLineProof = OpenLineProof [HypBinding] [ProofFragment]
  deriving (Eq, Ord, Show)

depth :: [ProofFragment] -> Int
depth = foldr max 0 . map aux
  where
    aux (VarIntroduction _ _) = 0
    aux (Line _ _ _ _) = 0
    aux (HoleLine _ _ _) = 0
    aux (Box _ _ frags) = 1 + depth frags

firstLine :: [ProofFragment] -> Int
firstLine [] = error "Empty proof fragment list"
firstLine (Line l _ _ _:_) = l
firstLine (HoleLine l _ _:_) = l
firstLine (VarIntroduction l _:_) = l
firstLine (Box l _ _:_) = l

lastLine :: [ProofFragment] -> Int
lastLine = aux . reverse
  where
    aux [] = error "Empty proof fragment list"
    aux (Line l _ _ _:_) = l
    aux (HoleLine l _ _:_) = l
    aux (VarIntroduction l _:_) = l
    aux (Box _ l' _:_) = l'

linearize :: OpenProofTerm -> OpenLineProof
linearize (OpenProofTerm hyps t) =
  OpenLineProof hyps frags
  where
    (frags, _) = evalState (linearize' t) initLinearizationState

data LinearizationState =
  LinearizationState { nextLine :: Int
                     , refScope :: M.Map RefName LineRef
                     }

initLinearizationState :: LinearizationState
initLinearizationState = LinearizationState
                         { nextLine = 1
                         , refScope = M.empty
                         }

incNextLine :: (MonadState LinearizationState m) => m ()
incNextLine = do
  modify $ \s -> s { nextLine = nextLine s + 1 }

pushScope :: (MonadState LinearizationState m) => m a -> m a
pushScope action = do
  outerScope <- gets refScope
  res <- action
  modify $ \s -> s { refScope = outerScope }
  return res

saveLineRef :: (MonadState LinearizationState m) => Maybe RefName -> LineRef -> m ()
saveLineRef mx l =
  modify $ \s -> s { refScope = maybe id (flip M.insert l) mx (refScope s) }

type LineSpan = (Int, Int)

singleLine :: (MonadState LinearizationState m)
           => Formula -> RuleName -> [LineRef]
           -> m ([ProofFragment], LineSpan)
singleLine phi rule refs = do
  l <- gets nextLine
  incNextLine
  return ([Line l phi rule refs], (l,l))

getRef :: (MonadState LinearizationState m) => RefName -> m LineRef
getRef n = do
  refs <- gets refScope
  return $ maybe (LineRefHole n) id (M.lookup n refs)

linearize' :: (MonadState LinearizationState m) => ProofTerm
           -> m ([ProofFragment],
                 LineSpan) -- ^ Indicates the line span of the last proof fragment
                           --   in the returned list.
linearize' pt =
  case pt of
  VarIntro mv pt' -> pushScope $ do
    lfrom <- gets nextLine
    incNextLine
    (frags, (_, lto)) <- linearize' pt'
    return ([Box lfrom lto (VarIntroduction lfrom (maybe "_" id mv):frags)], (lfrom, lto))
  Assumption _bt phi mx pt' -> pushScope $ do
    l <- gets nextLine
    incNextLine
    saveLineRef mx (LineRefSingle l)
    (frags, (_, lto)) <- linearize' pt'
    return ([Box l lto (Line l phi "assumption" []:frags)], (l, lto))
  Seq _btS _btT pt1 mx pt' -> do
    (frags1, (lfrom1, lto1)) <- linearize' pt1
    saveLineRef mx $ if lfrom1 == lto1 then
                       LineRefSingle lfrom1
                     else
                       LineRefMulti lfrom1 lto1
    (frags2, span') <- linearize' pt'
    return $ (frags1 ++ frags2, span')
  Copy phi ref1 -> do
    l1 <- getRef ref1
    singleLine phi "copy" [l1]
  TopI -> singleLine Top "top_i" []
  ConI phiA phiB refA refB -> do
    lA <- getRef refA
    lB <- getRef refB
    singleLine (Conj phiA phiB) "con_i" [lA, lB]
  ConE1 phiA _phiB ref -> do
    l <- getRef ref
    singleLine phiA "con_e1" [l]
  ConE2 _phiA phiB ref -> do
    l <- getRef ref
    singleLine phiB "con_e2" [l]
  DisE _phiA _phiB phiC ref1 ref2 ref3 -> do
    l1 <- getRef ref1
    l2 <- getRef ref2
    l3 <- getRef ref3
    singleLine phiC "dis_e" [l1, l2, l3]
  DisI1 phiA phiB ref -> do
    l <- getRef ref
    singleLine (Disj phiA phiB) "dis_i1" [l]
  DisI2 phiA phiB ref -> do
    l <- getRef ref
    singleLine (Disj phiA phiB) "dis_i2" [l]
  ImpI phiA phiB ref -> do
    l <- getRef ref
    singleLine (Imp phiA phiB) "imp_i" [l]
  ImpE _phiA phiB ref1 ref2 -> do
    ls <- mapM getRef [ref1, ref2]
    singleLine phiB "imp_e" ls
  NegI phiA ref -> do
    l <- getRef ref
    singleLine (Neg phiA) "neg_i" [l]
  NegE _phiA ref1 ref2 -> do
    ls <- mapM getRef [ref1, ref2]
    singleLine Bot "neg_e" ls
  BotE phiA ref -> do
    l <- getRef ref
    singleLine phiA "bot_e" [l]
  AllI mx phiA ref -> do
    l <- getRef ref
    singleLine (All (maybe "_" id mx) phiA) "all_i" [l]
  AllE mx phiA t ref -> do
    l <- getRef ref
    singleLine (maybe id (subst t) mx phiA) "all_e" [l]
  ExiI mx phiA _t ref -> do
    l <- getRef ref
    singleLine (Exi (maybe "_" id mx) phiA) "exi_i" [l]
  ExiE _mx _phiA phiB ref1 ref2 -> do
    ls <- mapM getRef [ref1, ref2]
    singleLine phiB "exi_e" ls
  EqI t -> singleLine (Eq t t) "eq_i" []
  EqE _s t mx phiA ref1 ref2 -> do
    ls <- mapM getRef [ref1, ref2]
    singleLine (maybe id (subst t) mx phiA) "eq_e" ls
  LEM phiA -> singleLine (Disj phiA (Neg phiA)) "lem" []
  NNE phiA ref -> do
    l <- getRef ref
    singleLine phiA "nne" [l]
  Hole proofType x -> do
    l <- gets nextLine
    incNextLine
    return ([HoleLine l proofType x], (l,l))
