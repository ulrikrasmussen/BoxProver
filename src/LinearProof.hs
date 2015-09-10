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
  | Line Int Sequent RuleName [LineRef]
  | HoleLine Int ProofType VarName [Obj]
  | Box Int Int [ProofFragment]
  deriving (Eq, Ord, Show)

data OpenLineProof = OpenLineProof [HypBinding] [ProofFragment]
  deriving (Eq, Ord, Show)

isClosedProof :: OpenLineProof -> Bool
isClosedProof (OpenLineProof bs _) = all (not . bindImplicit) bs

depth :: [ProofFragment] -> Int
depth = foldr max 0 . map aux
  where
    aux (VarIntroduction _ _) = 0
    aux (Line _ _ _ _) = 0
    aux (HoleLine _ _ _ _) = 0
    aux (Box _ _ frags) = 1 + depth frags

linearize :: Open (ProofTerm, Sequent) -> OpenLineProof
linearize (Open hyps (t, sq)) =
  OpenLineProof hyps (flatten True frags)
  where
    (frags, _) = evalState (linearize' t sq) initLinearizationState
    flatten _ [] = []
    flatten p [Box _ _ frags'] = flatten p frags'
    flatten p (VarIntroduction l x:frags') =
        VarIntroduction l x:flatten p frags'
    flatten p (Line l phi "assumption" refs:frags') =
        let rule = if p then "premise" else "assumption"
        in Line l phi rule refs:flatten p frags'
    flatten _ frags' = map flatten' frags'

    flatten' (Box l1 l2 frags') = Box l1 l2 (flatten False frags')
    flatten' l = l

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
           => Sequent -> RuleName -> [LineRef]
           -> m ([ProofFragment], LineSpan)
singleLine sq rule refs = do
  l <- gets nextLine
  incNextLine
  return ([Line l sq rule refs], (l,l))

getRef :: (MonadState LinearizationState m) => RefName -> m LineRef
getRef n = do
  refs <- gets refScope
  return $ maybe (LineRefHole n) id (M.lookup n refs)

linearize' :: (MonadState LinearizationState m)
           => ProofTerm
           -> Sequent
           -> m ([ProofFragment],
                 LineSpan) -- ^ Indicates the line span of the last proof fragment
                           --   in the returned list.
linearize' pt sq =
  case pt of
  VarIntro sq' mv pt' -> pushScope $ do
    lfrom <- gets nextLine
    incNextLine
    (frags, (_, lto)) <- linearize' pt' sq'
    return ([Box lfrom lto (VarIntroduction lfrom (maybe "_" id mv):frags)], (lfrom, lto))
  Assumption sq' phi mx pt' -> pushScope $ do
    l <- gets nextLine
    incNextLine
    saveLineRef mx (LineRefSingle l)
    (frags, (_, lto)) <- linearize' pt' sq'
    return ([Box l lto (Line l (Sequent [] (Right phi)) "assumption" []:frags)], (l, lto))
  Seq sq1 sq2 pt1 mx pt' -> do
    (frags1, (lfrom1, lto1)) <- linearize' pt1 sq1
    saveLineRef mx $ if lfrom1 == lto1 then
                       LineRefSingle lfrom1
                     else
                       LineRefMulti lfrom1 lto1
    (frags2, span') <- linearize' pt' sq2
    return $ (frags1 ++ frags2, span')
  Copy _phi ref1 -> do
    l1 <- getRef ref1
    singleLine sq "copy" [l1]
  TopI -> singleLine sq "top_i" []
  ConI _phiA _phiB refA refB -> do
    lA <- getRef refA
    lB <- getRef refB
    singleLine sq "con_i" [lA, lB]
  ConE1 _phiA _phiB ref -> do
    l <- getRef ref
    singleLine sq "con_e1" [l]
  ConE2 _phiA _phiB ref -> do
    l <- getRef ref
    singleLine sq "con_e2" [l]
  DisE _phiA _phiB _phiC ref1 ref2 ref3 -> do
    l1 <- getRef ref1
    l2 <- getRef ref2
    l3 <- getRef ref3
    singleLine sq "dis_e" [l1, l2, l3]
  DisI1 _phiA _phiB ref -> do
    l <- getRef ref
    singleLine sq "dis_i1" [l]
  DisI2 _phiA _phiB ref -> do
    l <- getRef ref
    singleLine sq "dis_i2" [l]
  ImpI _phiA _phiB ref -> do
    l <- getRef ref
    singleLine sq "imp_i" [l]
  ImpE _phiA _phiB ref1 ref2 -> do
    ls <- mapM getRef [ref1, ref2]
    singleLine sq "imp_e" ls
  NegI _phiA ref -> do
    l <- getRef ref
    singleLine sq "neg_i" [l]
  NegE _phiA ref1 ref2 -> do
    ls <- mapM getRef [ref1, ref2]
    singleLine sq "neg_e" ls
  BotE _phiA ref -> do
    l <- getRef ref
    singleLine sq "bot_e" [l]
  AllI _mx _phiA ref -> do
    l <- getRef ref
    singleLine sq "all_i" [l]
  AllE _mx _phiA _t ref -> do
    l <- getRef ref
    singleLine sq "all_e" [l]
  ExiI _mx _phiA _t ref -> do
    l <- getRef ref
    singleLine sq "exi_i" [l]
  ExiE _mx _phiA _phiB ref1 ref2 -> do
    ls <- mapM getRef [ref1, ref2]
    singleLine sq "exi_e" ls
  EqI _t -> singleLine sq "eq_i" []
  EqE _s _t _mx _phiA ref1 ref2 -> do
    ls <- mapM getRef [ref1, ref2]
    singleLine sq "eq_e" ls
  LEM _phiA -> singleLine sq "lem" []
  NNE _phiA ref -> do
    l <- getRef ref
    singleLine sq "nne" [l]
  NNI _phiA ref -> do
    l <- getRef ref
    singleLine sq "nni" [l]
  PBC _phiA ref -> do
    l <- getRef ref
    singleLine sq "pbc" [l]
  MT _phiA _phiB ref1 ref2 -> do
    ls <- mapM getRef [ref1, ref2]
    singleLine sq "mt" ls
  Hole proofType x args -> do
    l <- gets nextLine
    incNextLine
    return ([HoleLine l proofType x args], (l,l))
