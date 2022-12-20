{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Test.Cardano.Ledger.Constrained.Spec where

-- import Debug.Trace (trace)
-- import Data.Ratio ((%))

import Cardano.Ledger.BaseTypes (EpochNo)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Credential (Credential)
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.Era (Era (EraCrypto))
import Cardano.Ledger.Keys (KeyHash, KeyRole (StakePool, Staking))
import Cardano.Ledger.PoolParams (PoolParams)
import Data.Graph
import Data.Kind (Type)
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Pulse (foldlM')
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Universe (Any (..), Some (..), cmpIndex)
import Data.Word (Word64)
import Test.Cardano.Ledger.Constrained.Combinators
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Monad
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Core.Arbitrary ()
import Test.Cardano.Ledger.Generic.Proof
  ( Evidence (..),
    Mock,
    Proof (..),
    ShelleyEra,
  )
import Test.Cardano.Ledger.Shelley.Serialisation.EraIndepGenerators ()
import Test.QuickCheck hiding (Fixed, total)

-- ===============================================================================

type Shell = ShelleyEra Mock

-- ==================================================

data Literal era t where
  Lit :: Rep era t -> t -> Literal era t

data Term era t where
  Fixed :: Literal era t -> Term era t
  Var :: V era t -> Term era t
  Dom :: Ord a => Term era (Map a b) -> Term era (Set a)
  Rng :: (Ord a, Ord b) => Term era (Map a b) -> Term era (Set b)

infix 4 :=:

infix 4 :<=:

data Pred era where
  Sized :: Sizeable t => Term era Word64 -> Term era t -> Pred era
  (:=:) :: Eq a => Term era a -> Term era a -> Pred era
  (:<=:) :: Ord a => Term era (Set a) -> Term era (Set a) -> Pred era
  SumsTo :: Summable r => Term era r -> [Sum (Term era) r] -> Pred era
  Random :: Term era t -> Pred era
  HasDom :: Ord d => Term era (Map d r) -> Term era (Set d) -> Pred era

data Sum f t where
  SumMap :: Summable rng => f (Map dom rng) -> Sum f rng
  SumSet :: Summable rng => f (Set rng) -> Sum f rng
  One :: Summable t => f t -> Sum f t

-- | The defining purpose of Sum's, you can add them up
sums :: Summable t => Sum Id t -> t
sums (One (Id x)) = x
sums (SumMap (Id m)) = Map.foldl' plusSum zeroSum m
sums (SumSet (Id m)) = Set.foldl' plusSum zeroSum m

infixl 0 :$

data Target era t where
  Simple :: Term era t -> Target era t
  Constant :: Literal era t -> Target era t
  Named :: V era t -> Target era t
  (:$) :: Target era (a -> b) -> Target era a -> Target era b
  Constr :: String -> (a -> b) -> Target era (a -> b)

-- ===================================

showL :: (t -> String) -> [Char] -> [t] -> [Char]
showL _f _sep [] = ""
showL f _sep [t] = f t
showL f sep (t : ts) = f t ++ sep ++ showL f sep ts

instance Show (Literal era t) where
  show (Lit r k) = synopsis r k

instance Show (Term era t) where
  show (Fixed k) = "(Fixed " ++ show k ++ ")"
  show (Var (V nm _rep)) = nm -- ++ "::" ++ show _rep
  show (Dom x) = "(dom " ++ show x ++ ")"
  show (Rng x) = "(rng " ++ show x ++ ")"
  showList xs ans = unlines (ans : (map show xs))

instance Show (Pred era) where
  show (Sized n t) = "Sized " ++ show n ++ " " ++ show t
  show (x :=: y) = show x ++ " = " ++ show y
  show (x :<=: y) = show x ++ " ⊆  " ++ show y
  show (SumsTo c m) = show c ++ " =∑= " ++ showL show " + " m
  show (Random x) = "Random " ++ show x
  show (HasDom m s) = "HasDomain " ++ show m ++ " " ++ show s
  showList xs ans = unlines (ans : (map show xs))

instance Show (Target era t) where
  show (Constant v) = show v
  show (Constr nm _f) = nm
  show (Simple x) = show x
  show (Named (V nm rep)) = nm ++ "::" ++ show rep
  show (f :$ x) = "(" ++ show f ++ " :$ " ++ showL pp " :$ " (args x) ++ ")"
    where
      pp :: Any (Target era) -> String
      pp (Any spec) = show spec

args :: Target era t -> [Any (Target era)]
args (x :$ xs) = (Any x) : args xs
args other = [Any other]

-- ===========================================================
-- Sizeable Class

class Show t => Sizeable t where
  getsize :: t -> Word64

instance (Show dom, Show rng) => Sizeable (Map dom rng) where
  getsize m = fromIntegral (Map.size m)

instance Show t => Sizeable (Set t) where
  getsize m = fromIntegral (Set.size m)

instance Sizeable Coin where
  getsize (Coin n) = fromIntegral n

-- ===========================================================
-- Sum Class

class (Ord t, Show t) => Summable t where
  zeroSum :: t
  plusSum :: t -> t -> t
  partition :: Int -> t -> Gen [t]

instance Summable Int where
  zeroSum = 0
  plusSum = (+)
  partition = intPartition 1

instance Summable Coin where
  zeroSum = Coin 0
  plusSum = (<>)
  partition = coinPartition (Coin 1)

instance Summable Rational where
  zeroSum = 0
  plusSum = (+)
  partition = rationalPartition

instance Show (Sum (Term era) t) where
  show (SumMap x) = "sum " ++ show x
  show (SumSet x) = "sum " ++ show x
  show (One x) = show x

sumMapFromSet :: (Ord a, Summable b) => b -> Set a -> Gen (Map a b)
sumMapFromSet total set = do
  ranges <- partition (Set.size set) total
  pure $ Map.fromList (zip (Set.toList set) ranges)

-- | Generate a list of length 'size' that sums to 'total', where the minimum element is (>= 'smallest')
intPartition :: Int -> Int -> Int -> Gen [Int]
intPartition smallest size total
  | size > total = error ("Can't partition " ++ show total ++ " into " ++ show size ++ " positive pieces.")
  | size < 1 = error ("Can only make a partion of positive number of pieces: " ++ show size)
  | smallest < 0 = error ("The minimum choice must be positive : " ++ show smallest)
  | smallest * size > total =
      error
        ("Can't partition " ++ show total ++ " into " ++ show size ++ " pieces, each (>= " ++ show smallest ++ ")")
  | total < 1 = error ("Total must be positive: " ++ show total)
  | otherwise =
      let mean = total `div` size + 1
          go 1 total1
            | total1 < 1 = error ("Ran out of choices(2), total went negative: " ++ show total1)
            | otherwise = pure [total1]
          go 2 total1 = do
            z <- chooseInt (smallest, total1 - 1)
            pure [z, total1 - z]
          go size1 total1 = do
            let hi =
                  min
                    (max 1 mean)
                    (total1 - (size1 - 1))
            x <- chooseInt (smallest, hi)
            xs <- go (size1 - 1) (total1 - x)
            pure (x : xs)
       in do
            ws <- go size total
            shuffle ws

gauss :: Floating a => a -> a -> a -> a
gauss mean stdev x = (1 / (stdev * (sqrt (2 * pi)))) * exp (negate ((1 / 2) * ((x - mean) / stdev) ** 2))

rationalPartition :: Int -> Rational -> Gen [Rational]
rationalPartition n total = do
  let iScale = n * 1000
      rScale :: Rational
      rScale = fromIntegral iScale
  is <- intPartition (iScale `div` n) n (round (total * rScale))
  pure (map ((/ rScale) . fromIntegral) is)

coinPartition :: Coin -> Int -> Coin -> Gen [Coin]
coinPartition (Coin smallest) size (Coin total) =
  map (Coin . fromIntegral) <$> intPartition (fromIntegral smallest) size (fromIntegral total)

sumMap :: Summable t => Map a t -> t
sumMap m = Map.foldl' plusSum zeroSum m

sumSet :: Summable t => Set t -> t
sumSet m = Set.foldl' plusSum zeroSum m

-- ===================================================
-- Computing the variables (V era t) in a Term, Pred, Target
-- Their are no binders in any of these, so this is not so difficult
-- But (V era t) may have different 't', so we hide 't' in 'Name'

varsOfTerm :: Set (Name era) -> Term era t -> Set (Name era)
varsOfTerm ans s = case s of
  Fixed _ -> ans
  Var v@(V _ _) -> Set.insert (Name v) ans
  Dom x -> varsOfTerm ans x
  Rng x -> varsOfTerm ans x

vars :: Term era t -> Set (Name era)
vars x = varsOfTerm Set.empty x

varsOfTarget :: Set (Name era) -> Target era t -> Set (Name era)
varsOfTarget ans s = case s of
  (a :$ b) -> varsOfTarget (varsOfTarget ans a) b
  (Simple x) -> varsOfTerm ans x
  Named v@(V _ _) -> Set.insert (Name v) ans
  (Constant _) -> ans
  (Constr _ _) -> ans

varsOfPred :: Set (Name era) -> Pred era -> Set (Name era)
varsOfPred ans s = case s of
  Sized a b -> varsOfTerm (varsOfTerm ans a) b
  (a :=: b) -> varsOfTerm (varsOfTerm ans a) b
  (a :<=: b) -> varsOfTerm (varsOfTerm ans a) b
  SumsTo x xs -> List.foldl' varsOfSum (varsOfTerm ans x) xs
  Random x -> varsOfTerm ans x
  HasDom a b -> varsOfTerm (varsOfTerm ans a) b

varsOfSum :: Set (Name era) -> Sum (Term era) r -> Set (Name era)
varsOfSum ans y = case y of
  One x -> varsOfTerm ans x
  SumSet x -> varsOfTerm ans x
  SumMap x -> varsOfTerm ans x

-- =====================================================
-- Subtitution of (V era t) inside of (Spec era t)

substToEnv :: [SubItem era] -> Env era -> Env era
substToEnv [] ans = ans
substToEnv ((SubItem v (Fixed (Lit rep t))) : more) ans =
  substToEnv more (storeVar v t ans)
substToEnv ((SubItem _ e) : more) ans = error ("Not Literal expr in substToEnv: " ++ show e)

data SubItem era where SubItem :: V era t -> Term era t -> SubItem era

instance Show (SubItem era) where
  show (SubItem (V nm rep) expr) = pad 14 nm ++ " = " ++ show expr

type Subst era = [SubItem era]

extend :: V era t -> Term era t -> Subst era -> Subst era
extend v k xs = (SubItem v k) : xs

findV :: Subst era -> V era t -> Term era t
findV [] (V n rep1) = Var (V n rep1) -- If its not in the Subst, return the Var
findV (SubItem (V n2 rep2) kn : more) v@(V n1 rep1) =
  if not (n1 == n2)
    then findV more v
    else case testEql rep1 rep2 of
      Just Refl -> kn
      Nothing ->
        error
          ( "In findV, we found: "
              ++ n1
              ++ ", but the types did not match. "
              ++ show rep1
              ++ " =/= "
              ++ show rep2
          )

substTerm :: Subst era -> Term era t -> Term era t
substTerm sub (Var v) = findV sub v
substTerm _ (Fixed k) = Fixed k
substTerm sub (Dom x) = Dom (substTerm sub x)
substTerm sub (Rng x) = Rng (substTerm sub x)

substPred :: Subst era -> Pred era -> Pred era
substPred sub (Sized a b) = Sized (substTerm sub a) (substTerm sub b)
substPred sub (a :=: b) = (substTerm sub a) :=: (substTerm sub b)
substPred sub (a :<=: b) = (substTerm sub a) :<=: (substTerm sub b)
substPred sub (SumsTo a b) = SumsTo (substTerm sub a) (map (substSum sub) b)
substPred sub (Random x) = Random (substTerm sub x)
substPred sub (HasDom a b) = HasDom (substTerm sub a) (substTerm sub b)

substSum :: Subst era -> Sum (Term era) t -> Sum (Term era) t
substSum sub (One x) = One (substTerm sub x)
substSum sub (SumMap x) = SumMap (substTerm sub x)
substSum sub (SumSet x) = SumSet (substTerm sub x)

substTarget :: Subst era -> Target era t -> Target era t
substTarget sub (Simple e) = case substTerm sub e of
  Fixed f -> Constant f
  Var x -> Named x
  other -> Simple other
substTarget _ (Constant x) = Constant x
substTarget sub (a :$ b) = substTarget sub a :$ substTarget sub b
substTarget _ (Constr n f) = Constr n f
substTarget sub (Named v) = case findV sub v of
  Var x -> Named x
  other -> Simple other

-- ======================================================
-- Evaluators

-- | Symbolic evaluation with free variables, that cause failures
eval :: Term era t -> Typed (Dyn era)
eval (Fixed (Lit r x)) = pure (Dyn r x)
eval (Dom x) = case eval x of
  Typed (Right (Dyn (MapR d r) m)) -> pure (Dyn (SetR d) (Map.keysSet m))
  Typed other -> failT ["In " ++ show (Dom x) ++ ", " ++ show x ++ " does not eval to a Map type"]
eval (Rng (Var (V nm _))) = failT ["Can't eval variable: " ++ nm]
eval (Rng (Fixed (Lit (MapR _ r) m))) = pure (Dyn (SetR r) (Set.fromList (Map.elems m)))
eval (Var (V nm _)) = failT ["Can't eval unbound variable: " ++ nm]
eval x = failT ["Can't eval Term: " ++ show x]

-- | Evidence that 'expr' has type 'r1'
evalWith :: Rep era t -> Term era s -> Typed t
evalWith r1 expr = explain ("(evalWith " ++ show r1 ++ " " ++ show expr ++ ") fails") $ do
  (Dyn r2 x) <- eval expr
  Refl <- sameRep r1 r2
  pure x

-- | Evaluate an arbitrary expression, if it actually has type (s rng) and (Ord rng) then
--   return evidence of these facts (HasCond Ord (s rng))
evalWithOrd :: Rep era (s rng) -> Term era k -> Rep era rng -> Typed (HasCond Ord (s rng))
evalWithOrd r expr rng = explain ("(evalWithOrd " ++ show r ++ " " ++ show expr ++ " " ++ show rng ++ ") fails") $ do
  m <- evalWith r expr
  hasOrd rng m

-- | Fully evaluate an Term, looking up the variables in the Env.
runTerm :: Env era -> Term era t -> Typed t
runTerm env (Fixed (Lit r x)) = pure x
runTerm env (Dom x) = do
  m <- runTerm env x
  pure (Map.keysSet m)
runTerm env (Rng x) = do
  m <- runTerm env x
  pure (Set.fromList (Map.elems m))
runTerm env (Var v) = findVar v env

runPred :: Env era -> Pred era -> Typed Bool
runPred env (Sized w x) = do
  word <- runTerm env w
  item <- runTerm env x
  pure (getsize item == word)
runPred env (x :=: y) = do
  x2 <- runTerm env x
  y2 <- runTerm env y
  pure (x2 == y2)
runPred env (x :<=: y) = do
  x2 <- runTerm env x
  y2 <- runTerm env y
  pure (Set.isSubsetOf x2 y2)
runPred env (SumsTo x ys) = do
  x2 <- runTerm env x
  is <- mapM (runSum env) ys
  let y2 = List.foldl' plusSum zeroSum is
  pure (x2 == y2)
runPred env (Random x) = pure True
runPred env (HasDom m s) = do
  m2 <- runTerm env m
  s2 <- runTerm env s
  pure (Set.isSubsetOf (Map.keysSet m2) s2)

runSum :: Env era -> Sum (Term era) t -> Typed t
runSum env (One expr) = runTerm env expr
runSum env (SumMap m) = sums . SumMap . Id <$> runTerm env m
runSum env (SumSet m) = sums . SumSet . Id <$> runTerm env m

makeTest :: Env era -> Pred era -> Typed String
makeTest env c = do
  b <- runPred env c
  pure (show c ++ " => " ++ show b)

-- ======================================================================================
-- Transform a [Pred era] by introducing new variables.

mkNewVar :: Term era (Map d r) -> Term era (Set d)
mkNewVar (Var (V nm (MapR d _))) = newVar
  where
    newstring = nm ++ "Dom"
    newV = V newstring (SetR d)
    newVar = Var newV
mkNewVar other = error ("mkNewVar should only be applied to variables: " ++ show other)

removeSameVar :: [Pred era] -> [Pred era] -> [Pred era]
removeSameVar [] ans = reverse ans
removeSameVar ((Var v :=: Var u) : more) ans | Name v == Name u = removeSameVar more ans
removeSameVar ((Var v :<=: Var u) : more) ans | Name v == Name u = removeSameVar more ans
removeSameVar (m : more) ans = removeSameVar more (m : ans)

removeEqual :: [Pred era] -> [Pred era] -> [Pred era]
removeEqual [] ans = reverse ans
removeEqual ((Var v :=: Var u) : more) ans | Name v == Name u = removeEqual more ans
removeEqual ((Var v :=: expr) : more) ans = removeEqual (map sub more) (map sub ans)
  where
    sub = substPred [SubItem v expr]
removeEqual (m : more) ans = removeEqual more (m : ans)

removeDom :: [Pred era] -> [Pred era]
removeDom cs = (List.foldl' help [] cs)
  where
    help :: [Pred era] -> Pred era -> [Pred era]
    help ans c = case c of
      Sized x (Dom old@(Var (V _ (MapR _ _)))) -> foldr addPred ans [Sized x newVar, HasDom old newVar]
        where
          newVar = mkNewVar old
      (Dom left@(Var (V _ (MapR d1 _)))) :=: (Dom right@(Var (V _ (MapR d2 _)))) ->
        let leftVar = mkNewVar left
            rightVar = mkNewVar right
         in case testEql d1 d2 of
              Just Refl -> foldr addPred ans [leftVar :=: rightVar, HasDom left leftVar, HasDom right rightVar]
              Nothing -> ans
      x :=: (Dom old@(Var (V _ (MapR _ _)))) -> foldr addPred ans [x :=: newVar, HasDom old newVar]
        where
          newVar = mkNewVar old
      (Dom old@(Var (V _ (MapR _ _)))) :=: x -> foldr addPred ans [newVar :=: x, HasDom old newVar]
        where
          newVar = mkNewVar old
      (Dom left@(Var (V _ (MapR d1 _)))) :<=: (Dom right@(Var (V _ (MapR d2 _)))) ->
        let leftVar = mkNewVar left
            rightVar = mkNewVar right
         in case testEql d1 d2 of
              Just Refl -> foldr addPred ans [leftVar :<=: rightVar, HasDom left leftVar, HasDom right rightVar]
              Nothing -> ans
      x :<=: (Dom old@(Var (V _ (MapR _ _)))) -> foldr addPred ans [x :<=: newVar, HasDom old newVar]
        where
          newVar = mkNewVar old
      (Dom old@(Var (V _ (MapR _ _)))) :<=: x -> foldr addPred ans [newVar :<=: x, HasDom old newVar]
        where
          newVar = mkNewVar old
      ss@(SumsTo (Fixed _) _) -> addPred ss ans
      SumsTo x ys -> foldr addPred ans (SumsTo x ys2 : (concat new))
        where
          pairs = map remSum ys
          new = map snd pairs
          ys2 = map fst pairs
      other -> addPred other ans

remSum :: Summable t => Sum (Term era) t -> (Sum (Term era) t, [Pred era])
remSum (SumMap old@(Var (V nm (MapR _ rng)))) = (One newVar, [SumsTo newVar [SumMap old]])
  where
    newstring = nm ++ "Sum"
    newV = V newstring rng
    newVar = Var newV
remSum (SumSet old@(Var (V nm (SetR rng)))) = (One newVar, [SumsTo newVar [SumSet old]])
  where
    newstring = nm ++ "Sum"
    newV = V newstring rng
    newVar = Var newV
remSum other = (other, [])

rewrite :: [Pred era] -> [Pred era]
rewrite cs = removeSameVar (removeEqual (removeDom cs) []) []

-- =========================
-- Do not add duplicates

addName :: Name era -> [Name era] -> [Name era]
addName n ns = List.nubBy cmpName (n : ns)

addPred :: Pred era -> [Pred era] -> [Pred era]
addPred x xs = List.nubBy cmpPred (x : xs)

cmpV :: V era t -> V era s -> Ordering
cmpV (V n1 r1) (V n2 r2) = case compare n1 n2 of
  EQ -> cmpIndex r1 r2
  other -> other

cmpName :: Name era -> Name era -> Bool
cmpName (Name v1) (Name v2) = cmpV v1 v2 == EQ

-- | conservative equality. If it returns True, they are really equal, if it returns False, then who knows?
cmpPred :: forall era. Pred era -> Pred era -> Bool
cmpPred (HasDom (Var x) (Var y)) (HasDom (Var a) (Var b)) = Name x == Name a && Name y == Name b
cmpPred (Sized (Var x) (Var y)) (Sized (Var a) (Var b)) = Name x == Name a && Name y == Name b
cmpPred ((Var x) :=: (Var y)) ((Var a) :=: (Var b)) = Name x == Name a && Name y == Name b
cmpPred ((Var x) :<=: (Var y)) ((Var a) :<=: (Var b)) = Name x == Name a && Name y == Name b
cmpPred (Random (Var x)) (Random (Var a)) = Name x == Name a
cmpPred (SumsTo (Var x@(V _ r1)) xs) (SumsTo (Var a@(V _ r2)) as) =
  case testEql r1 r2 of
    Just Refl -> Name x == Name a && length xs == length as && and (zipWith cmpSum xs as)
    Nothing -> False
cmpPred _ _ = False

cmpSum :: Sum (Term era) t -> Sum (Term era) t -> Bool
cmpSum (One (Var x)) (One (Var a)) = Name x == Name a
cmpSum (SumMap (Var x)) (SumMap (Var a)) = Name x == Name a
cmpSum (SumSet (Var x)) (SumSet (Var a)) = Name x == Name a
cmpSum _ _ = False

-- ==============================================================
-- Solving a list of constraints

-- | A solution
data DependGraph era = DependGraph [(Name era, [Pred era])]

instance Show (DependGraph era) where
  show (DependGraph xs) = unlines (map f xs)
    where
      f (nm, cs) = pad n (shName nm) ++ " | " ++ showL show ", " cs
      n = maximum (map (length . shName . fst) xs) + 2
      shName (Name (V v rep)) = v ++ ": " ++ show rep

pad :: Int -> String -> String
pad n x = x ++ replicate (n - length x) ' '

-- =========================================================
-- Sketch of algorithm for creating a DependGraph
--
-- for every pair (name,[cond]) the variables of [cond] only contain name, and names defined in previous lines
-- Can we find such an order? to compute this from a [Pred era]
-- try prev choices constraints =
--   (c,more) <- pick choices
--   possible <- filter (only mentions (c:prev)) constraints
--   if null possible
--      then try prev (more ++ [(c,possible)]) constraints
--      else possible ++ try (c:prev) more (constraints - possible)
--
-- ===================================================================
-- Find an order to solve the variables in

mkDependGraph :: Int -> [(Name era, [Pred era])] -> [Name era] -> [Name era] -> [Pred era] -> Typed (DependGraph era)
mkDependGraph _ prev _ _ [] = pure (DependGraph (reverse prev))
mkDependGraph count prev choices badchoices specs
  | count <= 0 =
      failT
        [ "\nFailed to find an Ordering of variables to solve for.\nHandled Constraints\n",
          show (DependGraph (reverse prev)),
          "\n  vars to be processed",
          show choices,
          "\n  vars bad ",
          show badchoices,
          "\n  Still to be processed\n",
          unlines (map show specs)
        ]
mkDependGraph count prev [] badchoices cs = mkDependGraph (count - 1) prev (reverse badchoices) [] cs
mkDependGraph count prev (n : more) badchoices cs =
  if null possible
    then mkDependGraph count prev more (n : badchoices) cs
    else mkDependGraph count ((n, List.nubBy cmpPred possible) : prev) more badchoices notPossible
  where
    defined = Set.insert n (Set.fromList (map fst prev))
    ok constraint = Set.isSubsetOf (varsOfPred Set.empty constraint) defined
    (possible, notPossible) = List.partition ok cs

-- | Add to the dependency map 'answer' constraints such that every Name in 'before'
--   preceeds every Name in 'after' in the order in which Names are solved for.
mkDeps :: Set (Name era) -> Set (Name era) -> Map (Name era) (Set (Name era)) -> Map (Name era) (Set (Name era))
mkDeps before after answer = Set.foldl' accum answer after
  where
    accum ans left = Map.insertWith (Set.union) left before ans

-- ===================================================

data OrderInfo = OrderInfo
  { sumBeforeParts :: Bool,
    sizeBeforeArg :: Bool,
    setBeforeSubset :: Bool,
    mapBeforeDom :: Bool
  }

standardOrderInfo =
  OrderInfo
    { sumBeforeParts = False,
      sizeBeforeArg = False,
      setBeforeSubset = True,
      mapBeforeDom = False
    }

accumdep :: OrderInfo -> Map (Name era) (Set (Name era)) -> Pred era -> Map (Name era) (Set (Name era))
accumdep info answer c = case c of
  sub :<=: set ->
    if setBeforeSubset info
      then mkDeps (vars set) (vars sub) answer
      else mkDeps (vars sub) (vars set) answer
  Sized size arg ->
    if sizeBeforeArg info
      then mkDeps (vars size) (vars arg) answer
      else mkDeps (vars arg) (vars size) answer
  HasDom mp dom ->
    if mapBeforeDom info
      then mkDeps (vars mp) (vars dom) answer
      else mkDeps (vars dom) (vars mp) answer
  SumsTo sm parts ->
    if sumBeforeParts info
      then mkDeps (vars sm) (List.foldl' varsOfSum Set.empty parts) answer
      else mkDeps (List.foldl' varsOfSum Set.empty parts) (vars sm) answer
  other -> Set.foldl' accum answer (varsOfPred Set.empty other)
    where
      accum ans v = Map.insertWith (Set.union) v Set.empty ans

initialOrder :: OrderInfo -> [Pred era] -> Typed [Name era]
initialOrder info cs0 = do
  mmm <- flatOrError (stronglyConnComp listDep)
  pure (map nameOf mmm)
  where
    allvars = List.foldl' varsOfPred Set.empty cs0
    noDepMap = Set.foldl' (\ans n -> Map.insert n Set.empty ans) Map.empty allvars
    mapDep = List.foldl' (accumdep info) noDepMap cs0
    listDep = zipWith (\(x, m) n -> (n, x, Set.toList m)) (Map.toList mapDep) [0 ..]
    (_graph1, nodeFun, _keyf) = graphFromEdges listDep
    nameOf x = n where (_node, n, _children) = nodeFun x
    flatOrError [] = pure []
    flatOrError (AcyclicSCC x : more) = (x :) <$> flatOrError more
    flatOrError (CyclicSCC xs : _) = failT [message]
      where
        names = map nameOf xs
        theCycle = map show (names ++ [head names])
        message = "Cycle in dependencies: " ++ List.intercalate " <= " theCycle

maybePartition :: (a -> Maybe b) -> [a] -> ([b], [a])
maybePartition _f [] = ([], [])
maybePartition f (a : more) = maybe (bs, a : as) (\b -> (b : bs, as)) (f a)
  where
    (bs, as) = maybePartition f more

compile :: OrderInfo -> [Pred era] -> Typed (DependGraph era)
compile info cs = do
  let simple = rewrite cs
  orderedNames <- initialOrder info simple
  mkDependGraph (length orderedNames) [] orderedNames [] simple

-- ===========================================================
-- Example variables

treasury :: Term era Coin
treasury = Var $ V "treasury" CoinR

reserves :: Term era Coin
reserves = Var $ V "reserves" CoinR

-- utxo = Var $ V "utxo" (MapR TxInR TxOutR)

deposits :: Term era Coin
deposits = Var $ V "deposits" CoinR

fees :: Term era Coin
fees = Var $ V "fees" CoinR

rewards :: Term era (Map (Credential 'Staking (EraCrypto era)) Coin)
rewards = Var $ V "rewards" (MapR CredR CoinR)

delegations :: Term era (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era)))
delegations = Var $ V "delegations" (MapR CredR PoolR)

keyDeposits :: Term era (Map (Credential 'Staking (EraCrypto era)) Coin)
keyDeposits = Var $ V "keyDeposits" (MapR CredR CoinR)

poolDeposits :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) Coin)
poolDeposits = Var $ V "poolDeposits" (MapR PoolR CoinR)

poolDistr :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) Rational)
poolDistr = Var $ V "poolDistr" (MapR PoolR RationalR)

retiring :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) EpochNo)
retiring = Var $ V "retiring" (MapR PoolR EpochR)

regPools :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era)))
regPools = Var $ V "regPools" (MapR PoolR PoolParamsR)

totalAda :: Term era Coin
totalAda = Var $ V "totalAda" CoinR

utxoCoin :: Term era Coin
utxoCoin = Var $ V "utxoCoin" CoinR

creds :: Term era (Set (Credential 'Staking (EraCrypto era)))
creds = Var $ V "creds" (SetR CredR)

pools :: Term era (Set (KeyHash 'StakePool (EraCrypto era)))
pools = Var $ V "pools" (SetR PoolR)

-- ===========================================================
-- Example list of Constraints

constraints :: [Pred era]
constraints =
  [ -- Sized (Fixed (Lit Word64R 1000)) totalAda,
    Sized (Fixed (Lit Word64R 10)) creds,
    Sized (Fixed (Lit Word64R 10)) pools,
    Dom rewards :<=: creds,
    Rng delegations :<=: pools,
    Dom poolDeposits :<=: pools,
    Dom rewards :=: Dom keyDeposits,
    Dom keyDeposits :<=: creds,
    Dom delegations :<=: creds,
    Dom delegations :<=: Dom rewards,
    Dom poolDistr :<=: Dom regPools,
    Dom regPools :=: Dom poolDistr,
    Dom regPools :=: Dom poolDeposits,
    Dom regPools :<=: pools,
    Dom retiring :<=: Dom regPools,
    SumsTo deposits [SumMap keyDeposits, SumMap poolDeposits],
    SumsTo (Fixed (Lit RationalR 1)) [SumMap poolDistr],
    SumsTo
      totalAda
      [ One utxoCoin,
        One treasury,
        One reserves,
        One fees,
        SumMap keyDeposits,
        SumMap poolDeposits,
        SumMap rewards
      ],
    Random treasury,
    Random reserves,
    Random fees,
    Random utxoCoin
  ]

-- | Used to test cyclic dependencies
cs1 :: [Pred era]
cs1 = [a :<=: b, b :<=: c, c :<=: a]
  where
    a = Var (V "a" (SetR IntR))
    b = Var (V "b" (SetR IntR))
    c = Var (V "c" (SetR IntR))

test3 :: IO ()
test3 = do
  let cs =
        [ Dom poolDistr :<=: Dom regPools,
          Dom regPools :=: Dom poolDistr,
          Dom regPools :=: Dom poolDeposits,
          Dom regPools :<=: pools,
          Dom retiring :<=: Dom regPools
        ]
  -- putStrLn (show cs)
  let cs2 = (removeDom cs)
  -- putStrLn (show cs2)
  let cs3 = removeEqual cs2 []
  -- putStrLn (show cs3)
  let cs4 = removeSameVar cs3 []
  -- putStrLn (show cs4)
  putStrLn
    ( unlines
        [ "Constraints",
          show cs,
          "Introduce new variables",
          show cs2,
          "Substitute Equality",
          show cs3,
          "Remove tautology",
          show cs4
        ]
    )

-- ==============================================

test6 :: OrderInfo -> IO ()
test6 info = case runTyped (compile info constraints) of
  Right x -> print x
  Left xs -> putStrLn (unlines xs)

-- ==========================================================

data RngSpec rng where
  SumRng :: Summable rng => rng -> RngSpec rng
  Exact :: Ord rng => [rng] -> RngSpec rng
  SubsetRng :: Ord rng => (Set rng) -> RngSpec rng
  None :: RngSpec rng

showRngSpec :: Rep era t -> RngSpec t -> String
showRngSpec _ (SumRng r) = "(Sum " ++ show r ++ ")"
showRngSpec rep (Exact xs) = "(RngEqual " ++ synopsis (ListR rep) xs ++ ")"
showRngSpec rep (SubsetRng xs) = "(Subset " ++ synopsis (SetR rep) xs ++ ")"
showRngSpec _ None = "None"

mergeRngSpec :: RngSpec r -> RngSpec r -> Either [String] (RngSpec r)
mergeRngSpec None x = Right x
mergeRngSpec x None = Right x
mergeRngSpec (SumRng x) (SumRng y) | x == y = Right (SumRng x)
mergeRngSpec (Exact x) (Exact y) | x == y = Right (Exact x)
mergeRngSpec (SubsetRng x) (SubsetRng y) = Right (SubsetRng (Set.intersection x y))
mergeRngSpec (Exact xs) (SubsetRng ys) | Set.isSubsetOf (Set.fromList xs) ys = Right (Exact xs)
mergeRngSpec (SubsetRng ys) (Exact xs) | Set.isSubsetOf (Set.fromList xs) ys = Right (Exact xs)
mergeRngSpec _ _ = Left ["Different range specs in mergeRngSpec"]

data MapSpec dom rng where
  MapSpec :: (Maybe Word64) -> (Maybe (Set dom)) -> (RngSpec rng) -> MapSpec dom rng
  MapExact :: Ord rng => Map dom rng -> MapSpec dom rng
  NeverMap :: [String] -> MapSpec dom rng

showMapSpec :: Rep era (Map dom rng) -> MapSpec dom rng -> String
showMapSpec rep@(MapR dom rng) (MapSpec w Nothing r) =
  "(MapSpec " ++ show w ++ " Nothing " ++ showRngSpec rng r ++ ")"
showMapSpec rep@(MapR dom rng) (MapSpec w (Just s) r) =
  "(MapSpec " ++ show w ++ " " ++ synopsis (SetR dom) s ++ " " ++ showRngSpec rng r ++ ")"
showMapSpec rep@(MapR dom rng) (MapExact m) = "(MapEqual " ++ synopsis rep m ++ ")"
showMapSpec _ (NeverMap xs) = "NeverMap"
showMapSpec (TxOutR _) _ = "OOPS"

instance LiftT (MapSpec a b) where
  liftT (NeverMap xs) = failT xs
  liftT x = pure x
  dropT (Typed (Left s)) = NeverMap s
  dropT (Typed (Right x)) = x

comb1 :: Ord a => (Maybe (Set a)) -> (Maybe (Set a)) -> Maybe (Set a)
comb1 Nothing x = x
comb1 x Nothing = x
comb1 (Just x) (Just y) = Just (Set.intersection x y)

comb2 :: (Maybe Word64) -> (Maybe Word64) -> Either [String] (Maybe Word64)
comb2 Nothing x = Right x
comb2 x Nothing = Right x
comb2 (Just s1) (Just s2) =
  if s1 == s2
    then Right (Just s1)
    else Left ["Can't be size " ++ show s1 ++ " " ++ show s2 ++ " at the same time."]

instance (Ord dom) => Semigroup (MapSpec dom rng) where
  (NeverMap s) <> (NeverMap t) = NeverMap (s ++ t)
  (NeverMap _) <> y = y
  x <> (NeverMap _) = x
  (MapExact x) <> (MapExact y) =
    if x == y then MapExact x else NeverMap ["Two non-matching Exact"]
  (MapExact x) <> m@(MapSpec _ _ _) = MapSpec Nothing (Just (Map.keysSet x)) (Exact (Map.elems x)) <> m
  m@(MapSpec _ _ _) <> (MapExact x) = MapSpec Nothing (Just (Map.keysSet x)) (Exact (Map.elems x)) <> m
  (MapSpec s1 d1 r1) <> (MapSpec s2 d2 r2) = case comb2 s1 s2 of
    Left s -> NeverMap s
    Right s -> case mergeRngSpec r1 r2 of
      Left msg -> NeverMap msg
      Right r -> MapSpec s (comb1 d1 d2) r

instance (Ord dom) => Monoid (MapSpec dom rng) where mempty = MapSpec Nothing Nothing None

-- =======================================================

solveMap :: V era (Map dom rng) -> Pred era -> Typed (MapSpec dom rng)
solveMap v1@(V _ r@(TxOutR _)) _ = failT ["TxOutR anomaly in solveMap"]
solveMap v1@(V _ r@(MapR dom rng)) cond = case cond of
  (Sized (Fixed (Lit Word64R n)) (Var v2))
    | Name v1 == Name v2 -> do
        With none <- hasOrd rng None
        pure (MapSpec (Just n) Nothing none)
  (Var v2 :=: expr) | Name v1 == Name v2 ->
    do
      With m <- evalWithOrd r expr rng
      pure (MapExact m)
  (expr :=: v2@(Var _)) -> solveMap v1 (v2 :=: expr)
  -- delegations: (Map Cred Pool) | HasDomain delegations delegationsDom, (rng delegations) ⊆  pools
  (Rng (Var v2) :<=: expr)
    | Name v1 == Name v2 -> do
        dyn <- eval expr
        With n <- isDynSet dyn rng
        pure (MapSpec Nothing Nothing (SubsetRng n))

  -- e.g. poolDistr: (Map Pool Rational) | (Fixed 1 % 1) =∑= sum poolDistr
  (SumsTo expr [SumMap (Var v2)])
    | Name v1 == Name v2 -> do
        n <- evalWith rng expr
        case rng of
          IntR -> pure $ MapSpec Nothing Nothing (SumRng n)
          CoinR -> pure $ MapSpec Nothing Nothing (SumRng n)
          RationalR -> pure $ MapSpec Nothing Nothing (SumRng n)
          _ -> failT ["Type " ++ show rng ++ " does not have Summable instance"]
  (Random (Var v2)) | Name v1 == Name v2 -> do
    With none2 <- hasOrd rng None
    pure $ MapSpec Nothing Nothing none2

  -- e.g poolDeposits: (Map Pool Coin)  | HasDomain poolDeposits poolDistrDom
  (HasDom (Var v2) expr) | Name v1 == Name v2 -> do
    dyn <- eval expr
    With set <- isDynSet dyn dom
    With emptyRngSpec <- hasOrd rng None
    pure $ MapSpec Nothing (Just set) emptyRngSpec
  other -> failT ["Cannot solve map condition: " ++ show other]

solveMaps :: Ord dom => V era (Map dom rng) -> [Pred era] -> Typed (MapSpec dom rng)
solveMaps (V _ (TxOutR _)) _ = failT ["TxOutR anomaly in solveMaps"]
solveMaps v@(V nm (MapR _ rngRep)) cs = foldlM' accum (MapSpec Nothing Nothing None) cs
  where
    accum spec cond = do
      condspec <- solveMap v cond
      explain ("Solving Map constraint (" ++ show cond ++ ") for variable " ++ show nm) (liftT (spec <> condspec))

genMap ::
  (Ord a) =>
  Crypto (EraCrypto era) =>
  Rep era (Map a b) ->
  MapSpec a b ->
  Typed (Gen (Map a b))
genMap (TxOutR _) _ = failT ["TxOut strangeness"]
genMap rep@(MapR d r) cond = explain ("Producing Map generator for " ++ showMapSpec rep cond) $ case cond of
  (MapExact m) -> Typed $ Right $ pure m -- or equivalently (pure $ pure m) which is confusing
  (NeverMap ss) -> failT ss
  (MapSpec Nothing Nothing None) -> pure $ genRep rep
  (MapSpec Nothing Nothing (Exact rs)) -> pure $ mapFromRange rs (genRep d)
  (MapSpec Nothing Nothing (SumRng tot)) -> pure $ do
    n <- arbitrary
    ranges <- partition n tot
    mapFromRange ranges (genRep d)
  (MapSpec Nothing Nothing (SubsetRng set)) -> pure $ do
    rs <- subsetFromSet set
    mapFromRange (Set.toList rs) (genRep d)
  (MapSpec Nothing (Just dom) None) -> pure $ mapFromSet dom (genRep r)
  (MapSpec Nothing (Just dom) (SumRng tot)) -> pure $ do
    ranges <- partition (Set.size dom) tot
    pure (Map.fromList $ zip (Set.toList dom) ranges)
  (MapSpec Nothing (Just dom) (Exact rs)) ->
    pure $ pure (Map.fromList (zip (Set.toList dom) rs))
  (MapSpec Nothing (Just dom) (SubsetRng set)) ->
    pure $ mapFromSet dom (itemFromSet set)
  (MapSpec (Just n) Nothing None) -> pure $ genSizedRep (fromIntegral n) rep
  (MapSpec (Just n) Nothing (SumRng tot)) -> pure $ do
    ranges <- partition (fromIntegral n) tot
    mapFromRange ranges (genRep d)
  (MapSpec (Just n) Nothing (Exact rs))
    | (fromIntegral n) == length rs -> pure $ mapFromRange rs (genRep d)
    | otherwise -> failT ["Explicit size and exact range don't match"]
  (MapSpec (Just n) Nothing (SubsetRng rs)) ->
    pure $ mapSized (fromIntegral n) (genRep d) (itemFromSet rs)
  (MapSpec (Just n) (Just dom) None) ->
    pure $ mapSized (fromIntegral n) (itemFromSet dom) (genRep r)
  (MapSpec (Just n) (Just dom) (SumRng tot))
    | (fromIntegral n) == Set.size dom ->
        pure
          ( do
              ranges <- partition (fromIntegral n) tot
              pure (Map.fromList $ zip (Set.toList dom) ranges)
          )
    | otherwise -> failT ["Explicit size and dom set don't match"]
  (MapSpec (Just n) (Just dom) (Exact rs))
    | (fromIntegral n) == length rs -> pure $ mapFromRange rs (itemFromSet dom)
    | otherwise -> failT ["Explicit size and exact range don't match"]
  (MapSpec (Just n) (Just dom) (SubsetRng rng)) ->
    pure $ mapSized (fromIntegral n) (itemFromSet dom) (itemFromSet rng)

-- ================================================

data SetSpec a = Ord a => SetSpec (Maybe Int) (RngSpec a) | NeverSet [String]

showSetSpec :: Rep era a -> SetSpec a -> String
showSetSpec rep (SetSpec m r) = "(SetSpec " ++ show m ++ " " ++ showRngSpec rep r ++ ")"
showSetSpec _ (NeverSet _) = "NeverSet"

instance LiftT (SetSpec t) where
  liftT (NeverSet xs) = failT xs
  liftT x = pure x
  dropT (Typed (Left s)) = NeverSet s
  dropT (Typed (Right x)) = x

mergeSetSpec :: Ord a => SetSpec a -> SetSpec a -> SetSpec a
mergeSetSpec s1 s2 = case (s1, s2) of
  (NeverSet xs, NeverSet ys) -> NeverSet (xs ++ ys)
  (NeverSet xs, _) -> NeverSet xs
  (_, NeverSet ys) -> NeverSet ys
  (SetSpec Nothing xs, SetSpec Nothing ys) -> case mergeRngSpec xs ys of
    Left x -> NeverSet x
    Right x -> SetSpec Nothing x
  (SetSpec (Just a) xs, SetSpec Nothing ys) -> case mergeRngSpec xs ys of
    Left x -> NeverSet x
    Right x -> SetSpec (Just a) x
  (SetSpec Nothing xs, SetSpec (Just a) ys) -> case mergeRngSpec xs ys of
    Left x -> NeverSet x
    Right x -> SetSpec (Just a) x
  (SetSpec (Just n) xs, SetSpec (Just m) ys)
    | n == m -> case mergeRngSpec xs ys of
        Left x -> NeverSet x
        Right x -> SetSpec (Just n) x
    | otherwise -> NeverSet ["Two SetSpec with explicit sizes can't be merged: " ++ show (n, m)]

instance Ord a => Semigroup (SetSpec a) where
  (<>) = mergeSetSpec

instance Ord a => Monoid (SetSpec a) where
  mempty = SetSpec Nothing None

sumFromDyn :: Rep era t -> Dyn era -> Typed (HasCond Summable (Id t))
sumFromDyn rep (Dyn rep2 m) = case (testEql rep rep2) of
  Just Refl -> hasSummable rep2 (Id m)
  Nothing -> failT ["(Dyn " ++ show rep2 ++ " _) does not store expected type: " ++ show rep]

hasSummable :: Rep era t -> (s t) -> Typed (HasCond Summable (s t))
hasSummable IntR x = pure $ With x
hasSummable CoinR x = pure $ With x
hasSummable RationalR x = pure $ With x
hasSummable r _ = failT [show r ++ " does not have Summable instance."]

solveSet :: V era (Set a) -> Pred era -> Typed (SetSpec a)
solveSet v1@(V _ (SetR r)) (Sized (Fixed (Lit Word64R n)) (Var v2))
  | Name v1 == Name v2 = do
      With none2 <- hasOrd r None
      pure (SetSpec (Just (fromIntegral n)) none2)
solveSet v1@(V _ (SetR r)) (Var v2 :=: expr)
  | Name v1 == Name v2 = do
      dyn <- eval expr
      With set <- isDynSet dyn r
      pure $ SetSpec Nothing (Exact (Set.toList set))
solveSet v1 (expr :=: v2@(Var _)) = solveSet v1 (v2 :=: expr)
solveSet v1@(V _ (SetR r)) (Var v2 :<=: expr)
  | Name v1 == Name v2 = do
      dyn <- eval expr
      With set <- isDynSet dyn r
      pure $ SetSpec Nothing (SubsetRng set)
solveSet v1@(V _ (SetR r)) cond@(expr :<=: Var v2)
  | Name v1 == Name v2 = failT ["Don't know how to solve superset constraint: " ++ show cond]
solveSet v1@(V _ (SetR r)) (SumsTo expr [SumSet (Var v2)])
  | Name v1 == Name v2 = do
      dyn <- eval expr
      With (Id m2) <- sumFromDyn r dyn
      pure $ SetSpec Nothing (SumRng m2)
solveSet v1@(V _ (SetR r)) (Random (Var v2))
  | Name v1 == Name v2 = pure $ SetSpec Nothing None
solveSet _ cond = failT ["Can't solveSet " ++ show cond]

solveSets :: V era (Set a) -> [Pred era] -> Typed (SetSpec a)
solveSets v@(V _ (TxOutR a)) cs = failT ["TxOutR anomaly in solveSets"]
solveSets v@(V nm (SetR a)) cs = foldlM' accum mempty cs
  where
    accum spec cond = do
      condspec <- solveSet v cond
      explain ("Solving Set constraint (" ++ show cond ++ ") for variable " ++ show nm) (liftT (spec <> condspec))

genSet ::
  (Ord a) =>
  Crypto (EraCrypto era) =>
  Rep era (Set a) ->
  SetSpec a ->
  Typed (Gen (Set a))
genSet (TxOutR _) _ = failT ["TxOut anomaly in genSet"]
genSet rep@(SetR r) cond = explain ("Producing Set generator for " ++ showSetSpec r cond) $ case cond of
  NeverSet ss -> failT ss
  SetSpec Nothing None -> pure $ genRep rep
  SetSpec Nothing (SubsetRng x) -> pure $ subsetFromSet x
  SetSpec Nothing (Exact xs) -> pure $ pure (Set.fromList xs)
  SetSpec Nothing (SumRng n) -> pure $ do
    i <- choose (2, 5) -- We don't want 'i'too large, or we might not be able to break 'n' into 'i' parts.
    xs <- partition i n
    pure (Set.fromList xs)
  SetSpec (Just n) None -> pure $ genSizedRep n rep
  SetSpec (Just n) (SubsetRng set) -> pure $ subsetFromSetWithSize set n
  SetSpec (Just n) (Exact xs) ->
    if n == length xs
      then pure $ pure (Set.fromList xs)
      else failT ["Explicit size and exact set don't match up"]
  SetSpec (Just i) (SumRng n) -> pure $ do
    xs <- partition i n
    pure (Set.fromList xs)

-- =============================================================
data SumSpec t where
  SumSpec :: Summable t => Maybe t -> Maybe t -> SumSpec t
  NeverSum :: [String] -> SumSpec t

showSumSpec :: SumSpec a -> String
showSumSpec (SumSpec m r) = "(SumSpec " ++ show m ++ " " ++ show r ++ ")"
showSumSpec (NeverSum _) = "NeverSum"

instance LiftT (SumSpec t) where
  liftT (NeverSum xs) = failT xs
  liftT x = pure x
  dropT (Typed (Left s)) = NeverSum s
  dropT (Typed (Right x)) = x

sameMaybe :: (Eq x, Show x) => Maybe x -> Maybe x -> Either [String] (Maybe x)
sameMaybe Nothing Nothing = Right Nothing
sameMaybe (Just x) Nothing = Right (Just x)
sameMaybe Nothing (Just x) = Right (Just x)
sameMaybe (Just x) (Just y) =
  if x == y
    then Right (Just x)
    else Left ["Not the same in sameMaybe: " ++ show (x, y)]

mergeSumSpec :: Summable t => SumSpec t -> SumSpec t -> SumSpec t
mergeSumSpec (NeverSum xs) (NeverSum ys) = NeverSum (xs ++ ys)
mergeSumSpec (NeverSum xs) _ = NeverSum xs
mergeSumSpec _ (NeverSum xs) = NeverSum xs
mergeSumSpec (SumSpec x a) (SumSpec y b) = case (sameMaybe x y, sameMaybe a b) of
  (Right z, Right c) -> SumSpec z c
  (Left z, Right _) -> NeverSum z
  (Right _, Left c) -> NeverSum c
  (Left z, Left c) -> NeverSum (z ++ c)

instance Summable t => Semigroup (SumSpec t) where
  (<>) = mergeSumSpec

instance Summable t => Monoid (SumSpec t) where
  mempty = SumSpec Nothing Nothing

evalSum :: Summable t => Rep era t -> Sum (Term era) t -> Typed (HasCond Summable (Id t))
evalSum rep (One expr) = do
  dyn <- eval expr
  sumFromDyn rep dyn
evalSum rep (SumMap (Fixed (Lit (MapR _ b) m))) = pure $ With (Id (Map.foldl' plusSum zeroSum m))
evalSum rep (SumSet (Fixed (Lit (SetR b) m))) = pure $ With (Id (Set.foldl' plusSum zeroSum m))
evalSum rep x = failT ["Can't evalSum " ++ show x]

evalSums :: Summable t => Rep era t -> [Sum (Term era) t] -> Typed (HasCond Summable (Id t))
evalSums rep xs = foldlM' accum (With (Id zeroSum)) xs
  where
    accum (With (Id n)) x = do
      With (Id m) <- evalSum rep x
      pure (With (Id (plusSum n m)))

solveSum :: Summable t => V era t -> Pred era -> Typed (SumSpec t)
solveSum v1@(V _ r) c = case c of
  (Sized expr (Var v2)) | Name v1 == Name v2 -> do
    dyn <- eval expr
    With (Id n) <- sumFromDyn r dyn
    pure $ SumSpec (Just n) Nothing
  (expr :=: (Var v2)) | Name v1 == Name v2 -> do
    dyn <- eval expr
    With (Id n) <- sumFromDyn r dyn
    pure $ SumSpec (Just n) Nothing
  (Random (Var v2)) | Name v1 == Name v2 -> pure $ SumSpec Nothing Nothing
  (SumsTo (Var v2@(V _ r2)) xs@(_ : _)) | Name v1 == Name v2 -> do
    Refl <- sameRep r r2
    With (Id n) <- evalSums r xs
    pure $ SumSpec Nothing (Just n)
  other -> failT ["Can't solveSum " ++ show other]

solveSums :: Summable t => V era t -> [Pred era] -> Typed (SumSpec t)
solveSums v@(V nm rep) cs = foldlM' accum mempty cs
  where
    accum spec cond = do
      condspec <- solveSum v cond
      explain
        ("Solving Sum constraint (" ++ show cond ++ ") for variable " ++ show nm)
        (liftT (spec <> condspec))

genSum :: (Summable t, Crypto (EraCrypto era)) => Rep era t -> SumSpec t -> Typed (Gen t)
genSum rep spec = explain ("Producing Sum generator for " ++ showSumSpec spec) $ case spec of
  (SumSpec Nothing Nothing) -> pure $ genRep rep
  (SumSpec (Just t) Nothing) -> pure $ pure t
  (SumSpec Nothing (Just tot)) -> pure $ pure tot
  (SumSpec (Just x) (Just tot)) ->
    if x == tot
      then pure $ pure x
      else failT ["Not the same in genSum: " ++ show (x, tot)]
  _ -> failT ["OOPs"]

isSumType :: forall era t. Rep era t -> Bool
isSumType rep = case hasSummable rep (Id (undefined :: t)) of
  (Typed (Right (With _))) -> True
  (Typed (Left _)) -> False

-- ===================================================

genPair :: Crypto (EraCrypto era) => (V era t, [Pred era]) -> Typed (Gen t)
genPair (v@(V _nm rep@(MapR _ _)), cs) = (solveMaps v cs) >>= genMap rep
genPair (v@(V _nm rep@(SetR _)), cs) = (solveSets v cs) >>= genSet rep
genPair (v@(V _nm rep), cs) | isSumType rep = do
  With v2 <- hasSummable rep v
  xs <- solveSums v2 cs
  genSum rep xs
genPair (v1@(V _nm rep), [Random (Var v2)]) | Name v1 == Name v2 = pure $ genRep rep
genPair (v@(V _nm rep), cs) = failT ["No solution at type " ++ show rep ++ " for condtions " ++ show cs]

genOrFail ::
  Crypto (EraCrypto era) =>
  Either [String] (Subst era) ->
  (Name era, [Pred era]) ->
  Gen (Either [String] (Subst era))
genOrFail (Right subst) (Name v@(V nm rep), conds) =
  case runTyped $ genPair (v, map (substPred subst) conds) of
    Right gen -> do
      t <- gen
      pure (Right (SubItem v (Fixed (Lit rep t)) : subst))
    Left msgs -> pure (Left msgs)
genOrFail (Left msgs) _ = pure (Left msgs)

genOrFailList ::
  Crypto (EraCrypto era) =>
  Either [String] (Subst era) ->
  [(Name era, [Pred era])] ->
  Gen (Either [String] (Subst era))
genOrFailList = foldlM' genOrFail

genDependGraph :: Proof era -> DependGraph era -> Gen (Either [String] (Subst era))
genDependGraph (Shelley _) (DependGraph pairs) = genOrFailList (Right []) pairs
genDependGraph (Allegra _) (DependGraph pairs) = genOrFailList (Right []) pairs
genDependGraph (Mary _) (DependGraph pairs) = genOrFailList (Right []) pairs
genDependGraph (Alonzo _) (DependGraph pairs) = genOrFailList (Right []) pairs
genDependGraph (Babbage _) (DependGraph pairs) = genOrFailList (Right []) pairs
genDependGraph (Conway _) (DependGraph pairs) = genOrFailList (Right []) pairs

-- ================================================================

test7 :: IO ()
test7 = do
  putStrLn (show constraints)
  graph <- ioTyped $ compile standardOrderInfo constraints
  putStrLn (show graph)
  result <- generate (genDependGraph (Shelley Mock) graph)
  subst <- case result of
    Left msgs -> error (unlines msgs)
    Right x -> pure x
  putStrLn (unlines (map show subst))
  let env = substToEnv subst emptyEnv
  ss <- ioTyped (mapM (makeTest env) constraints)
  putStrLn (unlines ss)

-- ==========================================================
-- Extras

known :: Rep era s -> Literal era t -> Maybe s
known s (Lit r x) = case testEql s r of Nothing -> Nothing; Just Refl -> Just x

repOf :: Term era t -> Rep era t
repOf (Fixed (Lit r _)) = r
repOf (Var (V _ r)) = r
repOf (Dom e) = case repOf e of MapR d _ -> SetR d; other -> error "Ill-typed Dom in repOf"
repOf (Rng e) = case repOf e of MapR _ r -> SetR r; other -> error "Ill-typed Rng in repOf"

-- =======================================================================

{-  Here is a solution

ghci> test6 False
ghci> test6 False
utxoCoin: Coin                        | Random utxoCoin
treasury: Coin                        | Random treasury
reserves: Coin                        | Random reserves
pools: (Set Pool )                    | Sized (Fixed 10) pools
poolDistrDom: (Set Pool )             | poolDistrDom ⊆  pools
regPools: (Map Pool (PoolParams c))   | HasDomain regPools poolDistrDom
retiringDom: (Set Pool )              | retiringDom ⊆  poolDistrDom
retiring: (Map Pool EpochNo)          | HasDomain retiring retiringDom
poolDistr: (Map Pool Rational)        | (Fixed 1 % 1) =∑= sum poolDistr, HasDomain poolDistr poolDistrDom
poolDeposits: (Map Pool Coin)         | HasDomain poolDeposits poolDistrDom
poolDepositsSum: Coin                 | poolDepositsSum =∑= sum poolDeposits
fees: Coin                            | Random fees
creds: (Set Cred )                    | Sized (Fixed 10) creds
keyDepositsDom: (Set Cred )           | keyDepositsDom ⊆  creds
delegationsDom: (Set Cred )           | delegationsDom ⊆  keyDepositsDom, delegationsDom ⊆  creds
delegations: (Map Cred Pool)          | HasDomain delegations delegationsDom, (rng delegations) ⊆  pools
keyDeposits: (Map Cred Coin)          | HasDomain keyDeposits keyDepositsDom
keyDepositsSum: Coin                  | keyDepositsSum =∑= sum keyDeposits
deposits: Coin                        | deposits =∑= keyDepositsSum + poolDepositsSum
rewards: (Map Cred Coin)              | HasDomain rewards keyDepositsDom
rewardsSum: Coin                      | rewardsSum =∑= sum rewards
totalAda: Coin                        | totalAda =∑= utxoCoin + treasury + reserves + fees + keyDepositsSum + poolDepositsSum + rewardsSum
-}

-- | Here is a transcription by hand, just to get a feel of what we have to generate.
foo :: forall era. Crypto (EraCrypto era) => Proof era -> Gen [P era]
foo _proof = do
  utxoCoinX <- genRep @era CoinR
  treasuryX <- genRep @era CoinR
  reservesX <- genRep @era CoinR
  poolsX <- setSized 10 (genRep @era PoolR)
  poolDistrDomX <- subsetFromSet poolsX
  regPoolsX <- mapFromSet poolDistrDomX (genRep @era PoolParamsR)
  retiringDomX <- subsetFromSet poolDistrDomX
  retiringX <- mapFromSet retiringDomX (genRep @era EpochR)
  rs <- partition (Set.size poolDistrDomX) (1 :: Rational)
  let poolDistrX = mapFromDomRange poolDistrDomX rs
  poolDepositsX <- mapFromSet poolDistrDomX (genRep @era CoinR)
  let poolDepositsSumX = sumMap poolDepositsX
  feesX <- genRep @era CoinR
  credsX <- setSized 10 (genRep @era CredR)
  keyDepositxDomX <- subsetFromSet credsX
  delegationsDomX <- subsetFromSet keyDepositxDomX
  delegationsX <- mapFromSet delegationsDomX (itemFromSet poolsX)
  keyDepositsX <- mapFromSet keyDepositxDomX (genRep @era CoinR)
  let keyDepositsSumX = sumMap keyDepositsX
  let depositsX = plusSum poolDepositsSumX keyDepositsSumX
  rewardsX <- mapFromSet keyDepositxDomX (genRep @era CoinR)
  let rewardsSumX = sumMap rewardsX
  let totalAdaX = List.foldl' plusSum zeroSum [utxoCoinX, treasuryX, reservesX, feesX, keyDepositsSumX, poolDepositsSumX, rewardsSumX]
  pure
    [ p utxoCoin utxoCoinX,
      p treasury treasuryX,
      p reserves reservesX,
      p fees feesX,
      P (V "keyDepositSum" CoinR) keyDepositsSumX,
      P (V "poolDepositSum" CoinR) poolDepositsSumX,
      P (V "rewardsSum" CoinR) rewardsSumX,
      p totalAda totalAdaX,
      p pools poolsX,
      P (V "poolDistrDom" (SetR PoolR)) poolDistrDomX,
      p regPools regPoolsX,
      p retiring retiringX,
      p poolDistr poolDistrX,
      p poolDeposits poolDepositsX,
      p creds credsX,
      p rewards rewardsX,
      p delegations delegationsX,
      p keyDeposits keyDepositsX
    ]

p :: Term era t -> t -> P era
p (Var v) t = P v t
p other _ = error ("p applied to non Var: " ++ show other)
