{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE DerivingStrategies #-}
module QSM2 where

import Control.Concurrent (ThreadId, myThreadId)
import Control.Concurrent.Async (concurrently_, mapConcurrently)
import Control.Concurrent.STM.TQueue
import Control.Monad (forM_, replicateM_, unless)
import Control.Monad.STM (atomically)
import Data.IORef (atomicModifyIORef')
import Data.List (permutations)
import Data.Tree
import Test.QuickCheck
import Test.QuickCheck.Monadic


import QSM1 (Counter(Counter), Model, Command(Get, Incr), Response(Int, Unit),
              initModel, get, step, newCounter, exec, shrinkCommand, genCommand)

newtype ConcProgram = ConcProgram { unConcProgram :: [[Command]] }
  deriving stock Show


genConcProgram :: Model -> Gen ConcProgram
genConcProgram m0 = sized (go m0 [])
  where
    go :: Model -> [[Command]] -> Int -> Gen ConcProgram
    go m acc sz | sz <= 0   = return (ConcProgram (reverse acc))
                | otherwise = do
                    n <- chooseInt (2, 5)
                    -- cmds :: [Command]
                    cmds <- vectorOf n genCommand `suchThat` concSafe m
                    go (advanceModel m cmds) (cmds : acc) (sz - n)

advanceModel :: Model -> [Command] -> Model
advanceModel m cmds = foldr (\cmd ih -> fst (step ih cmd)) m cmds

-- are all permuatations of the command list valid?
-- strange criteria; I would instead generate all
-- programs (lazily) and filter valid ones
concSafe :: Model -> [Command] -> Bool
concSafe m = all (validProgram m) . permutations

-- trivially valid
validProgram :: Model -> [Command] -> Bool
validProgram _model _cmds = True



-- iterate through each list of commands;
-- execute them and pass the resulting model to `go`
-- in each iteration check if `concSafe`
-- short circuit on the above check
validConcProgram :: Model -> ConcProgram -> Bool
validConcProgram m0 (ConcProgram cmdss0) = go m0 True cmdss0
  where
    go :: Model -> Bool -> [[Command]] -> Bool
    go _m False _              = False
    go _m acc   []             = acc
    go m _acc   (cmds : cmdss) = go (advanceModel m cmds) (concSafe m cmds) cmdss

shrinkConcProgram :: Model -> ConcProgram -> [ConcProgram]
shrinkConcProgram m
  = filter (validConcProgram m)
  . map ConcProgram
  . filter (not . null)
  . shrinkList shrinkProg
  . unConcProgram
  where
    --            Program   -> [Program]
    shrinkProg :: [Command] -> [[Command]]
    shrinkProg = shrinkList shrinkCommand

prettyConcProgram :: ConcProgram -> String
prettyConcProgram = show

newtype Pid = Pid Int
  deriving stock (Eq, Ord, Show)

data Operation = CMD Pid Command | RESP Pid Response deriving (Eq, Show)

type History = [Operation]

toPid :: ThreadId -> Pid
toPid tid = Pid (read (drop (length ("ThreadId " :: String)) (show tid)))

-- currying two arguments
appendHistory :: TQueue Operation -> Operation -> IO ()
appendHistory = (.) atomically . writeTQueue

concExec :: TQueue Operation -> Counter -> Command -> IO ()
concExec tq counter cmd = do
  pid  <- toPid <$> myThreadId
  appendHistory tq (CMD pid cmd)
  -- resp <- exec counter cmd
  resp <- threadSafeExec counter cmd
  appendHistory tq (RESP pid resp)


threadSafeExec :: Counter -> Command -> IO Response
threadSafeExec c cmd = case cmd of
  Incr i -> Unit <$> threadSafeIncr c i
  Get    -> Int  <$> get c
  where
    threadSafeIncr (Counter ref) i = atomicModifyIORef' ref (\j -> (i + j, ()))


{-
data Tree a = Node a [Tree a]

data Forest a = [Tree a]

data Tree a = Node a (Forest a)

-}

interleavings :: History -> Forest (Command, Response)
interleavings [] = []
interleavings ops0 =
  [ Node (cmd, resp) (interleavings ops')
  | (tid, cmd)   <- takeInvocations ops0
  , (resp, ops') <- findResponse tid
                      (filter1 (not . matchInvocation tid) ops0)
  ]
  where
    -- get all invocations till you encounter a response
    takeInvocations :: History -> [(Pid, Command)]
    takeInvocations []                         = []
    takeInvocations ((CMD pid cmd)   : ops) = (pid, cmd) : takeInvocations ops
    takeInvocations ((RESP    _pid _resp) : _)   = []

    findResponse :: Pid -> History -> [(Response, [Operation])]
    findResponse _pid []                                    = []
    findResponse  pid ((RESP pid' resp) : ops) | pid == pid' = [(resp, ops)]
    findResponse  pid (op             : ops)                =
      [ (resp, op : ops') | (resp, ops') <- findResponse pid ops ]

    matchInvocation :: Pid -> Operation -> Bool
    matchInvocation pid (CMD pid' _cmd) = pid == pid'
    matchInvocation _   _               = False

    filter1 :: (a -> Bool) -> [a] -> [a]
    filter1 _ []                   = []
    filter1 p (x : xs) | p x       = x : filter1 p xs
                       | otherwise = xs


linearisable :: Forest (Command, Response) -> Bool
linearisable = any' (go initModel)
  where
    go :: Model -> Tree (Command, Response) -> Bool
    go model (Node (cmd, resp) ts) =
      let
        (model', resp') = step model cmd
      in
        resp == resp' && any' (go model') ts

    any' :: (a -> Bool) -> [a] -> Bool
    any' _p [] = True
    any'  p xs = any p xs

sampleHistory :: History
sampleHistory = [CMD (Pid 1) (Incr 1), CMD (Pid 2) (Incr 2), RESP (Pid 1) (Unit ()), CMD (Pid 1) (Get), RESP (Pid 2) (Unit ()),CMD (Pid 3) Get,  RESP (Pid 1) (Int 3), RESP (Pid 3) (Int 3)]

printInterleavings :: IO ()
printInterleavings =
  (putStrLn . drawForest . fmap (fmap show) . interleavings) sampleHistory

prop_Concurrent :: Property
prop_Concurrent =
  forAllShrinkShow (genConcProgram m) (shrinkConcProgram m)
      show $ \(ConcProgram cmdss) -> monadicIO $ do
    monitor (classifyCommandsLength (concat cmdss))
    -- Rerun a couple of times, to avoid being lucky with the interleavings.
    monitor (tabulate "Commands" (map constructorString (concat cmdss)))
    monitor (tabulate "Number of concurrent commands" (map (show . length) cmdss))
    replicateM_ 10 $ do
      counter <- run newCounter
      queue   <- run newTQueueIO
      run (mapM_ (mapConcurrently (concExec queue counter)) cmdss)
      hist <- run (atomically (flushTQueue queue))
      assertWithFail (linearisable (interleavings hist)) (prettyHistory hist)
  where
    m = initModel

    constructorString :: Command -> String
    constructorString Incr {} = "Incr"
    constructorString Get  {} = "Get"

assertWithFail :: Monad m => Bool -> String -> PropertyM m ()
assertWithFail condition msg = do
  unless condition $
    monitor (counterexample ("Failed: " ++ msg))
  assert condition

classifyCommandsLength :: [Command] -> Property -> Property
classifyCommandsLength cmds
  = classify (length cmds == 0)                        "length commands: 0"
  . classify (0   < length cmds && length cmds <= 10)  "length commands: 1-10"
  . classify (10  < length cmds && length cmds <= 50)  "length commands: 11-50"
  . classify (50  < length cmds && length cmds <= 100) "length commands: 51-100"
  . classify (100 < length cmds && length cmds <= 200) "length commands: 101-200"
  . classify (200 < length cmds && length cmds <= 500) "length commands: 201-500"
  . classify (500 < length cmds)                       "length commands: >501"

prettyHistory :: History -> String
prettyHistory = show

{-@ QuickCheck combinators

arbitrary :: Arbitrary a => Gen a

-- generators
listOf    :: Gen a -> Gen [a]
vectorOf  :: Int   -> Gen a       -> Gen [a]
suchThat  :: Gen a -> (a -> Bool) -> Gen a
oneof     :: [Gen a] -> Gen a
choose    :: Random a => (a, a) -> Gen a
elements  :: [a] -> Gen a
frequency :: [(Int, Gen a)] -> Gen a

-- property combinators
forAll :: (Show a, Testable prop)
       => Gen a -> (a -> prop) -> Property
(==>)  :: Testable prop => Bool -> prop -> Property

generate :: Gen a -> IO a
sample   :: Show a => Gen a -> IO ()

-- shrinking
shrink :: Arbitrary a => a -> [a]
-- Shrink a list of values given a shrinking function
-- for individual values.
shrinkList :: (a -> [a]) -> [a] -> [[a]]

-- forAll with shrinking
forAllShrink
  :: (Show a, Testable prop) =>
     Gen a -> (a -> [a]) -> (a -> prop) -> Property

-- Monadic QuickCheck
run       :: Monad m    => m a -> PropertyM m a
monadicIO :: Testable a => PropertyM IO a -> Property
monitor   :: Monad m => (Property -> Property) -> PropertyM m ()

@-}
