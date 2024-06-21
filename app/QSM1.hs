{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE DerivingStrategies #-}
module QSM1 where

import Control.Monad.IO.Class
import Data.IORef
import Test.QuickCheck
import Test.QuickCheck.Monadic

newtype Counter = Counter (IORef Int)

newCounter :: IO Counter
newCounter = do
  ref <- newIORef 0
  return (Counter ref)

incr :: Counter -> Int -> IO ()
incr (Counter ref) i = do
  j <- readIORef ref
  if j > 1000
  then writeIORef ref (i + j + 1)
  else writeIORef ref (i + j)

get :: Counter -> IO Int
get (Counter ref) = readIORef ref

reset :: Counter -> IO ()
reset (Counter ref) = modifyIORef ref (const 0)

newtype FakeCounter = FakeCounter Int
  deriving stock Show

data Command = Incr Int | Get
             -- | Reset
  deriving stock (Eq, Show)

data Response = Unit () | Int Int
  deriving stock (Eq, Show)

type Model = FakeCounter -- A.k.a. state

mockIncr :: Model -> Int -> (Model, Response)
mockIncr (FakeCounter i) j = (FakeCounter (i+j), Unit ())

mockGet :: Model -> (Model, Response)
mockGet m@(FakeCounter i) = (m, Int i)

mockReset :: Model -> (Model, Response)
mockReset (FakeCounter i) = (FakeCounter 0, Unit ())

initModel :: Model
initModel = FakeCounter 0

step :: Model -> Command -> (Model, Response)
step model (Incr n) = mockIncr  model n
step model Get      = mockGet   model
-- step model Reset    = mockReset model

newtype Program = Program [Command]
  deriving stock Show

genProgram :: Gen Program
genProgram =
  Program <$> (listOf genCommand `suchThat` ((> 0) . length))

genCommand :: Gen Command
genCommand = oneof [Incr <$> genInt, return Get]
  where
    genInt :: Gen Int
    genInt = frequency [ (400, arbitrary `suchThat` (> 0))
                       , (1, return  maxBound)
                       ]

shrinkProgram :: Program -> [Program]
shrinkProgram (Program cmds) =
  [Program (merge cmds') | cmds' <- shrinkList shrinkCommand cmds]
  where
    merge :: [Command] -> [Command]
    merge [] = []
    merge (Incr i : Incr j : cmds') = Incr (i + j) : merge cmds'
    -- merge (Incr i: Reset : cmds')   = Reset : merge cmds'
    merge (cmd: cmds') = cmd : merge cmds'

shrinkCommand :: Command -> [Command]
shrinkCommand (Incr i) = [ Incr i' | i' <- shrink i ]
shrinkCommand Get      = []
-- shrinkCommand Reset    = []

samplePrograms :: IO ()
samplePrograms = sample genProgram

type Trace = [Step]

data Step = Step
  { sModelBefore :: Model
  , sCommand     :: Command
  , sResponse    :: Response
  , sModelAfter  :: Model
  }

-- XXX: What if this function doesn't terminate?
runPrograms :: MonadIO m => Counter -> Model -> Program -> m (Bool, Trace)
runPrograms c0 m0 (Program cmds0) = go c0 m0 [] cmds0
  where
     go _c _m hist []           = return (True, reverse hist)
     go  c  m hist (cmd : cmds) = do
       resp <- liftIO $ exec c cmd  -- real program
       let (m', resp') = step m cmd -- model program
       if resp == resp'
       then go c m' (Step m cmd resp m' : hist) cmds
       else return (False, reverse hist)

exec :: Counter -> Command -> IO Response
exec c cmd = case cmd of
  Incr i -> Unit <$> incr  c i
  Get    -> Int  <$> get   c
  -- Reset  -> Unit <$> reset c

prop_counter :: Property
prop_counter = forAllShrink genProgram shrinkProgram $ \prog -> monadicIO $ do
  c <- run newCounter
  (b, history) <- runPrograms c initModel prog
  monitor (coverage history) -- display results only upon success
  return b

coverage :: Trace -> Property -> Property
coverage hist = classifyLength hist . classifyOverflow hist
  where
    classifyLength xs =
      classify (length xs == 0)                      "0 length"
      . classify (0   < length xs && length xs <= 10)  "1-10 length"
      . classify (10  < length xs && length xs <= 50)  "11-50 length"
      . classify (50  < length xs && length xs <= 100) "51-100 length"
      . classify (100 < length xs && length xs <= 300) "101-300 length"
      . classify (300 < length xs && length xs <= 500) "301-500 length"
    classifyOverflow [] = id
    classifyOverflow (Step (FakeCounter c) (Incr i) _resp _model' : hist') =
       cover 2 (isOverflow c i) "overflow" . classifyOverflow hist'
    classifyOverflow (_ : hist') = classifyOverflow hist'

    isOverflow i j = toInteger i + toInteger j > toInteger (maxBound :: Int)

foo = do
  c <- newCounter
  incr c 5
  incr c 996
  incr c 5
  reset c
  i <- get c
  putStrLn $ "Counter : " <> show i

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
