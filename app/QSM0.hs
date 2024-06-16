{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE DerivingStrategies #-}
module QSM2 where

import Control.Concurrent.Async (concurrently_)
import Control.Monad (forM_)
import Control.Monad.IO.Class
import Data.IORef
import Test.QuickCheck
import Test.QuickCheck.Monadic

-- https://www.linkedin.com/posts/hillel-wayne_one-of-the-ways-formal-methods-can-find-bugs-activity-7206681074142236673-YotX/?utm_source=share&utm_medium=member_desktop

newtype Balance = Balance (IORef Int)

newAccount :: Int -> IO Balance
newAccount init_bal = do
  ref <- newIORef init_bal
  return (Balance ref)

addBalance :: Balance -> Int -> IO ()
addBalance (Balance ref) i = do
  j <- readIORef ref
  writeIORef ref (i + j)

withdraw :: Balance -> Int -> IO ()
withdraw (Balance ref) i = do
  j <- readIORef ref
  writeIORef ref (j - i)

getBalance :: Balance -> IO Int
getBalance (Balance ref) = do
  j <- readIORef ref
  pure j

data Command = ADDBAL Int
             | WITHDRAW Int
             deriving (Show, Eq)

instance Arbitrary Command where
  arbitrary = do
    i <- arbitrary `suchThat` (> 0)
    j <- arbitrary `suchThat` (> 0)
    oneof [return (ADDBAL i), return (WITHDRAW j)]

newtype Program = Program [Command]
  deriving stock (Eq, Show)

instance Arbitrary Program where
  arbitrary = Program <$> listOf arbitrary

  shrink :: Program -> [Program]
  shrink (Program cmds) =
    [Program (merge cmds') | cmds' <- shrinkList shrinkCommand cmds]
    where
      merge :: [Command] -> [Command]
      merge [] = []
      merge (ADDBAL i : ADDBAL j : cmds')     = ADDBAL (i + j)   : merge cmds'
      merge (WITHDRAW i : WITHDRAW j : cmds') = WITHDRAW (i + j) : merge cmds'
      merge (ADDBAL i : WITHDRAW j : cmds')
        | i >= j    = ADDBAL (i - j)   : merge cmds'
        | otherwise = WITHDRAW (j - i) : merge cmds'
      merge (WITHDRAW i : ADDBAL j : cmds')
        | i >= j    = WITHDRAW (i - j) : merge cmds'
        | otherwise = ADDBAL (j - i)   : merge cmds'
      merge (cmd: cmds') = cmd : merge cmds'

      shrinkCommand :: Command -> [Command]
      shrinkCommand (ADDBAL i)   = [ ADDBAL i'   | i' <- shrink i]
      shrinkCommand (WITHDRAW i) = [ WITHDRAW i' | i' <- shrink i]


step :: Balance -> Command -> IO ()
step bal (ADDBAL i)   = addBalance bal i
step bal (WITHDRAW i) = withdraw bal i


prop_positive_bal :: Property
prop_positive_bal = monadicIO $ do
  (initBal, cmds) <- liftIO $ gen_balance_and_prog
  bal  <- liftIO $ newAccount initBal
  run  $  mapM_ (step bal) cmds
  bal' <- liftIO $ getBalance bal
  monitor (counterexample ("Initial Balance " ++ show initBal ++
                           " " ++ show cmds ++
                           "Final Balance: " ++ show bal'))
  assert (bal' > 0)


gen_balance_and_prog :: IO (Int, [Command])
gen_balance_and_prog = generate $ do
  init_bal <- arbitrary `suchThat` (> 100)
  prog     <- arbitrary
  let (Program cmds) = prog
  return (init_bal, cmds)



foo = do
  acc <- newAccount 5
  addBalance acc 5
  withdraw acc 4
  withdraw acc 7
  bal <- getBalance acc
  putStrLn $ "Balance : " <> show bal
