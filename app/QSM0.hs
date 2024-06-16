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


step :: Command -> Balance -> IO ()
step (ADDBAL i) bal = addBalance bal i
step (WITHDRAW i) bal = withdraw bal i


-- prop_positive_bal_per_cmd :: [Command] -> Property
-- prop_positive_bal_per_cmd [] = monadicIO $ assert True
-- prop_positive_bal_per_cmd (c:cs) = undefined

prop_positive_bal :: Property
prop_positive_bal = monadicIO $ do
  init_bal <- liftIO $ generate (arbitrary `suchThat` (> 100))
  bal  <- liftIO $ newAccount init_bal
  prog <- liftIO $ generate (arbitrary :: Gen Program)
  let (Program cmds) = prog
  run $ mapM_ (\c -> step c bal) cmds
  bal' <- liftIO $ getBalance bal
  monitor (counterexample ("Initial Balance " ++ show init_bal ++
                           " " ++ show cmds ++
                           "Final Balance: " ++ show bal'))
  assert (bal' > 0)

prop_positive_bal' :: Property
prop_positive_bal' = monadicIO $ do
  init_bal <- liftIO $ generate (arbitrary `suchThat` (> 100))
  bal  <- liftIO $ newAccount init_bal
  prog <- liftIO $ generate (arbitrary :: Gen Program)
  let (Program cmds) = prog
  res <- run (go cmds bal)
  bal' <- liftIO $ getBalance bal
  monitor (counterexample ("Initial Balance " ++ show init_bal ++
                           " " ++ show cmds ++
                           "Final Balance: " ++ show bal'))
  assert res
  where
    go :: [Command] -> Balance -> IO Bool
    go [] _ = pure True
    go (c:cs) bal = do
      step c bal
      b <- getBalance bal
      if (b < 0)
      then pure False
      else go cs bal





foo = do
  acc <- newAccount 5
  addBalance acc 5
  withdraw acc 4
  withdraw acc 7
  bal <- getBalance acc
  putStrLn $ "Balance : " <> show bal
