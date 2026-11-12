module Lib
    ( aProcess
    ) where

import ForSyDe.Atom.MoC.SY as SY

aProcess :: Signal Integer -> Signal Integer
aProcess = comb11 (+1)

system_div :: Signal Integer -> Signal Integer -> (Signal Integer, Signal Integer)
system_div s_a s_b = (s_div, s_quot) where
  s_div = SY.comb21 div s_a s_b
  s_quot = SY.comb21 quot s_a s_b
