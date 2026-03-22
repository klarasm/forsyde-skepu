module Lib
    ( aProcess
    ) where

import ForSyDe.Atom.MoC.SY

aProcess :: Signal Integer -> Signal Integer
aProcess = comb11 (+1)
