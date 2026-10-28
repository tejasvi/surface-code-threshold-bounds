import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7580 = true := by
  decide +kernel

theorem tot7580 : totK PD2M8K2 D2M8K2.t7580 = [0, 0, 177199642935, 454345930326, 262983915538, 25162668854, 0, 0] := by
  decide +kernel

theorem rows7581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7581 = true := by
  decide +kernel

theorem tot7581 : totK PD2M8K2 D2M8K2.t7581 = [0, 37052073317, 202948993541, 429070471009, 225891098937, 14355102150, 0, 0] := by
  decide +kernel

theorem rows7582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7582 = true := by
  decide +kernel

theorem tot7582 : totK PD2M8K2 D2M8K2.t7582 = [0, 191513709406, 477312832844, 209949382957, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows7583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7583 = true := by
  decide +kernel

theorem tot7583 : totK PD2M8K2 D2M8K2.t7583 = [0, 174744310784, 459244218691, 225807701928, 13795945806, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
