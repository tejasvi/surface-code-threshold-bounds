import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6352 = true := by
  decide +kernel

theorem tot6352 : totK PD2M8K2 D2M8K2.t6352 = [0, 179150813341, 397491456892, 213561492266, 100145871098, 11574339130, 0, 0] := by
  decide +kernel

theorem rows6353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6353 = true := by
  decide +kernel

theorem tot6353 : totK PD2M8K2 D2M8K2.t6353 = [0, 167663178353, 449380902556, 231898704091, 14902632746, 0, 0, 0] := by
  decide +kernel

theorem rows6354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6354 = true := by
  decide +kernel

theorem tot6354 : totK PD2M8K2 D2M8K2.t6354 = [0, 68447766432, 331156505036, 403890595191, 82702775872, 1334361349, 0, 0] := by
  decide +kernel

theorem rows6355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6355 = true := by
  decide +kernel

theorem tot6355 : totK PD2M8K2 D2M8K2.t6355 = [0, 52378864304, 349244933817, 454401880110, 48974580800, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
