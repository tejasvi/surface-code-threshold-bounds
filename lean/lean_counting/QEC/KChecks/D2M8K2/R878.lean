import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3512 = true := by
  decide +kernel

theorem tot3512 : totK PD2M8K2 D2M8K2.t3512 = [0, 211584988492, 487577367567, 201914236439, 7991928755, 0, 0, 0] := by
  decide +kernel

theorem rows3513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3513 = true := by
  decide +kernel

theorem tot3513 : totK PD2M8K2 D2M8K2.t3513 = [84104726401, 262971229681, 361857310271, 172465644886, 8187419287, 0, 0, 0] := by
  decide +kernel

theorem rows3514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3514 = true := by
  decide +kernel

theorem tot3514 : totK PD2M8K2 D2M8K2.t3514 = [182457623694, 461850636910, 264823848983, 24065771945, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3515 = true := by
  decide +kernel

theorem tot3515 : totK PD2M8K2 D2M8K2.t3515 = [171341364500, 471191869081, 248354475926, 12662173714, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
