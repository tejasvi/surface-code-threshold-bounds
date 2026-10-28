import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3396 = true := by
  decide +kernel

theorem tot3396 : totK PD2M8K2 D2M8K2.t3396 = [0, 184055839217, 459404912610, 251035835760, 22776889198, 0, 0, 0] := by
  decide +kernel

theorem rows3397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3397 = true := by
  decide +kernel

theorem tot3397 : totK PD2M8K2 D2M8K2.t3397 = [0, 179268887844, 469885576231, 235717104905, 13620090166, 0, 0, 0] := by
  decide +kernel

theorem rows3398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3398 = true := by
  decide +kernel

theorem tot3398 : totK PD2M8K2 D2M8K2.t3398 = [0, 0, 285409658262, 493626584092, 111114976361, 1198073392, 0, 0] := by
  decide +kernel

theorem rows3399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3399 = true := by
  decide +kernel

theorem tot3399 : totK PD2M8K2 D2M8K2.t3399 = [0, 0, 202675745994, 473494262663, 189559042005, 11985024718, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
