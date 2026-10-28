import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1200 = true := by
  decide +kernel

theorem tot1200 : totK PD2M8K2 D2M8K2.t1200 = [0, 88265605660, 358961423282, 352209753091, 77534211109, 1369150432, 0, 0] := by
  decide +kernel

theorem rows1201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1201 = true := by
  decide +kernel

theorem tot1201 : totK PD2M8K2 D2M8K2.t1201 = [0, 0, 335125255646, 459306094403, 65197547034, 0, 0, 0] := by
  decide +kernel

theorem rows1202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1202 = true := by
  decide +kernel

theorem tot1202 : totK PD2M8K2 D2M8K2.t1202 = [0, 221186405672, 489187428981, 188084978749, 5446766509, 0, 0, 0] := by
  decide +kernel

theorem rows1203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1203 = true := by
  decide +kernel

theorem tot1203 : totK PD2M8K2 D2M8K2.t1203 = [0, 188280026943, 470717293352, 211124152563, 12243442891, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
