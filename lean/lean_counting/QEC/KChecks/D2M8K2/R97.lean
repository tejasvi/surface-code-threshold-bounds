import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t388 = true := by
  decide +kernel

theorem tot388 : totK PD2M8K2 D2M8K2.t388 = [90904776651, 382180839880, 394389254285, 50809413524, 0, 0, 0, 0] := by
  decide +kernel

theorem rows389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t389 = true := by
  decide +kernel

theorem tot389 : totK PD2M8K2 D2M8K2.t389 = [186081945682, 448311872292, 242642718639, 22654231251, 0, 0, 0, 0] := by
  decide +kernel

theorem rows390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t390 = true := by
  decide +kernel

theorem tot390 : totK PD2M8K2 D2M8K2.t390 = [109200570846, 415837903419, 335665071175, 48746798424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t391 = true := by
  decide +kernel

theorem tot391 : totK PD2M8K2 D2M8K2.t391 = [0, 152216770200, 439097769208, 273113041851, 25278154240, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
