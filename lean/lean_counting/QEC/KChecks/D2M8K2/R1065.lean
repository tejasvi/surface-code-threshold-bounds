import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4260 = true := by
  decide +kernel

theorem tot4260 : totK PD2M8K2 D2M8K2.t4260 = [0, 0, 0, 172685660425, 461787282688, 239315087828, 9920649387, 0] := by
  decide +kernel

theorem rows4261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4261 = true := by
  decide +kernel

theorem tot4261 : totK PD2M8K2 D2M8K2.t4261 = [0, 0, 0, 196738344163, 462318747799, 221575280416, 20914053737, 0] := by
  decide +kernel

theorem rows4262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4262 = true := by
  decide +kernel

theorem tot4262 : totK PD2M8K2 D2M8K2.t4262 = [0, 0, 0, 188835683734, 472467586372, 220074879346, 9331893713, 0] := by
  decide +kernel

theorem rows4263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4263 = true := by
  decide +kernel

theorem tot4263 : totK PD2M8K2 D2M8K2.t4263 = [0, 0, 0, 47820571596, 397044193328, 407369664644, 39280267923, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
