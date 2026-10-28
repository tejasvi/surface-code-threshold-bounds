import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15468 = true := by
  decide +kernel

theorem tot15468 : totK PD2M8K2 D2M8K2.t15468 = [0, 93610018881, 387315792464, 407678933661, 52914059214, 0, 0, 0] := by
  decide +kernel

theorem rows15469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15469 = true := by
  decide +kernel

theorem tot15469 : totK PD2M8K2 D2M8K2.t15469 = [0, 174769799367, 448792921223, 262693337788, 20877246301, 0, 0, 0] := by
  decide +kernel

theorem rows15470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15470 = true := by
  decide +kernel

theorem tot15470 : totK PD2M8K2 D2M8K2.t15470 = [0, 162484517857, 472566217787, 262572852300, 15900680049, 0, 0, 0] := by
  decide +kernel

theorem rows15471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15471 = true := by
  decide +kernel

theorem tot15471 : totK PD2M8K2 D2M8K2.t15471 = [0, 0, 199690058317, 457121015826, 234741808748, 24250117784, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
