import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5392 = true := by
  decide +kernel

theorem tot5392 : totK PD2M8K2 D2M8K2.t5392 = [0, 0, 151030372931, 440194675107, 309517981608, 35769834095, 0, 0] := by
  decide +kernel

theorem rows5393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5393 = true := by
  decide +kernel

theorem tot5393 : totK PD2M8K2 D2M8K2.t5393 = [0, 0, 191555346723, 468730741948, 233031350886, 15378596648, 0, 0] := by
  decide +kernel

theorem rows5394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5394 = true := by
  decide +kernel

theorem tot5394 : totK PD2M8K2 D2M8K2.t5394 = [0, 0, 126440840104, 446009788898, 315103418400, 35028303828, 0, 0] := by
  decide +kernel

theorem rows5395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5395 = true := by
  decide +kernel

theorem tot5395 : totK PD2M8K2 D2M8K2.t5395 = [0, 0, 0, 172478553568, 447797900107, 257796601529, 25330798048, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
