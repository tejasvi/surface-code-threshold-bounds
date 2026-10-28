import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6392 = true := by
  decide +kernel

theorem tot6392 : totK PD2M8K2 D2M8K2.t6392 = [0, 165778232083, 448236761227, 269229360870, 21479586816, 0, 0, 0] := by
  decide +kernel

theorem rows6393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6393 = true := by
  decide +kernel

theorem tot6393 : totK PD2M8K2 D2M8K2.t6393 = [0, 158327626926, 459089261666, 275678525341, 26365922967, 0, 0, 0] := by
  decide +kernel

theorem rows6394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6394 = true := by
  decide +kernel

theorem tot6394 : totK PD2M8K2 D2M8K2.t6394 = [0, 0, 200370644421, 473363651375, 218819335953, 13604428459, 0, 0] := by
  decide +kernel

theorem rows6395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6395 = true := by
  decide +kernel

theorem tot6395 : totK PD2M8K2 D2M8K2.t6395 = [0, 73966261092, 300093920877, 418070946538, 116443481575, 1409560813, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
