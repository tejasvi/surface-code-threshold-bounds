import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t264 = true := by
  decide +kernel

theorem tot264 : totK PD2M8K2 D2M8K2.t264 = [0, 182435010564, 487424913547, 217362156952, 9771395610, 0, 0, 0] := by
  decide +kernel

theorem rows265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t265 = true := by
  decide +kernel

theorem tot265 : totK PD2M8K2 D2M8K2.t265 = [0, 159104674148, 450914762429, 262618249068, 16307055597, 0, 0, 0] := by
  decide +kernel

theorem rows266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t266 = true := by
  decide +kernel

theorem tot266 : totK PD2M8K2 D2M8K2.t266 = [0, 0, 278210720713, 506658130187, 109131187615, 1369150432, 0, 0] := by
  decide +kernel

theorem rows267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t267 = true := by
  decide +kernel

theorem tot267 : totK PD2M8K2 D2M8K2.t267 = [0, 87608005910, 370151129139, 398013349185, 57846240747, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
