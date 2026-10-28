import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1472 = true := by
  decide +kernel

theorem tot1472 : totK PD2M8K2 D2M8K2.t1472 = [0, 0, 171691699245, 480946874343, 215704630152, 4878316567, 0, 0] := by
  decide +kernel

theorem rows1473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1473 = true := by
  decide +kernel

theorem tot1473 : totK PD2M8K2 D2M8K2.t1473 = [0, 130736772173, 354526634890, 299798487236, 114904439866, 6804944647, 0, 0] := by
  decide +kernel

theorem rows1474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1474 = true := by
  decide +kernel

theorem tot1474 : totK PD2M8K2 D2M8K2.t1474 = [0, 165305123217, 430742394715, 269710131914, 29478065379, 0, 0, 0] := by
  decide +kernel

theorem rows1475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1475 = true := by
  decide +kernel

theorem tot1475 : totK PD2M8K2 D2M8K2.t1475 = [0, 122586310065, 438560833200, 312391884096, 22783694169, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
