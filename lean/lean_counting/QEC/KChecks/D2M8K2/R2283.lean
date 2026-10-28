import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9132 = true := by
  decide +kernel

theorem tot9132 : totK PD2M8K2 D2M8K2.t9132 = [0, 122242817460, 275162690334, 182392554377, 214958598959, 76590533551, 3819176523, 0] := by
  decide +kernel

theorem rows9133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9133 = true := by
  decide +kernel

theorem tot9133 : totK PD2M8K2 D2M8K2.t9133 = [0, 192672223740, 459024425435, 213819231289, 12637928123, 0, 0, 0] := by
  decide +kernel

theorem rows9134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9134 = true := by
  decide +kernel

theorem tot9134 : totK PD2M8K2 D2M8K2.t9134 = [0, 88990076640, 388820900418, 354331451344, 57450447324, 1369150432, 0, 0] := by
  decide +kernel

theorem rows9135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9135 = true := by
  decide +kernel

theorem tot9135 : totK PD2M8K2 D2M8K2.t9135 = [0, 0, 294028634949, 515795453997, 77770459691, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
