import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4388 = true := by
  decide +kernel

theorem tot4388 : totK PD2M8K2 D2M8K2.t4388 = [0, 0, 168671568062, 484154271064, 224307916959, 8671967938, 0, 0] := by
  decide +kernel

theorem rows4389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4389 = true := by
  decide +kernel

theorem tot4389 : totK PD2M8K2 D2M8K2.t4389 = [0, 0, 204304829155, 474447980035, 192833740344, 9090925252, 0, 0] := by
  decide +kernel

theorem rows4390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4390 = true := by
  decide +kernel

theorem tot4390 : totK PD2M8K2 D2M8K2.t4390 = [0, 0, 193037257041, 488796979173, 211177595467, 8378253043, 0, 0] := by
  decide +kernel

theorem rows4391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4391 = true := by
  decide +kernel

theorem tot4391 : totK PD2M8K2 D2M8K2.t4391 = [0, 0, 160303892784, 461434391895, 259170557909, 14245381420, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
