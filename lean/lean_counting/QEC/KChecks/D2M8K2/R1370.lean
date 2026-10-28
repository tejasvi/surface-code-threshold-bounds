import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5480 = true := by
  decide +kernel

theorem tot5480 : totK PD2M8K2 D2M8K2.t5480 = [0, 0, 19498359861, 312652451873, 467466421104, 91385833534, 1164319620, 0] := by
  decide +kernel

theorem rows5481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5481 = true := by
  decide +kernel

theorem tot5481 : totK PD2M8K2 D2M8K2.t5481 = [0, 0, 0, 226069766434, 501869750873, 153026172509, 5316191185, 0] := by
  decide +kernel

theorem rows5482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5482 = true := by
  decide +kernel

theorem tot5482 : totK PD2M8K2 D2M8K2.t5482 = [0, 0, 186644715946, 457217152444, 234842602810, 22766485928, 0, 0] := by
  decide +kernel

theorem rows5483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5483 = true := by
  decide +kernel

theorem tot5483 : totK PD2M8K2 D2M8K2.t5483 = [0, 0, 212270855152, 481936056419, 200300979932, 9434007521, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
