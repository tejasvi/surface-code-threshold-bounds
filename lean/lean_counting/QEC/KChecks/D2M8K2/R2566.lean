import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10264 = true := by
  decide +kernel

theorem tot10264 : totK PD2M8K2 D2M8K2.t10264 = [0, 175688188989, 476562194703, 232827814288, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows10265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10265 = true := by
  decide +kernel

theorem tot10265 : totK PD2M8K2 D2M8K2.t10265 = [0, 0, 274047601251, 501736371228, 107924398262, 1369150432, 0, 0] := by
  decide +kernel

theorem rows10266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10266 = true := by
  decide +kernel

theorem tot10266 : totK PD2M8K2 D2M8K2.t10266 = [0, 93305483181, 388130068823, 389038860318, 51230403572, 0, 0, 0] := by
  decide +kernel

theorem rows10267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10267 = true := by
  decide +kernel

theorem tot10267 : totK PD2M8K2 D2M8K2.t10267 = [0, 158810478943, 450086373444, 288346640876, 22913866869, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
