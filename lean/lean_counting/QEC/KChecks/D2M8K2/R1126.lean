import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4504 = true := by
  decide +kernel

theorem tot4504 : totK PD2M8K2 D2M8K2.t4504 = [0, 0, 288980289077, 519397318763, 96741188913, 1369150432, 0, 0] := by
  decide +kernel

theorem rows4505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4505 = true := by
  decide +kernel

theorem tot4505 : totK PD2M8K2 D2M8K2.t4505 = [0, 180654617217, 446641011077, 266791719471, 30779545020, 0, 0, 0] := by
  decide +kernel

theorem rows4506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4506 = true := by
  decide +kernel

theorem tot4506 : totK PD2M8K2 D2M8K2.t4506 = [0, 203009868069, 491323966201, 221582543549, 11236481552, 0, 0, 0] := by
  decide +kernel

theorem rows4507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4507 = true := by
  decide +kernel

theorem tot4507 : totK PD2M8K2 D2M8K2.t4507 = [0, 34345744739, 274700819581, 404868487253, 183218940464, 21380039407, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
