import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4396 = true := by
  decide +kernel

theorem tot4396 : totK PD2M8K2 D2M8K2.t4396 = [0, 39163193280, 218679191958, 442559232347, 198718428985, 8214505460, 0, 0] := by
  decide +kernel

theorem rows4397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4397 = true := by
  decide +kernel

theorem tot4397 : totK PD2M8K2 D2M8K2.t4397 = [0, 192338356846, 466733510519, 247517061225, 23388038350, 0, 0, 0] := by
  decide +kernel

theorem rows4398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4398 = true := by
  decide +kernel

theorem tot4398 : totK PD2M8K2 D2M8K2.t4398 = [0, 192036550133, 471910713796, 223518654058, 12346377983, 0, 0, 0] := by
  decide +kernel

theorem rows4399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4399 = true := by
  decide +kernel

theorem tot4399 : totK PD2M8K2 D2M8K2.t4399 = [0, 0, 300898013379, 496870452005, 103476276631, 1163840124, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
