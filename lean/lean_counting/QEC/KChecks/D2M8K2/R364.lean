import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1456 = true := by
  decide +kernel

theorem tot1456 : totK PD2M8K2 D2M8K2.t1456 = [0, 0, 210415188785, 468540930920, 230992837346, 18044708413, 0, 0] := by
  decide +kernel

theorem rows1457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1457 = true := by
  decide +kernel

theorem tot1457 : totK PD2M8K2 D2M8K2.t1457 = [0, 0, 205296520142, 487943519639, 199473675801, 10597857724, 0, 0] := by
  decide +kernel

theorem rows1458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1458 = true := by
  decide +kernel

theorem tot1458 : totK PD2M8K2 D2M8K2.t1458 = [0, 0, 205472898824, 481767814792, 204707199206, 11380923020, 0, 0] := by
  decide +kernel

theorem rows1459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1459 = true := by
  decide +kernel

theorem tot1459 : totK PD2M8K2 D2M8K2.t1459 = [0, 0, 186243846001, 470557461425, 213545160951, 12278689302, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
