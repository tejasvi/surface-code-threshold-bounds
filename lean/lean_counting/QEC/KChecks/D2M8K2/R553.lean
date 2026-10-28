import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2212 = true := by
  decide +kernel

theorem tot2212 : totK PD2M8K2 D2M8K2.t2212 = [0, 170346574352, 446420355237, 251797501571, 32597312537, 0, 0, 0] := by
  decide +kernel

theorem rows2213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2213 = true := by
  decide +kernel

theorem tot2213 : totK PD2M8K2 D2M8K2.t2213 = [0, 159889420346, 431916407345, 280944173973, 23428083082, 0, 0, 0] := by
  decide +kernel

theorem rows2214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2214 = true := by
  decide +kernel

theorem tot2214 : totK PD2M8K2 D2M8K2.t2214 = [0, 91718010228, 366702987250, 358566150375, 70313698449, 1096505104, 0, 0] := by
  decide +kernel

theorem rows2215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2215 = true := by
  decide +kernel

theorem tot2215 : totK PD2M8K2 D2M8K2.t2215 = [0, 0, 298029849944, 510055627271, 95218421503, 1069412848, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
