import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12660 = true := by
  decide +kernel

theorem tot12660 : totK PD2M8K2 D2M8K2.t12660 = [0, 0, 172013363287, 464305827483, 262381880649, 19695344657, 0, 0] := by
  decide +kernel

theorem rows12661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12661 = true := by
  decide +kernel

theorem tot12661 : totK PD2M8K2 D2M8K2.t12661 = [0, 0, 185900904694, 489569420355, 224757719791, 7978993580, 0, 0] := by
  decide +kernel

theorem rows12662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12662 = true := by
  decide +kernel

theorem tot12662 : totK PD2M8K2 D2M8K2.t12662 = [0, 0, 179237366747, 449181143694, 261661296445, 22781763169, 0, 0] := by
  decide +kernel

theorem rows12663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12663 = true := by
  decide +kernel

theorem tot12663 : totK PD2M8K2 D2M8K2.t12663 = [0, 0, 139072279963, 447793296432, 282834539392, 20392946328, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
