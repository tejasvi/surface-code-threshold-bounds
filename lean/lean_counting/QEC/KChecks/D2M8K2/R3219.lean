import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12876 = true := by
  decide +kernel

theorem tot12876 : totK PD2M8K2 D2M8K2.t12876 = [0, 0, 158607486777, 438169962358, 274275266054, 27951024414, 0, 0] := by
  decide +kernel

theorem rows12877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12877 = true := by
  decide +kernel

theorem tot12877 : totK PD2M8K2 D2M8K2.t12877 = [0, 0, 88072440675, 428250223105, 360086579911, 29549108996, 0, 0] := by
  decide +kernel

theorem rows12878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12878 = true := by
  decide +kernel

theorem tot12878 : totK PD2M8K2 D2M8K2.t12878 = [0, 0, 67239190043, 308702949624, 410164273546, 91024567883, 1435164049, 0] := by
  decide +kernel

theorem rows12879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12879 = true := by
  decide +kernel

theorem tot12879 : totK PD2M8K2 D2M8K2.t12879 = [0, 0, 179334680700, 465111650505, 248142575112, 20884098803, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
