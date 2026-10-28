import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7080 = true := by
  decide +kernel

theorem tot7080 : totK PD2M8K2 D2M8K2.t7080 = [0, 0, 195582469976, 507099895179, 196351662646, 5265834820, 0, 0] := by
  decide +kernel

theorem rows7081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7081 = true := by
  decide +kernel

theorem tot7081 : totK PD2M8K2 D2M8K2.t7081 = [0, 0, 170522104061, 461136293246, 230244445608, 10510199724, 0, 0] := by
  decide +kernel

theorem rows7082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7082 = true := by
  decide +kernel

theorem tot7082 : totK PD2M8K2 D2M8K2.t7082 = [0, 90905995700, 293101293947, 336905867511, 165684278235, 15168170160, 0, 0] := by
  decide +kernel

theorem rows7083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7083 = true := by
  decide +kernel

theorem tot7083 : totK PD2M8K2 D2M8K2.t7083 = [0, 184161002634, 460565089989, 234119278339, 17111991321, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
