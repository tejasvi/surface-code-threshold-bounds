import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9804 = true := by
  decide +kernel

theorem tot9804 : totK PD2M8K2 D2M8K2.t9804 = [0, 155666639267, 461116912243, 271154638339, 18750911563, 0, 0, 0] := by
  decide +kernel

theorem rows9805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9805 = true := by
  decide +kernel

theorem tot9805 : totK PD2M8K2 D2M8K2.t9805 = [0, 157518307958, 448863577807, 258231983234, 16367744543, 0, 0, 0] := by
  decide +kernel

theorem rows9806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9806 = true := by
  decide +kernel

theorem tot9806 : totK PD2M8K2 D2M8K2.t9806 = [0, 0, 279580645770, 514973287013, 95196342150, 1096505104, 0, 0] := by
  decide +kernel

theorem rows9807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9807 = true := by
  decide +kernel

theorem tot9807 : totK PD2M8K2 D2M8K2.t9807 = [0, 128824206414, 360063447812, 311157265297, 83939085429, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
