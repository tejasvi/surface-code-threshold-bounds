import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7104 = true := by
  decide +kernel

theorem tot7104 : totK PD2M8K2 D2M8K2.t7104 = [0, 0, 86538753630, 394307747037, 334246393991, 50028985011, 1206465782, 0] := by
  decide +kernel

theorem rows7105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7105 = true := by
  decide +kernel

theorem tot7105 : totK PD2M8K2 D2M8K2.t7105 = [0, 0, 15833713871, 329197733453, 462050444916, 59141995501, 0, 0] := by
  decide +kernel

theorem rows7106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7106 = true := by
  decide +kernel

theorem tot7106 : totK PD2M8K2 D2M8K2.t7106 = [0, 0, 176762650320, 469284676805, 254146369385, 22755530258, 0, 0] := by
  decide +kernel

theorem rows7107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7107 = true := by
  decide +kernel

theorem tot7107 : totK PD2M8K2 D2M8K2.t7107 = [0, 0, 206760524750, 480916438683, 207010607957, 11726061196, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
