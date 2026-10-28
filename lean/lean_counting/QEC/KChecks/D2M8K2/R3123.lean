import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12492 = true := by
  decide +kernel

theorem tot12492 : totK PD2M8K2 D2M8K2.t12492 = [0, 0, 169726264932, 459136468997, 221452685677, 11310342365, 0, 0] := by
  decide +kernel

theorem rows12493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12493 = true := by
  decide +kernel

theorem tot12493 : totK PD2M8K2 D2M8K2.t12493 = [0, 0, 216738545837, 480399635326, 187084906607, 9244775796, 0, 0] := by
  decide +kernel

theorem rows12494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12494 = true := by
  decide +kernel

theorem tot12494 : totK PD2M8K2 D2M8K2.t12494 = [0, 0, 183260687819, 460666149867, 213131658292, 12319708528, 0, 0] := by
  decide +kernel

theorem rows12495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12495 = true := by
  decide +kernel

theorem tot12495 : totK PD2M8K2 D2M8K2.t12495 = [0, 0, 166946390691, 489466542660, 221906422586, 10178307621, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
