import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7404 = true := by
  decide +kernel

theorem tot7404 : totK PD2M8K2 D2M8K2.t7404 = [0, 0, 0, 385510306595, 453676011193, 39568358400, 0, 0] := by
  decide +kernel

theorem rows7405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7405 = true := by
  decide +kernel

theorem tot7405 : totK PD2M8K2 D2M8K2.t7405 = [0, 0, 137659150004, 370248535941, 303422009260, 66003220717, 1376099875, 0] := by
  decide +kernel

theorem rows7406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7406 = true := by
  decide +kernel

theorem tot7406 : totK PD2M8K2 D2M8K2.t7406 = [0, 0, 175358263801, 448285798642, 263349994278, 23367863069, 0, 0] := by
  decide +kernel

theorem rows7407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7407 = true := by
  decide +kernel

theorem tot7407 : totK PD2M8K2 D2M8K2.t7407 = [0, 85146215446, 239813577126, 338401394912, 221741293260, 19480770285, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
