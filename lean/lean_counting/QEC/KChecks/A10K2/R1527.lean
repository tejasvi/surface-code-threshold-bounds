import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6108 = true := by
  decide +kernel

theorem tot6108 : totK PA10K2 A10K2.t6108 = [0, 321107158991, 1128776053227, 1178218287647, 734802023590, 1002327576633, 501217979401, 48886019071, 0, 0] := by
  decide +kernel

theorem rows6109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6109 = true := by
  decide +kernel

theorem tot6109 : totK PA10K2 A10K2.t6109 = [0, 548792962994, 1935249761635, 1902109345525, 453997062683, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6110 = true := by
  decide +kernel

theorem tot6110 : totK PA10K2 A10K2.t6110 = [0, 0, 648911865559, 2012862643217, 1704426898274, 400406620018, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows6111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6111 = true := by
  decide +kernel

theorem tot6111 : totK PA10K2 A10K2.t6111 = [0, 293873915135, 1220928993576, 1921799228392, 1200604322515, 190779593529, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
