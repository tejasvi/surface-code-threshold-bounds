import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15340 = true := by
  decide +kernel

theorem tot15340 : totK PD2M8K2 D2M8K2.t15340 = [0, 0, 283888809872, 508291318197, 115167978355, 1190718505, 0, 0] := by
  decide +kernel

theorem rows15341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15341 = true := by
  decide +kernel

theorem tot15341 : totK PD2M8K2 D2M8K2.t15341 = [0, 33314680501, 205481124842, 431369365279, 184471613510, 10587834391, 0, 0] := by
  decide +kernel

theorem rows15342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15342 = true := by
  decide +kernel

theorem tot15342 : totK PD2M8K2 D2M8K2.t15342 = [0, 193041347659, 474983129944, 231530282003, 22079037560, 0, 0, 0] := by
  decide +kernel

theorem rows15343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15343 = true := by
  decide +kernel

theorem tot15343 : totK PD2M8K2 D2M8K2.t15343 = [0, 175594194578, 452506488985, 248941731869, 14739030420, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
