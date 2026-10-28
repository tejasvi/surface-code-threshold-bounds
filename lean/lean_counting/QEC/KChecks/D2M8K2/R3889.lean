import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15556 = true := by
  decide +kernel

theorem tot15556 : totK PD2M8K2 D2M8K2.t15556 = [0, 0, 88825966916, 343500280501, 368681952338, 109496692814, 12902418090, 0] := by
  decide +kernel

theorem rows15557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15557 = true := by
  decide +kernel

theorem tot15557 : totK PD2M8K2 D2M8K2.t15557 = [0, 0, 0, 179850491231, 465968138738, 227659282363, 12235493097, 0] := by
  decide +kernel

theorem rows15558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15558 = true := by
  decide +kernel

theorem tot15558 : totK PD2M8K2 D2M8K2.t15558 = [0, 0, 52305724443, 235298643546, 413219618918, 175571851248, 7877424857, 0] := by
  decide +kernel

theorem rows15559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15559 = true := by
  decide +kernel

theorem tot15559 : totK PD2M8K2 D2M8K2.t15559 = [0, 0, 200078571336, 459513367417, 241804530843, 22858987141, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
