import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6596 = true := by
  decide +kernel

theorem tot6596 : totK PD2M8K2 D2M8K2.t6596 = [0, 168567008104, 465240124746, 218634421261, 14344490487, 0, 0, 0] := by
  decide +kernel

theorem rows6597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6597 = true := by
  decide +kernel

theorem tot6597 : totK PD2M8K2 D2M8K2.t6597 = [0, 152099302163, 450898029473, 247232170393, 14977982414, 0, 0, 0] := by
  decide +kernel

theorem rows6598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6598 = true := by
  decide +kernel

theorem tot6598 : totK PD2M8K2 D2M8K2.t6598 = [0, 0, 302577669700, 464204518355, 78403596793, 1138244013, 0, 0] := by
  decide +kernel

theorem rows6599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6599 = true := by
  decide +kernel

theorem tot6599 : totK PD2M8K2 D2M8K2.t6599 = [0, 180027324132, 465608837300, 249081423326, 23082057477, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
