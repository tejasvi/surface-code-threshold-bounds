import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15964 = true := by
  decide +kernel

theorem tot15964 : totK PD2M8K2 D2M8K2.t15964 = [0, 0, 138983479959, 441471391340, 275853147519, 20043116836, 0, 0] := by
  decide +kernel

theorem rows15965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15965 = true := by
  decide +kernel

theorem tot15965 : totK PD2M8K2 D2M8K2.t15965 = [0, 0, 0, 310833650710, 496836614285, 70660088735, 1096505104, 0] := by
  decide +kernel

theorem rows15966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15966 = true := by
  decide +kernel

theorem tot15966 : totK PD2M8K2 D2M8K2.t15966 = [0, 0, 196176404889, 462080677781, 239376480305, 18784143437, 0, 0] := by
  decide +kernel

theorem rows15967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15967 = true := by
  decide +kernel

theorem tot15967 : totK PD2M8K2 D2M8K2.t15967 = [0, 0, 199651552529, 473860485269, 216399866074, 10795835990, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
