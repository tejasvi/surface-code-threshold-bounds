import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10724 = true := by
  decide +kernel

theorem tot10724 : totK PD2M8K2 D2M8K2.t10724 = [0, 0, 0, 247420813479, 493586713258, 174553273969, 9654694938, 0] := by
  decide +kernel

theorem rows10725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10725 = true := by
  decide +kernel

theorem tot10725 : totK PD2M8K2 D2M8K2.t10725 = [0, 0, 85737809554, 297812420303, 373975249633, 128399042794, 5411637735, 0] := by
  decide +kernel

theorem rows10726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10726 = true := by
  decide +kernel

theorem tot10726 : totK PD2M8K2 D2M8K2.t10726 = [0, 0, 181411962985, 466644917185, 251382138019, 20500766586, 0, 0] := by
  decide +kernel

theorem rows10727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10727 = true := by
  decide +kernel

theorem tot10727 : totK PD2M8K2 D2M8K2.t10727 = [0, 0, 172403227915, 471372608096, 251089895493, 13782265251, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
