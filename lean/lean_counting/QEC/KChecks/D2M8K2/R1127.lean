import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4508 = true := by
  decide +kernel

theorem tot4508 : totK PD2M8K2 D2M8K2.t4508 = [0, 0, 204326636714, 497033420743, 203299415283, 7960973547, 0, 0] := by
  decide +kernel

theorem rows4509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4509 = true := by
  decide +kernel

theorem tot4509 : totK PD2M8K2 D2M8K2.t4509 = [0, 83078108543, 276516074927, 355586137677, 165682290793, 8213711289, 0, 0] := by
  decide +kernel

theorem rows4510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4510 = true := by
  decide +kernel

theorem tot4510 : totK PD2M8K2 D2M8K2.t4510 = [0, 180617658682, 451459691148, 265008592432, 27730744812, 0, 0, 0] := by
  decide +kernel

theorem rows4511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4511 = true := by
  decide +kernel

theorem tot4511 : totK PD2M8K2 D2M8K2.t4511 = [0, 160784359334, 458878306798, 265242680325, 19924488988, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
