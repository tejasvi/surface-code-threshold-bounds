import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8528 = true := by
  decide +kernel

theorem tot8528 : totK PD2M8K2 D2M8K2.t8528 = [0, 171636277593, 437870778211, 273395127520, 28310883041, 0, 0, 0] := by
  decide +kernel

theorem rows8529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8529 = true := by
  decide +kernel

theorem tot8529 : totK PD2M8K2 D2M8K2.t8529 = [0, 92515481918, 434796270828, 343328528788, 35021474315, 0, 0, 0] := by
  decide +kernel

theorem rows8530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8530 = true := by
  decide +kernel

theorem tot8530 : totK PD2M8K2 D2M8K2.t8530 = [0, 0, 232651520355, 495753036137, 146187773497, 2484078857, 0, 0] := by
  decide +kernel

theorem rows8531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8531 = true := by
  decide +kernel

theorem tot8531 : totK PD2M8K2 D2M8K2.t8531 = [93572267332, 241780322324, 226591691937, 235474307905, 109824496519, 6818291842, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
