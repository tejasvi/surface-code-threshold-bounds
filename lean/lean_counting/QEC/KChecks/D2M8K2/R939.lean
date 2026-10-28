import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3756 = true := by
  decide +kernel

theorem tot3756 : totK PD2M8K2 D2M8K2.t3756 = [0, 19691318959, 367469293398, 453733340425, 67234779947, 0, 0, 0] := by
  decide +kernel

theorem rows3757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3757 = true := by
  decide +kernel

theorem tot3757 : totK PD2M8K2 D2M8K2.t3757 = [0, 0, 173712603590, 494235251646, 199347851551, 4763482009, 0, 0] := by
  decide +kernel

theorem rows3758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3758 = true := by
  decide +kernel

theorem tot3758 : totK PD2M8K2 D2M8K2.t3758 = [192306315413, 462721243608, 202675652767, 9852138406, 16217060694, 4538888690, 0, 0] := by
  decide +kernel

theorem rows3759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3759 = true := by
  decide +kernel

theorem tot3759 : totK PD2M8K2 D2M8K2.t3759 = [186516519315, 467613470315, 231876827659, 12197677780, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
