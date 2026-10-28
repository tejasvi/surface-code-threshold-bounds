import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10324 = true := by
  decide +kernel

theorem tot10324 : totK PD2M8K2 D2M8K2.t10324 = [0, 0, 183085300013, 502346586046, 217675604875, 10179897161, 0, 0] := by
  decide +kernel

theorem rows10325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10325 = true := by
  decide +kernel

theorem tot10325 : totK PD2M8K2 D2M8K2.t10325 = [0, 0, 172949880739, 459893230978, 240350143512, 11616113070, 0, 0] := by
  decide +kernel

theorem rows10326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10326 = true := by
  decide +kernel

theorem tot10326 : totK PD2M8K2 D2M8K2.t10326 = [0, 0, 213126509622, 480346222116, 186433542622, 7506458362, 0, 0] := by
  decide +kernel

theorem rows10327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10327 = true := by
  decide +kernel

theorem tot10327 : totK PD2M8K2 D2M8K2.t10327 = [0, 0, 196888177493, 488188645196, 215190983907, 11066126582, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
