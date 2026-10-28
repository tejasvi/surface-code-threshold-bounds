import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10364 = true := by
  decide +kernel

theorem tot10364 : totK PD2M8K2 D2M8K2.t10364 = [0, 0, 0, 236281875770, 486968854121, 133852081560, 4931404646, 0] := by
  decide +kernel

theorem rows10365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10365 = true := by
  decide +kernel

theorem tot10365 : totK PD2M8K2 D2M8K2.t10365 = [0, 0, 123863213820, 427587644228, 304288096457, 33826599873, 0, 0] := by
  decide +kernel

theorem rows10366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10366 = true := by
  decide +kernel

theorem tot10366 : totK PD2M8K2 D2M8K2.t10366 = [0, 0, 182518778281, 445272380401, 261826437305, 23634715559, 0, 0] := by
  decide +kernel

theorem rows10367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10367 = true := by
  decide +kernel

theorem tot10367 : totK PD2M8K2 D2M8K2.t10367 = [0, 0, 133909833557, 450563006907, 305971827320, 22504783920, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
