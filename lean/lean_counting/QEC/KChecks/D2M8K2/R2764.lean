import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11056 = true := by
  decide +kernel

theorem tot11056 : totK PD2M8K2 D2M8K2.t11056 = [177617385333, 446273675215, 264012604661, 28912744582, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11057 = true := by
  decide +kernel

theorem tot11057 : totK PD2M8K2 D2M8K2.t11057 = [122143486344, 435703432358, 307570674746, 24918203585, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11058 = true := by
  decide +kernel

theorem tot11058 : totK PD2M8K2 D2M8K2.t11058 = [0, 197983992872, 483159910379, 190308252661, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows11059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11059 = true := by
  decide +kernel

theorem tot11059 : totK PD2M8K2 D2M8K2.t11059 = [86654048599, 330393617008, 365066283770, 99145618535, 3581949829, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
