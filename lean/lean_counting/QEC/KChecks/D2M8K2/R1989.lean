import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7956 = true := by
  decide +kernel

theorem tot7956 : totK PD2M8K2 D2M8K2.t7956 = [0, 0, 73783516490, 351662035142, 390319001773, 70644679296, 1096505104, 0] := by
  decide +kernel

theorem rows7957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7957 = true := by
  decide +kernel

theorem tot7957 : totK PD2M8K2 D2M8K2.t7957 = [0, 0, 3757402556, 262507496893, 493611853235, 113336620193, 3884009855, 0] := by
  decide +kernel

theorem rows7958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7958 = true := by
  decide +kernel

theorem tot7958 : totK PD2M8K2 D2M8K2.t7958 = [0, 0, 214868872770, 493713336797, 184622175231, 5416482464, 0, 0] := by
  decide +kernel

theorem rows7959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7959 = true := by
  decide +kernel

theorem tot7959 : totK PD2M8K2 D2M8K2.t7959 = [0, 0, 105825649423, 411999500216, 322736348335, 43996446214, 1268739303, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
