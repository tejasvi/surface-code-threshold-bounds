import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8184 = true := by
  decide +kernel

theorem tot8184 : totK PD2M8K2 D2M8K2.t8184 = [0, 90441204705, 374260617909, 364775571111, 90498806877, 10443484490, 0, 0] := by
  decide +kernel

theorem rows8185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8185 = true := by
  decide +kernel

theorem tot8185 : totK PD2M8K2 D2M8K2.t8185 = [0, 0, 172440977869, 455272126762, 244701436576, 16418932420, 0, 0] := by
  decide +kernel

theorem rows8186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8186 = true := by
  decide +kernel

theorem tot8186 : totK PD2M8K2 D2M8K2.t8186 = [0, 36946381487, 203423964551, 433743490050, 217403219542, 8204069046, 0, 0] := by
  decide +kernel

theorem rows8187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8187 = true := by
  decide +kernel

theorem tot8187 : totK PD2M8K2 D2M8K2.t8187 = [0, 176346316846, 454349314116, 255030800133, 23080323466, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
