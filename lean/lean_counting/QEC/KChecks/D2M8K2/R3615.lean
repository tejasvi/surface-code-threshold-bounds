import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14460 = true := by
  decide +kernel

theorem tot14460 : totK PD2M8K2 D2M8K2.t14460 = [0, 196663126068, 500092772121, 193862555790, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows14461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14461 = true := by
  decide +kernel

theorem tot14461 : totK PD2M8K2 D2M8K2.t14461 = [177812611450, 371916666204, 263731319780, 107869121370, 6804944647, 0, 0, 0] := by
  decide +kernel

theorem rows14462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14462 = true := by
  decide +kernel

theorem tot14462 : totK PD2M8K2 D2M8K2.t14462 = [153875893019, 462062105802, 273685700807, 17423517457, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14463 = true := by
  decide +kernel

theorem tot14463 : totK PD2M8K2 D2M8K2.t14463 = [0, 260304356332, 492305663650, 149257171472, 8298533344, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
