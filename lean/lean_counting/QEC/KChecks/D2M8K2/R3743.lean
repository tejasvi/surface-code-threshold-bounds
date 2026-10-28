import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14972 = true := by
  decide +kernel

theorem tot14972 : totK PD2M8K2 D2M8K2.t14972 = [0, 175379211516, 442397729510, 272722417301, 29836128130, 0, 0, 0] := by
  decide +kernel

theorem rows14973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14973 = true := by
  decide +kernel

theorem tot14973 : totK PD2M8K2 D2M8K2.t14973 = [0, 135679915600, 449194611490, 291547113847, 23575980931, 0, 0, 0] := by
  decide +kernel

theorem rows14974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14974 = true := by
  decide +kernel

theorem tot14974 : totK PD2M8K2 D2M8K2.t14974 = [0, 0, 215843355785, 494515988318, 174514693211, 8143100748, 0, 0] := by
  decide +kernel

theorem rows14975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14975 = true := by
  decide +kernel

theorem tot14975 : totK PD2M8K2 D2M8K2.t14975 = [0, 79122610321, 301006444053, 377109780073, 108883191553, 4906626486, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
