import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2392 = true := by
  decide +kernel

theorem tot2392 : totK PD2M8K2 D2M8K2.t2392 = [0, 0, 0, 293162744926, 490803770673, 98737384962, 1171084559, 0] := by
  decide +kernel

theorem rows2393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2393 = true := by
  decide +kernel

theorem tot2393 : totK PD2M8K2 D2M8K2.t2393 = [0, 0, 81275040639, 355098424379, 350117170856, 89307177200, 4254746638, 0] := by
  decide +kernel

theorem rows2394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2394 = true := by
  decide +kernel

theorem tot2394 : totK PD2M8K2 D2M8K2.t2394 = [0, 0, 195630125739, 470513477377, 229873747530, 12912075212, 0, 0] := by
  decide +kernel

theorem rows2395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2395 = true := by
  decide +kernel

theorem tot2395 : totK PD2M8K2 D2M8K2.t2395 = [0, 0, 208063343460, 489032962775, 181175091791, 5242142951, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
