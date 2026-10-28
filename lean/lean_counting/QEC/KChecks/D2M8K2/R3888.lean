import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15552 = true := by
  decide +kernel

theorem tot15552 : totK PD2M8K2 D2M8K2.t15552 = [0, 0, 282095049978, 508438629059, 120567828702, 1267860612, 0, 0] := by
  decide +kernel

theorem rows15553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15553 = true := by
  decide +kernel

theorem tot15553 : totK PD2M8K2 D2M8K2.t15553 = [0, 0, 172255509699, 482450295380, 218881522727, 8634597626, 0, 0] := by
  decide +kernel

theorem rows15554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15554 = true := by
  decide +kernel

theorem tot15554 : totK PD2M8K2 D2M8K2.t15554 = [0, 0, 182748149967, 436237841122, 276554772536, 33165414881, 0, 0] := by
  decide +kernel

theorem rows15555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15555 = true := by
  decide +kernel

theorem tot15555 : totK PD2M8K2 D2M8K2.t15555 = [0, 0, 169937826428, 478084200918, 243284457760, 11939762448, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
