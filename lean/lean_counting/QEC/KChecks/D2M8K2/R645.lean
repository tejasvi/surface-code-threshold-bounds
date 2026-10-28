import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2580 = true := by
  decide +kernel

theorem tot2580 : totK PD2M8K2 D2M8K2.t2580 = [0, 151653129149, 459942598450, 262285600424, 18337374713, 0, 0, 0] := by
  decide +kernel

theorem rows2581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2581 = true := by
  decide +kernel

theorem tot2581 : totK PD2M8K2 D2M8K2.t2581 = [0, 0, 297149456220, 469601560770, 91626632162, 1095107716, 0, 0] := by
  decide +kernel

theorem rows2582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2582 = true := by
  decide +kernel

theorem tot2582 : totK PD2M8K2 D2M8K2.t2582 = [135288977207, 271369053312, 168717053870, 218116469872, 89936393989, 3882006667, 0, 0] := by
  decide +kernel

theorem rows2583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2583 = true := by
  decide +kernel

theorem tot2583 : totK PD2M8K2 D2M8K2.t2583 = [189480927250, 461620164683, 232901667310, 16833463597, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
