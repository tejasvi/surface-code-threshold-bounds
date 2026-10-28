import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2596 = true := by
  decide +kernel

theorem tot2596 : totK PD2M8K2 D2M8K2.t2596 = [76209290054, 352716536129, 394158585292, 85162307945, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows2597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2597 = true := by
  decide +kernel

theorem tot2597 : totK PD2M8K2 D2M8K2.t2597 = [0, 200585972280, 474198079974, 190470670519, 11885993687, 0, 0, 0] := by
  decide +kernel

theorem rows2598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2598 = true := by
  decide +kernel

theorem tot2598 : totK PD2M8K2 D2M8K2.t2598 = [172666973679, 451461491054, 270808103275, 34422166601, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2599 = true := by
  decide +kernel

theorem tot2599 : totK PD2M8K2 D2M8K2.t2599 = [175878735128, 451010844847, 264695050737, 21553619811, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
