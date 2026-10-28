import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t464 = true := by
  decide +kernel

theorem tot464 : totK PD2M8K2 D2M8K2.t464 = [0, 84122848947, 366451143414, 366930052722, 66996204808, 1198073392, 0, 0] := by
  decide +kernel

theorem rows465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t465 = true := by
  decide +kernel

theorem tot465 : totK PD2M8K2 D2M8K2.t465 = [0, 75915349209, 362923836391, 413732099063, 54537533946, 0, 0, 0] := by
  decide +kernel

theorem rows466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t466 = true := by
  decide +kernel

theorem tot466 : totK PD2M8K2 D2M8K2.t466 = [0, 160176361374, 465540406847, 251915490799, 13559100489, 0, 0, 0] := by
  decide +kernel

theorem rows467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t467 = true := by
  decide +kernel

theorem tot467 : totK PD2M8K2 D2M8K2.t467 = [0, 168650718947, 458960202215, 234169830192, 16968298272, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
