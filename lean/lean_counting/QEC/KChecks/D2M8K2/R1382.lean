import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5528 = true := by
  decide +kernel

theorem tot5528 : totK PD2M8K2 D2M8K2.t5528 = [0, 0, 289879092238, 459699777048, 106685806223, 1369150432, 0, 0] := by
  decide +kernel

theorem rows5529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5529 = true := by
  decide +kernel

theorem tot5529 : totK PD2M8K2 D2M8K2.t5529 = [0, 156103765308, 453438392162, 264186161659, 22695287968, 0, 0, 0] := by
  decide +kernel

theorem rows5530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5530 = true := by
  decide +kernel

theorem tot5530 : totK PD2M8K2 D2M8K2.t5530 = [0, 176995372658, 458649764719, 233417161518, 13629821414, 0, 0, 0] := by
  decide +kernel

theorem rows5531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5531 = true := by
  decide +kernel

theorem tot5531 : totK PD2M8K2 D2M8K2.t5531 = [0, 174485740025, 476263575089, 231080187778, 12885670648, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
