import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2484 = true := by
  decide +kernel

theorem tot2484 : totK PD2M8K2 D2M8K2.t2484 = [0, 162199455996, 448596524240, 275501215419, 25368447013, 0, 0, 0] := by
  decide +kernel

theorem rows2485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2485 = true := by
  decide +kernel

theorem tot2485 : totK PD2M8K2 D2M8K2.t2485 = [0, 174232524196, 473992834805, 232238019968, 8931382700, 0, 0, 0] := by
  decide +kernel

theorem rows2486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2486 = true := by
  decide +kernel

theorem tot2486 : totK PD2M8K2 D2M8K2.t2486 = [189138556760, 453596733792, 244014426734, 27061298859, 2174602308, 0, 0, 0] := by
  decide +kernel

theorem rows2487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2487 = true := by
  decide +kernel

theorem tot2487 : totK PD2M8K2 D2M8K2.t2487 = [198598261320, 476836422564, 221545565227, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
