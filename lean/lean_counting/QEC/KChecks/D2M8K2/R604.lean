import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2416 = true := by
  decide +kernel

theorem tot2416 : totK PD2M8K2 D2M8K2.t2416 = [0, 93924006320, 360211384379, 378560989251, 75712213368, 1268739303, 0, 0] := by
  decide +kernel

theorem rows2417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2417 = true := by
  decide +kernel

theorem tot2417 : totK PD2M8K2 D2M8K2.t2417 = [0, 0, 256818568639, 494613511423, 145978515098, 3699256714, 0, 0] := by
  decide +kernel

theorem rows2418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2418 = true := by
  decide +kernel

theorem tot2418 : totK PD2M8K2 D2M8K2.t2418 = [0, 0, 187936204613, 466913318865, 217691180232, 17080783126, 0, 0] := by
  decide +kernel

theorem rows2419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2419 = true := by
  decide +kernel

theorem tot2419 : totK PD2M8K2 D2M8K2.t2419 = [0, 0, 170438552657, 485238703913, 224834876387, 6520752454, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
