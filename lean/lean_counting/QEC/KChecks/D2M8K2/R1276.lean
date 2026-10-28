import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5104 = true := by
  decide +kernel

theorem tot5104 : totK PD2M8K2 D2M8K2.t5104 = [0, 0, 0, 296869998839, 472822222767, 92334906433, 1095107716, 0] := by
  decide +kernel

theorem rows5105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5105 = true := by
  decide +kernel

theorem tot5105 : totK PD2M8K2 D2M8K2.t5105 = [0, 0, 122913013692, 362729852658, 309174357458, 91339667021, 3882006667, 0] := by
  decide +kernel

theorem rows5106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5106 = true := by
  decide +kernel

theorem tot5106 : totK PD2M8K2 D2M8K2.t5106 = [0, 0, 189071264941, 450402564406, 226443640281, 17115888737, 0, 0] := by
  decide +kernel

theorem rows5107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5107 = true := by
  decide +kernel

theorem tot5107 : totK PD2M8K2 D2M8K2.t5107 = [0, 0, 108879417174, 429165634778, 331079602135, 24873878816, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
