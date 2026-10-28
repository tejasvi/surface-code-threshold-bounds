import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16052 = true := by
  decide +kernel

theorem tot16052 : totK PD2M8K2 D2M8K2.t16052 = [0, 0, 0, 246641548351, 494255480987, 150124841957, 6703801254, 0] := by
  decide +kernel

theorem rows16053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16053 = true := by
  decide +kernel

theorem tot16053 : totK PD2M8K2 D2M8K2.t16053 = [0, 0, 142241969926, 397384193270, 298050334819, 60210157231, 994345478, 0] := by
  decide +kernel

theorem rows16054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16054 = true := by
  decide +kernel

theorem tot16054 : totK PD2M8K2 D2M8K2.t16054 = [0, 0, 175838318300, 445639745029, 267867937353, 27466723085, 0, 0] := by
  decide +kernel

theorem rows16055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16055 = true := by
  decide +kernel

theorem tot16055 : totK PD2M8K2 D2M8K2.t16055 = [0, 0, 119720678104, 436432738691, 330968127686, 28873637601, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
