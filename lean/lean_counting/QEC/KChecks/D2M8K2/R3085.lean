import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12340 = true := by
  decide +kernel

theorem tot12340 : totK PD2M8K2 D2M8K2.t12340 = [0, 195914662931, 484286339263, 220148123407, 11066126582, 0, 0, 0] := by
  decide +kernel

theorem rows12341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12341 = true := by
  decide +kernel

theorem tot12341 : totK PD2M8K2 D2M8K2.t12341 = [0, 155688273883, 464953820846, 255900573202, 13597322258, 0, 0, 0] := by
  decide +kernel

theorem rows12342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12342 = true := by
  decide +kernel

theorem tot12342 : totK PD2M8K2 D2M8K2.t12342 = [0, 178458312349, 460173950641, 243690593213, 18484640963, 0, 0, 0] := by
  decide +kernel

theorem rows12343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12343 = true := by
  decide +kernel

theorem tot12343 : totK PD2M8K2 D2M8K2.t12343 = [0, 189051444308, 456360695096, 223983907982, 16702988424, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
