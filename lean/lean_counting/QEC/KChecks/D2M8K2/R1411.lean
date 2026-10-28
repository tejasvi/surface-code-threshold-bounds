import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5644 = true := by
  decide +kernel

theorem tot5644 : totK PD2M8K2 D2M8K2.t5644 = [173655177423, 446489996086, 269372827609, 28694063011, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5645 = true := by
  decide +kernel

theorem tot5645 : totK PD2M8K2 D2M8K2.t5645 = [114376722973, 433002805302, 326799372368, 29099387376, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5646 = true := by
  decide +kernel

theorem tot5646 : totK PD2M8K2 D2M8K2.t5646 = [0, 202466581976, 493879601481, 185051562766, 9583672031, 0, 0, 0] := by
  decide +kernel

theorem rows5647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5647 = true := by
  decide +kernel

theorem tot5647 : totK PD2M8K2 D2M8K2.t5647 = [103392314000, 348159937695, 344488078759, 88060006305, 3460111309, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
