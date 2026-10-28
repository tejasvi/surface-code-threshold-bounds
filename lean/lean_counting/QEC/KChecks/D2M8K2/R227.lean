import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t908 = true := by
  decide +kernel

theorem tot908 : totK PD2M8K2 D2M8K2.t908 = [25329802317, 273069471791, 477656351752, 123803916873, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t909 = true := by
  decide +kernel

theorem tot909 : totK PD2M8K2 D2M8K2.t909 = [199896113159, 485518065960, 209321923826, 9813691056, 0, 0, 0, 0] := by
  decide +kernel

theorem rows910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t910 = true := by
  decide +kernel

theorem tot910 : totK PD2M8K2 D2M8K2.t910 = [115260493205, 430189183693, 335948310966, 30508105564, 0, 0, 0, 0] := by
  decide +kernel

theorem rows911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t911 = true := by
  decide +kernel

theorem tot911 : totK PD2M8K2 D2M8K2.t911 = [0, 184321663372, 486912351457, 195569613970, 6033099918, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
