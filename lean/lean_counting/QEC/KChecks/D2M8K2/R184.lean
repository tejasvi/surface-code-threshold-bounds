import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t736 = true := by
  decide +kernel

theorem tot736 : totK PD2M8K2 D2M8K2.t736 = [0, 233510835326, 486764669321, 165822406461, 8466643012, 0, 0, 0] := by
  decide +kernel

theorem rows737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t737 = true := by
  decide +kernel

theorem tot737 : totK PD2M8K2 D2M8K2.t737 = [123629881743, 359873411996, 326578520535, 85757532283, 3579068459, 0, 0, 0] := by
  decide +kernel

theorem rows738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t738 = true := by
  decide +kernel

theorem tot738 : totK PD2M8K2 D2M8K2.t738 = [170541281389, 444485483749, 265153976325, 27907459689, 0, 0, 0, 0] := by
  decide +kernel

theorem rows739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t739 = true := by
  decide +kernel

theorem tot739 : totK PD2M8K2 D2M8K2.t739 = [146118275952, 454552860989, 296782350975, 23459543939, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
