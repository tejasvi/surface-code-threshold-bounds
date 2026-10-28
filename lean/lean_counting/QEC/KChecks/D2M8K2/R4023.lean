import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16092 = true := by
  decide +kernel

theorem tot16092 : totK PD2M8K2 D2M8K2.t16092 = [0, 0, 175934478572, 464949397078, 246223014843, 15113749748, 0, 0] := by
  decide +kernel

theorem rows16093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16093 = true := by
  decide +kernel

theorem tot16093 : totK PD2M8K2 D2M8K2.t16093 = [0, 17512063623, 199309854448, 453519419182, 219733728466, 9359077587, 0, 0] := by
  decide +kernel

theorem rows16094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16094 = true := by
  decide +kernel

theorem tot16094 : totK PD2M8K2 D2M8K2.t16094 = [0, 191569446228, 465380959123, 248008787487, 23389784016, 0, 0, 0] := by
  decide +kernel

theorem rows16095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16095 = true := by
  decide +kernel

theorem tot16095 : totK PD2M8K2 D2M8K2.t16095 = [0, 198759407781, 475363793445, 213194671000, 11241790751, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
