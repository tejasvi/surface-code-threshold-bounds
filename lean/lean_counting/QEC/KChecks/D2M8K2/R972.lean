import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3888 = true := by
  decide +kernel

theorem tot3888 : totK PD2M8K2 D2M8K2.t3888 = [0, 0, 185052782265, 488057040655, 211149969804, 10132347792, 0, 0] := by
  decide +kernel

theorem rows3889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3889 = true := by
  decide +kernel

theorem tot3889 : totK PD2M8K2 D2M8K2.t3889 = [0, 0, 193641071497, 486786718071, 195954980388, 6541871428, 0, 0] := by
  decide +kernel

theorem rows3890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3890 = true := by
  decide +kernel

theorem tot3890 : totK PD2M8K2 D2M8K2.t3890 = [0, 0, 194055252498, 481146374925, 206696927007, 10133125126, 0, 0] := by
  decide +kernel

theorem rows3891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3891 = true := by
  decide +kernel

theorem tot3891 : totK PD2M8K2 D2M8K2.t3891 = [0, 0, 191382647198, 463920905817, 210863017917, 10816184264, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
