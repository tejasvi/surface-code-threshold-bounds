import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11996 = true := by
  decide +kernel

theorem tot11996 : totK PD2M8K2 D2M8K2.t11996 = [0, 200973746047, 485658645262, 201338092143, 8105084698, 0, 0, 0] := by
  decide +kernel

theorem rows11997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11997 = true := by
  decide +kernel

theorem tot11997 : totK PD2M8K2 D2M8K2.t11997 = [0, 176133971040, 454236108013, 257489694749, 19325516616, 0, 0, 0] := by
  decide +kernel

theorem rows11998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11998 = true := by
  decide +kernel

theorem tot11998 : totK PD2M8K2 D2M8K2.t11998 = [0, 172314681018, 477762473206, 235184011241, 12480579653, 0, 0, 0] := by
  decide +kernel

theorem rows11999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11999 = true := by
  decide +kernel

theorem tot11999 : totK PD2M8K2 D2M8K2.t11999 = [0, 180238463366, 475474121131, 235599224784, 13845291295, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
