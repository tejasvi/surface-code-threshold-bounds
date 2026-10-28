import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t912 = true := by
  decide +kernel

theorem tot912 : totK PD2M8K2 D2M8K2.t912 = [0, 180218330610, 467270819069, 234060319518, 17385499678, 0, 0, 0] := by
  decide +kernel

theorem rows913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t913 = true := by
  decide +kernel

theorem tot913 : totK PD2M8K2 D2M8K2.t913 = [0, 173281809592, 456867135183, 225209062204, 16632994142, 0, 0, 0] := by
  decide +kernel

theorem rows914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t914 = true := by
  decide +kernel

theorem tot914 : totK PD2M8K2 D2M8K2.t914 = [0, 170425830964, 460038894980, 230920611218, 17079186840, 0, 0, 0] := by
  decide +kernel

theorem rows915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t915 = true := by
  decide +kernel

theorem tot915 : totK PD2M8K2 D2M8K2.t915 = [0, 0, 286352050991, 468672606221, 103448860700, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
