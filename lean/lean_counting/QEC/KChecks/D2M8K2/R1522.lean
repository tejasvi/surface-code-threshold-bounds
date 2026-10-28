import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6088 = true := by
  decide +kernel

theorem tot6088 : totK PD2M8K2 D2M8K2.t6088 = [0, 66979274056, 88280375764, 232641626749, 391936637508, 100601394923, 1429815836, 0] := by
  decide +kernel

theorem rows6089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6089 = true := by
  decide +kernel

theorem tot6089 : totK PD2M8K2 D2M8K2.t6089 = [0, 171058337827, 492950510985, 230969661724, 6541226398, 0, 0, 0] := by
  decide +kernel

theorem rows6090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6090 = true := by
  decide +kernel

theorem tot6090 : totK PD2M8K2 D2M8K2.t6090 = [0, 88787209398, 342605692466, 377710583037, 80298589803, 1369150432, 0, 0] := by
  decide +kernel

theorem rows6091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6091 = true := by
  decide +kernel

theorem tot6091 : totK PD2M8K2 D2M8K2.t6091 = [0, 93610018881, 383727725166, 400720086051, 49482366155, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
