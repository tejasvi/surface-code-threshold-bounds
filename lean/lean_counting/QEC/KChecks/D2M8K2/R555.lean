import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2220 = true := by
  decide +kernel

theorem tot2220 : totK PD2M8K2 D2M8K2.t2220 = [0, 0, 186971021230, 473355903738, 211136570441, 10794973564, 0, 0] := by
  decide +kernel

theorem rows2221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2221 = true := by
  decide +kernel

theorem tot2221 : totK PD2M8K2 D2M8K2.t2221 = [0, 0, 78900544820, 353015066954, 352614059941, 66507005035, 1239866073, 0] := by
  decide +kernel

theorem rows2222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2222 = true := by
  decide +kernel

theorem tot2222 : totK PD2M8K2 D2M8K2.t2222 = [0, 0, 36484948206, 362012711262, 430643651376, 44669065535, 0, 0] := by
  decide +kernel

theorem rows2223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2223 = true := by
  decide +kernel

theorem tot2223 : totK PD2M8K2 D2M8K2.t2223 = [0, 0, 196387307210, 489469496189, 220586894746, 11423986753, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
