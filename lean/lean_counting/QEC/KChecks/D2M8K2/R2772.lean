import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11088 = true := by
  decide +kernel

theorem tot11088 : totK PD2M8K2 D2M8K2.t11088 = [0, 209511424815, 467126361483, 192507462961, 12045711471, 0, 0, 0] := by
  decide +kernel

theorem rows11089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11089 = true := by
  decide +kernel

theorem tot11089 : totK PD2M8K2 D2M8K2.t11089 = [196322580659, 456173305944, 239188229670, 27471615087, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11090 = true := by
  decide +kernel

theorem tot11090 : totK PD2M8K2 D2M8K2.t11090 = [178202146060, 460922107831, 238928717265, 16684993013, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11091 = true := by
  decide +kernel

theorem tot11091 : totK PD2M8K2 D2M8K2.t11091 = [49282675271, 322064346389, 431740507314, 100300039954, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
