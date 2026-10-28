import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5536 = true := by
  decide +kernel

theorem tot5536 : totK PD2M8K2 D2M8K2.t5536 = [0, 208680442954, 478376058099, 205775502304, 8394630506, 0, 0, 0] := by
  decide +kernel

theorem rows5537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5537 = true := by
  decide +kernel

theorem tot5537 : totK PD2M8K2 D2M8K2.t5537 = [0, 201378224809, 472805150201, 205253439245, 7870241454, 0, 0, 0] := by
  decide +kernel

theorem rows5538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5538 = true := by
  decide +kernel

theorem tot5538 : totK PD2M8K2 D2M8K2.t5538 = [179595312347, 373945584878, 221917012854, 121612577862, 13468148062, 0, 0, 0] := by
  decide +kernel

theorem rows5539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5539 = true := by
  decide +kernel

theorem tot5539 : totK PD2M8K2 D2M8K2.t5539 = [155203790292, 449897349859, 253016382080, 18193274633, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
