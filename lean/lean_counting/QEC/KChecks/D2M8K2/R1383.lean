import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5532 = true := by
  decide +kernel

theorem tot5532 : totK PD2M8K2 D2M8K2.t5532 = [0, 191981900653, 454016481535, 215566662876, 12679943201, 0, 0, 0] := by
  decide +kernel

theorem rows5533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5533 = true := by
  decide +kernel

theorem tot5533 : totK PD2M8K2 D2M8K2.t5533 = [0, 191661522170, 470917671132, 209210502233, 12595094539, 0, 0, 0] := by
  decide +kernel

theorem rows5534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5534 = true := by
  decide +kernel

theorem tot5534 : totK PD2M8K2 D2M8K2.t5534 = [0, 158861950129, 479623693772, 229491749867, 8671967938, 0, 0, 0] := by
  decide +kernel

theorem rows5535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5535 = true := by
  decide +kernel

theorem tot5535 : totK PD2M8K2 D2M8K2.t5535 = [0, 174448159842, 456623546716, 225840966246, 13132442356, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
