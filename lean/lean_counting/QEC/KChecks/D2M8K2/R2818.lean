import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11272 = true := by
  decide +kernel

theorem tot11272 : totK PD2M8K2 D2M8K2.t11272 = [90490504222, 359115965356, 366049947274, 79400143696, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows11273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11273 = true := by
  decide +kernel

theorem tot11273 : totK PD2M8K2 D2M8K2.t11273 = [0, 227245513376, 483659394008, 171631516324, 6295843004, 0, 0, 0] := by
  decide +kernel

theorem rows11274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11274 = true := by
  decide +kernel

theorem tot11274 : totK PD2M8K2 D2M8K2.t11274 = [0, 192343257335, 463754023556, 211866463394, 14604724057, 0, 0, 0] := by
  decide +kernel

theorem rows11275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11275 = true := by
  decide +kernel

theorem tot11275 : totK PD2M8K2 D2M8K2.t11275 = [0, 186057319172, 467347055041, 215195478602, 12267505601, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
