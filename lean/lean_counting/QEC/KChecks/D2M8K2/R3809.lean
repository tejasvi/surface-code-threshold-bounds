import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15236 = true := by
  decide +kernel

theorem tot15236 : totK PD2M8K2 D2M8K2.t15236 = [0, 0, 154429761851, 457210331643, 283115161305, 23422710607, 0, 0] := by
  decide +kernel

theorem rows15237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15237 = true := by
  decide +kernel

theorem tot15237 : totK PD2M8K2 D2M8K2.t15237 = [0, 0, 174343224309, 443958858368, 247733944191, 14135316221, 0, 0] := by
  decide +kernel

theorem rows15238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15238 = true := by
  decide +kernel

theorem tot15238 : totK PD2M8K2 D2M8K2.t15238 = [0, 0, 86407673651, 349969856144, 376293438224, 73992023780, 1198073392, 0] := by
  decide +kernel

theorem rows15239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15239 = true := by
  decide +kernel

theorem tot15239 : totK PD2M8K2 D2M8K2.t15239 = [0, 0, 0, 271607549510, 504133355035, 105753923391, 4210752944, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
