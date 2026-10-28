import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10700 = true := by
  decide +kernel

theorem tot10700 : totK PD2M8K2 D2M8K2.t10700 = [0, 0, 159023080014, 407764133175, 272767140277, 58152041564, 2566665356, 0] := by
  decide +kernel

theorem rows10701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10701 = true := by
  decide +kernel

theorem tot10701 : totK PD2M8K2 D2M8K2.t10701 = [0, 0, 169572312022, 436645201090, 265880384416, 27219231910, 0, 0] := by
  decide +kernel

theorem rows10702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10702 = true := by
  decide +kernel

theorem tot10702 : totK PD2M8K2 D2M8K2.t10702 = [0, 0, 91681601894, 417529803179, 348038566237, 37899557665, 0, 0] := by
  decide +kernel

theorem rows10703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10703 = true := by
  decide +kernel

theorem tot10703 : totK PD2M8K2 D2M8K2.t10703 = [0, 0, 0, 296026633314, 523842075073, 89100358689, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
