import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11712 = true := by
  decide +kernel

theorem tot11712 : totK PD2M8K2 D2M8K2.t11712 = [173197134760, 450951800193, 262162069792, 34867437265, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11713 = true := by
  decide +kernel

theorem tot11713 : totK PD2M8K2 D2M8K2.t11713 = [161414725583, 446610578664, 281404836948, 20585454062, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11714 = true := by
  decide +kernel

theorem tot11714 : totK PD2M8K2 D2M8K2.t11714 = [93371872402, 349491620190, 375309670529, 76726068474, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows11715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11715 = true := by
  decide +kernel

theorem tot11715 : totK PD2M8K2 D2M8K2.t11715 = [0, 248471963636, 498614883698, 152312238655, 3699256714, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
