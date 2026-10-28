import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3096 = true := by
  decide +kernel

theorem tot3096 : totK PD2M8K2 D2M8K2.t3096 = [0, 93763323609, 394469064050, 369983989940, 50279576687, 1268739303, 0, 0] := by
  decide +kernel

theorem rows3097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3097 = true := by
  decide +kernel

theorem tot3097 : totK PD2M8K2 D2M8K2.t3097 = [0, 0, 230739800629, 492192866396, 161886781889, 3699256714, 0, 0] := by
  decide +kernel

theorem rows3098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3098 = true := by
  decide +kernel

theorem tot3098 : totK PD2M8K2 D2M8K2.t3098 = [72746125013, 94501798518, 133403720502, 364566008456, 202927325469, 17014456371, 0, 0] := by
  decide +kernel

theorem rows3099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3099 = true := by
  decide +kernel

theorem tot3099 : totK PD2M8K2 D2M8K2.t3099 = [178125618527, 481248466907, 226293561583, 11038245751, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
