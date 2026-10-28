import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12096 = true := by
  decide +kernel

theorem tot12096 : totK PD2M8K2 D2M8K2.t12096 = [0, 0, 207273939266, 470149184845, 191250002954, 12052611869, 0, 0] := by
  decide +kernel

theorem rows12097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12097 = true := by
  decide +kernel

theorem tot12097 : totK PD2M8K2 D2M8K2.t12097 = [0, 171277143297, 439279832599, 262003362710, 27905992105, 0, 0, 0] := by
  decide +kernel

theorem rows12098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12098 = true := by
  decide +kernel

theorem tot12098 : totK PD2M8K2 D2M8K2.t12098 = [0, 209753251597, 472121754956, 207764748485, 12178391273, 0, 0, 0] := by
  decide +kernel

theorem rows12099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12099 = true := by
  decide +kernel

theorem tot12099 : totK PD2M8K2 D2M8K2.t12099 = [0, 37670822061, 332161484451, 431850378129, 76486373080, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
