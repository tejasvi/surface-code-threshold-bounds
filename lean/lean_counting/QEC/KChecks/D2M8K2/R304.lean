import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1216 = true := by
  decide +kernel

theorem tot1216 : totK PD2M8K2 D2M8K2.t1216 = [159191398820, 445477703115, 274940231273, 20975033164, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1217 = true := by
  decide +kernel

theorem tot1217 : totK PD2M8K2 D2M8K2.t1217 = [87890102425, 342716604426, 383726692407, 86202244456, 1163840124, 0, 0, 0] := by
  decide +kernel

theorem rows1218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1218 = true := by
  decide +kernel

theorem tot1218 : totK PD2M8K2 D2M8K2.t1218 = [0, 208283107310, 475096137082, 183630823302, 11842047461, 0, 0, 0] := by
  decide +kernel

theorem rows1219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1219 = true := by
  decide +kernel

theorem tot1219 : totK PD2M8K2 D2M8K2.t1219 = [156547374977, 436156605446, 290474707365, 38837158863, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
