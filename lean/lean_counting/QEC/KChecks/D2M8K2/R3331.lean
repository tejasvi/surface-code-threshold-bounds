import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13324 = true := by
  decide +kernel

theorem tot13324 : totK PD2M8K2 D2M8K2.t13324 = [0, 158642196989, 450557903783, 290174531739, 24708820017, 0, 0, 0] := by
  decide +kernel

theorem rows13325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13325 = true := by
  decide +kernel

theorem tot13325 : totK PD2M8K2 D2M8K2.t13325 = [0, 166376668056, 457154081425, 256940107670, 17908694102, 0, 0, 0] := by
  decide +kernel

theorem rows13326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13326 = true := by
  decide +kernel

theorem tot13326 : totK PD2M8K2 D2M8K2.t13326 = [0, 0, 187478280131, 441458155895, 253758800199, 25123215704, 0, 0] := by
  decide +kernel

theorem rows13327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13327 = true := by
  decide +kernel

theorem tot13327 : totK PD2M8K2 D2M8K2.t13327 = [0, 0, 203270896157, 495955837989, 198127786252, 5430665091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
