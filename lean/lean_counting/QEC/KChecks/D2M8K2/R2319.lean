import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9276 = true := by
  decide +kernel

theorem tot9276 : totK PD2M8K2 D2M8K2.t9276 = [0, 129027011912, 405826579304, 344296735694, 39835946982, 0, 0, 0] := by
  decide +kernel

theorem rows9277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9277 = true := by
  decide +kernel

theorem tot9277 : totK PD2M8K2 D2M8K2.t9277 = [0, 206979220587, 472675360123, 217100964240, 12599632882, 0, 0, 0] := by
  decide +kernel

theorem rows9278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9278 = true := by
  decide +kernel

theorem tot9278 : totK PD2M8K2 D2M8K2.t9278 = [0, 166555199266, 475145060564, 241200627379, 15480724951, 0, 0, 0] := by
  decide +kernel

theorem rows9279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9279 = true := by
  decide +kernel

theorem tot9279 : totK PD2M8K2 D2M8K2.t9279 = [0, 181844105063, 470173802132, 252341717748, 19757109210, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
