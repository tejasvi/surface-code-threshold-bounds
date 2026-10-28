import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t204 = true := by
  decide +kernel

theorem tot204 : totK PD2M8K2 D2M8K2.t204 = [0, 0, 205462671646, 471908558611, 186140703501, 12242580035, 0, 0] := by
  decide +kernel

theorem rows205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t205 = true := by
  decide +kernel

theorem tot205 : totK PD2M8K2 D2M8K2.t205 = [0, 0, 204880754009, 498636994579, 176208272931, 5232301710, 0, 0] := by
  decide +kernel

theorem rows206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t206 = true := by
  decide +kernel

theorem tot206 : totK PD2M8K2 D2M8K2.t206 = [0, 72313472087, 221281159325, 372048790440, 198940682090, 17192599809, 0, 0] := by
  decide +kernel

theorem rows207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t207 = true := by
  decide +kernel

theorem tot207 : totK PD2M8K2 D2M8K2.t207 = [0, 177505864616, 484065781090, 226978607611, 11038245751, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
