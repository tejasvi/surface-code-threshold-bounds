import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16112 = true := by
  decide +kernel

theorem tot16112 : totK PD2M8K2 D2M8K2.t16112 = [0, 0, 0, 185839267527, 447273553440, 246281980570, 21838679684, 0] := by
  decide +kernel

theorem rows16113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16113 = true := by
  decide +kernel

theorem tot16113 : totK PD2M8K2 D2M8K2.t16113 = [0, 0, 0, 212772209903, 512610741966, 163103417742, 2529670933, 0] := by
  decide +kernel

theorem rows16114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16114 = true := by
  decide +kernel

theorem tot16114 : totK PD2M8K2 D2M8K2.t16114 = [0, 0, 156976588003, 383541906412, 259461152029, 94170212579, 6524090962, 0] := by
  decide +kernel

theorem rows16115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16115 = true := by
  decide +kernel

theorem tot16115 : totK PD2M8K2 D2M8K2.t16115 = [0, 0, 185183687930, 457195299795, 234380926737, 15173876809, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
