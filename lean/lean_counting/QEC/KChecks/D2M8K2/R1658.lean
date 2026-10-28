import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6632 = true := by
  decide +kernel

theorem tot6632 : totK PD2M8K2 D2M8K2.t6632 = [0, 0, 244386892662, 485806027114, 154012268818, 8391427444, 0, 0] := by
  decide +kernel

theorem rows6633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6633 = true := by
  decide +kernel

theorem tot6633 : totK PD2M8K2 D2M8K2.t6633 = [0, 0, 226804632233, 478463107452, 167559052123, 5155287779, 0, 0] := by
  decide +kernel

theorem rows6634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6634 = true := by
  decide +kernel

theorem tot6634 : totK PD2M8K2 D2M8K2.t6634 = [0, 0, 197116084164, 458479394295, 196823271676, 12253340667, 0, 0] := by
  decide +kernel

theorem rows6635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6635 = true := by
  decide +kernel

theorem tot6635 : totK PD2M8K2 D2M8K2.t6635 = [0, 0, 218757223566, 496328586648, 164200386716, 2772616150, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
