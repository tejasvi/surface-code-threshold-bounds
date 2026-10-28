import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9220 = true := by
  decide +kernel

theorem tot9220 : totK PD2M8K2 D2M8K2.t9220 = [0, 187823866520, 460767934366, 259883587505, 27313105768, 0, 0, 0] := by
  decide +kernel

theorem rows9221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9221 = true := by
  decide +kernel

theorem tot9221 : totK PD2M8K2 D2M8K2.t9221 = [0, 88744179269, 407681137969, 372657867553, 46224507968, 0, 0, 0] := by
  decide +kernel

theorem rows9222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9222 = true := by
  decide +kernel

theorem tot9222 : totK PD2M8K2 D2M8K2.t9222 = [0, 0, 234891108819, 507083679711, 150025000341, 2484078857, 0, 0] := by
  decide +kernel

theorem rows9223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9223 = true := by
  decide +kernel

theorem tot9223 : totK PD2M8K2 D2M8K2.t9223 = [176055752117, 391257976396, 137027730304, 89618055027, 86141447782, 6818291842, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
