import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6496 = true := by
  decide +kernel

theorem tot6496 : totK PD2M8K2 D2M8K2.t6496 = [0, 177395887876, 467434146377, 240737927359, 14978875236, 0, 0, 0] := by
  decide +kernel

theorem rows6497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6497 = true := by
  decide +kernel

theorem tot6497 : totK PD2M8K2 D2M8K2.t6497 = [0, 80626161392, 398933285445, 389125349056, 45441465878, 0, 0, 0] := by
  decide +kernel

theorem rows6498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6498 = true := by
  decide +kernel

theorem tot6498 : totK PD2M8K2 D2M8K2.t6498 = [0, 0, 218255115807, 501045891126, 159773904478, 5159868635, 0, 0] := by
  decide +kernel

theorem rows6499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6499 = true := by
  decide +kernel

theorem tot6499 : totK PD2M8K2 D2M8K2.t6499 = [0, 198679205628, 447262117732, 237577597841, 28581752801, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
