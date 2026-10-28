import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10824 = true := by
  decide +kernel

theorem tot10824 : totK PD2M8K2 D2M8K2.t10824 = [0, 0, 142123624119, 359889106031, 292922662136, 108838082638, 6524090962, 0] := by
  decide +kernel

theorem rows10825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10825 = true := by
  decide +kernel

theorem tot10825 : totK PD2M8K2 D2M8K2.t10825 = [0, 0, 171094482944, 459616274386, 255217816314, 17117448544, 0, 0] := by
  decide +kernel

theorem rows10826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10826 = true := by
  decide +kernel

theorem tot10826 : totK PD2M8K2 D2M8K2.t10826 = [0, 0, 71432936211, 396496245261, 398650772493, 48676623103, 0, 0] := by
  decide +kernel

theorem rows10827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10827 = true := by
  decide +kernel

theorem tot10827 : totK PD2M8K2 D2M8K2.t10827 = [0, 0, 67714192740, 337404226918, 405208527748, 83413132176, 1547833102, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
