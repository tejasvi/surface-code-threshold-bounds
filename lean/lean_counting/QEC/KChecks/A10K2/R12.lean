import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows48 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t48 = true := by
  decide +kernel

theorem tot48 : totK PA10K2 A10K2.t48 = [0, 280432172224, 1507135184060, 2080249811167, 699137287195, 39027466557, 0, 0, 0, 0] := by
  decide +kernel

theorem rows49 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t49 = true := by
  decide +kernel

theorem tot49 : totK PA10K2 A10K2.t49 = [0, 298377533599, 1149718226107, 1800529102412, 1137752902100, 173030684247, 5705019915, 0, 0, 0] := by
  decide +kernel

theorem rows50 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t50 = true := by
  decide +kernel

theorem tot50 : totK PA10K2 A10K2.t50 = [0, 484635519347, 1886681533422, 2104716570743, 579594727178, 31343198550, 0, 0, 0, 0] := by
  decide +kernel

theorem rows51 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t51 = true := by
  decide +kernel

theorem tot51 : totK PA10K2 A10K2.t51 = [0, 0, 726081406429, 2238482072871, 1750792162586, 296730155703, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
