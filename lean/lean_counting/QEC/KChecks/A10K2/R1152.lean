import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4608 = true := by
  decide +kernel

theorem tot4608 : totK PA10K2 A10K2.t4608 = [593238721492, 1950411061974, 1789185236417, 517995590555, 198447025619, 37674658091, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4609 = true := by
  decide +kernel

theorem tot4609 : totK PA10K2 A10K2.t4609 = [0, 700628706359, 2195332403759, 1723191636730, 375435365881, 25221471178, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4610 = true := by
  decide +kernel

theorem tot4610 : totK PA10K2 A10K2.t4610 = [477476970137, 1741196599672, 1918949706922, 724114066485, 72111853140, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4611 = true := by
  decide +kernel

theorem tot4611 : totK PA10K2 A10K2.t4611 = [306418931549, 1475664715830, 2179385596362, 953278351516, 84654811513, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
