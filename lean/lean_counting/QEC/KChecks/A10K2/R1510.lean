import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6040 = true := by
  decide +kernel

theorem tot6040 : totK PA10K2 A10K2.t6040 = [482764488651, 1729644223469, 1764926407150, 696882004052, 247903446001, 37674914273, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6041 = true := by
  decide +kernel

theorem tot6041 : totK PA10K2 A10K2.t6041 = [297062822345, 1436489451355, 2213667431159, 1063345493672, 91439202099, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6042 = true := by
  decide +kernel

theorem tot6042 : totK PA10K2 A10K2.t6042 = [105088995274, 650223811584, 1813793513072, 1858936318454, 517483594139, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6043 = true := by
  decide +kernel

theorem tot6043 : totK PA10K2 A10K2.t6043 = [494504235023, 1879938163372, 2097403060379, 622048663891, 44425445893, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
