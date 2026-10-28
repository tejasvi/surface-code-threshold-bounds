import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1144 = true := by
  decide +kernel

theorem tot1144 : totK PA10K2 A10K2.t1144 = [0, 0, 657985863166, 2052395632035, 1695011751587, 396847619951, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows1145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1145 = true := by
  decide +kernel

theorem tot1145 : totK PA10K2 A10K2.t1145 = [0, 293873915135, 1259961492961, 1901402335738, 1180612313741, 199480265253, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows1146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1146 = true := by
  decide +kernel

theorem tot1146 : totK PA10K2 A10K2.t1146 = [0, 428173033222, 1638033901562, 1858903690062, 592085750699, 42503166815, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1147 = true := by
  decide +kernel

theorem tot1147 : totK PA10K2 A10K2.t1147 = [0, 0, 832378004376, 2301510437353, 1340661379022, 121621384588, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
