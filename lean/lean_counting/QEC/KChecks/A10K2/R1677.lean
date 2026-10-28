import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6708 = true := by
  decide +kernel

theorem tot6708 : totK PA10K2 A10K2.t6708 = [0, 307030755596, 1482872073353, 2188829850962, 967294317397, 91367724007, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6709 = true := by
  decide +kernel

theorem tot6709 : totK PA10K2 A10K2.t6709 = [0, 286185292359, 1167888539843, 1939080667327, 1400521066251, 254982293620, 7151180950, 0, 0, 0] := by
  decide +kernel

theorem rows6710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6710 = true := by
  decide +kernel

theorem tot6710 : totK PA10K2 A10K2.t6710 = [0, 459953784416, 1798681856227, 2070772475984, 615206009826, 32045019311, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6711 = true := by
  decide +kernel

theorem tot6711 : totK PA10K2 A10K2.t6711 = [0, 122355545644, 983846357315, 2161697058727, 1496261980591, 262347487989, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
