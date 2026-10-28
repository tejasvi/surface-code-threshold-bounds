import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2880 = true := by
  decide +kernel

theorem tot2880 : totK PA10K2 A10K2.t2880 = [0, 198509887261, 1079630690337, 1992815690960, 1382951424118, 269941947000, 7007974415, 0, 0, 0] := by
  decide +kernel

theorem rows2881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2881 = true := by
  decide +kernel

theorem tot2881 : totK PA10K2 A10K2.t2881 = [0, 559974949842, 1898526851787, 1939850298727, 545684918143, 31908368213, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2882 = true := by
  decide +kernel

theorem tot2882 : totK PA10K2 A10K2.t2882 = [0, 45277493360, 829275226489, 2102235072096, 1587613862188, 368449325583, 25660650750, 0, 0, 0] := by
  decide +kernel

theorem rows2883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2883 = true := by
  decide +kernel

theorem tot2883 : totK PA10K2 A10K2.t2883 = [0, 246819733237, 1172024403292, 1971277388405, 1340415932904, 232648401641, 5624717336, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
