import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2528 = true := by
  decide +kernel

theorem tot2528 : totK PA10K2 A10K2.t2528 = [0, 163802199591, 992052765258, 1979557223651, 1340781494151, 224841356532, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2529 = true := by
  decide +kernel

theorem tot2529 : totK PA10K2 A10K2.t2529 = [0, 578471078260, 1896309224594, 1764717163208, 498745561447, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2530 = true := by
  decide +kernel

theorem tot2530 : totK PA10K2 A10K2.t2530 = [0, 0, 946531881751, 2400278990171, 1220123502929, 84289812315, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2531 = true := by
  decide +kernel

theorem tot2531 : totK PA10K2 A10K2.t2531 = [0, 469511191713, 1620606455070, 1888838828778, 891566889875, 157064614231, 6239673734, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
