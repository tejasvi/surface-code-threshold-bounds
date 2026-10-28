import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t344 = true := by
  decide +kernel

theorem tot344 : totK PA10K2 A10K2.t344 = [0, 0, 400187323937, 1365612458422, 1779812334990, 975353703033, 177535652379, 6354482628, 0, 0] := by
  decide +kernel

theorem rows345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t345 = true := by
  decide +kernel

theorem tot345 : totK PA10K2 A10K2.t345 = [0, 0, 362738961526, 1688477309510, 2059196812904, 660606125242, 39557919322, 0, 0, 0] := by
  decide +kernel

theorem rows346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t346 = true := by
  decide +kernel

theorem tot346 : totK PA10K2 A10K2.t346 = [0, 0, 0, 467532551006, 1875648391752, 1760135634970, 420976269294, 30074883546, 0, 0] := by
  decide +kernel

theorem rows347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t347 = true := by
  decide +kernel

theorem tot347 : totK PA10K2 A10K2.t347 = [0, 0, 518457632552, 1839995887262, 1824988958609, 507739786070, 32838645320, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
