import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5004 = true := by
  decide +kernel

theorem tot5004 : totK PA10K2 A10K2.t5004 = [0, 542995954258, 1753572476957, 1848854826944, 578837151118, 37961772096, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5005 = true := by
  decide +kernel

theorem tot5005 : totK PA10K2 A10K2.t5005 = [0, 471953021663, 1894659168276, 1918962806822, 436666649704, 25533540376, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5006 = true := by
  decide +kernel

theorem tot5006 : totK PA10K2 A10K2.t5006 = [0, 0, 875109011166, 2358971481832, 1261256849990, 139157767292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5007 = true := by
  decide +kernel

theorem tot5007 : totK PA10K2 A10K2.t5007 = [0, 541973644762, 1662402196726, 1671117664953, 712799761110, 152301580310, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
