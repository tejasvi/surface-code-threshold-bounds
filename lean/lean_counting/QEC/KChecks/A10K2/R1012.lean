import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4048 = true := by
  decide +kernel

theorem tot4048 : totK PA10K2 A10K2.t4048 = [0, 0, 0, 580077621842, 2016263450400, 1934385057258, 403262400678, 13390658032, 0, 0] := by
  decide +kernel

theorem rows4049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4049 = true := by
  decide +kernel

theorem tot4049 : totK PA10K2 A10K2.t4049 = [0, 0, 0, 0, 887184250557, 2350996958134, 1425717785975, 205403450893, 7007974415, 0] := by
  decide +kernel

theorem rows4050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4050 = true := by
  decide +kernel

theorem tot4050 : totK PA10K2 A10K2.t4050 = [0, 0, 0, 549975075816, 1968419368775, 1866983811277, 465366666970, 31452125142, 0, 0] := by
  decide +kernel

theorem rows4051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4051 = true := by
  decide +kernel

theorem tot4051 : totK PA10K2 A10K2.t4051 = [0, 0, 0, 538792118872, 1975991355479, 2084346764054, 546219970266, 25068640818, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
