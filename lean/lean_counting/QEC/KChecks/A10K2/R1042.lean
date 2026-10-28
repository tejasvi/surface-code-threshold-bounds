import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4168 = true := by
  decide +kernel

theorem tot4168 : totK PA10K2 A10K2.t4168 = [0, 0, 689572522551, 2045951044888, 1617120544828, 379860345113, 25239774317, 0, 0, 0] := by
  decide +kernel

theorem rows4169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4169 = true := by
  decide +kernel

theorem tot4169 : totK PA10K2 A10K2.t4169 = [0, 287912073481, 1266717421764, 1880483790675, 1041281647503, 169942575727, 5410721913, 0, 0, 0] := by
  decide +kernel

theorem rows4170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4170 = true := by
  decide +kernel

theorem tot4170 : totK PA10K2 A10K2.t4170 = [0, 480572733570, 1794493366593, 1924026943786, 531512573795, 31608797364, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4171 = true := by
  decide +kernel

theorem tot4171 : totK PA10K2 A10K2.t4171 = [0, 0, 867429569502, 2376252038389, 1282720820039, 118453847392, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
