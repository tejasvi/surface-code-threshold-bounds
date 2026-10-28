import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1980 = true := by
  decide +kernel

theorem tot1980 : totK PA10K2 A10K2.t1980 = [0, 0, 523359894886, 1855919544428, 1951516332936, 606408106143, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows1981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1981 = true := by
  decide +kernel

theorem tot1981 : totK PA10K2 A10K2.t1981 = [0, 0, 468370069426, 1786892929895, 2018445105483, 603903605970, 32077220640, 0, 0, 0] := by
  decide +kernel

theorem rows1982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1982 = true := by
  decide +kernel

theorem tot1982 : totK PA10K2 A10K2.t1982 = [0, 0, 0, 680693610723, 2196571633977, 1639790437998, 283955631850, 6904928264, 0, 0] := by
  decide +kernel

theorem rows1983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1983 = true := by
  decide +kernel

theorem tot1983 : totK PA10K2 A10K2.t1983 = [0, 0, 420068636232, 1642090576227, 1922998322809, 741656263683, 63520814907, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
