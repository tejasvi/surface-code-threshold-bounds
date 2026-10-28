import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4880 = true := by
  decide +kernel

theorem tot4880 : totK PA10K2 A10K2.t4880 = [0, 0, 927301159451, 2333166435636, 1300882130425, 125687312187, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4881 = true := by
  decide +kernel

theorem tot4881 : totK PA10K2 A10K2.t4881 = [0, 515753070049, 1738887952690, 1714150843546, 621223627738, 122625592826, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows4882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4882 = true := by
  decide +kernel

theorem tot4882 : totK PA10K2 A10K2.t4882 = [0, 303792748393, 1513396032496, 2117489857868, 759142465952, 44556629621, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4883 = true := by
  decide +kernel

theorem tot4883 : totK PA10K2 A10K2.t4883 = [0, 0, 713708935956, 2105945260231, 1519271814077, 262013702951, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
