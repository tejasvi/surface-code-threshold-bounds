import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2056 = true := by
  decide +kernel

theorem tot2056 : totK PA10K2 A10K2.t2056 = [0, 518220392115, 1766697744422, 1841240268710, 516867323511, 31607162994, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2057 = true := by
  decide +kernel

theorem tot2057 : totK PA10K2 A10K2.t2057 = [0, 403013071498, 1774077973548, 1978586236341, 523476248229, 31889781550, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2058 = true := by
  decide +kernel

theorem tot2058 : totK PA10K2 A10K2.t2058 = [0, 0, 705265633904, 2101620157918, 1438705836435, 237887323504, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2059 = true := by
  decide +kernel

theorem tot2059 : totK PA10K2 A10K2.t2059 = [476537513919, 1782589394850, 2039275452443, 750994677403, 65829077015, 12598862489, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
