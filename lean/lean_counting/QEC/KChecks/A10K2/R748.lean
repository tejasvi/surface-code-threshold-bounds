import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2992 = true := by
  decide +kernel

theorem tot2992 : totK PA10K2 A10K2.t2992 = [0, 239802595211, 1024138150070, 1897569862252, 1502359286111, 337521850180, 12681556880, 0, 0, 0] := by
  decide +kernel

theorem rows2993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2993 = true := by
  decide +kernel

theorem tot2993 : totK PA10K2 A10K2.t2993 = [0, 461203280119, 1794729858874, 2045243261824, 621747233166, 41539185317, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2994 = true := by
  decide +kernel

theorem tot2994 : totK PA10K2 A10K2.t2994 = [0, 165731654200, 1113491971307, 2155490921069, 1351432434728, 242447454993, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows2995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2995 = true := by
  decide +kernel

theorem tot2995 : totK PA10K2 A10K2.t2995 = [0, 0, 580129624019, 2051007571925, 1960548548370, 417268923157, 12855574250, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
