import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4984 = true := by
  decide +kernel

theorem tot4984 : totK PA10K2 A10K2.t4984 = [276686981428, 1174485427645, 1896679584827, 1181267684394, 228671755847, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4985 = true := by
  decide +kernel

theorem tot4985 : totK PA10K2 A10K2.t4985 = [184920197622, 1046470155212, 2040972581209, 1431387307295, 259301841465, 6962742351, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4986 = true := by
  decide +kernel

theorem tot4986 : totK PA10K2 A10K2.t4986 = [0, 493865512301, 1748379278978, 1892970228185, 660645857977, 63686582699, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4987 = true := by
  decide +kernel

theorem tot4987 : totK PA10K2 A10K2.t4987 = [0, 490385096477, 1846179752715, 1946188488184, 483363016464, 12917769548, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
