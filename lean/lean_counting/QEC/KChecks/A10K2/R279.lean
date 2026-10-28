import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1116 = true := by
  decide +kernel

theorem tot1116 : totK PA10K2 A10K2.t1116 = [0, 0, 110544802144, 716256303635, 1888164227749, 1785334172819, 403136118530, 12696458652, 0, 0] := by
  decide +kernel

theorem rows1117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1117 = true := by
  decide +kernel

theorem tot1117 : totK PA10K2 A10K2.t1117 = [0, 0, 372082193666, 1621875230201, 2111835261014, 807207260908, 59830859967, 0, 0, 0] := by
  decide +kernel

theorem rows1118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1118 = true := by
  decide +kernel

theorem tot1118 : totK PA10K2 A10K2.t1118 = [0, 0, 609252834019, 1925049553201, 1872669625878, 542568011619, 29367733220, 0, 0, 0] := by
  decide +kernel

theorem rows1119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1119 = true := by
  decide +kernel

theorem tot1119 : totK PA10K2 A10K2.t1119 = [0, 0, 0, 844853642056, 2306917334238, 1619016499463, 263194420950, 6279851884, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
