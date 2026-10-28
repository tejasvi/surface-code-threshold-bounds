import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t704 = true := by
  decide +kernel

theorem tot704 : totK PA10K2 A10K2.t704 = [0, 0, 426830019438, 1402480709539, 1824446460327, 983696814978, 193814237053, 6354482628, 0, 0] := by
  decide +kernel

theorem rows705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t705 = true := by
  decide +kernel

theorem tot705 : totK PA10K2 A10K2.t705 = [0, 0, 451460131934, 1768279340569, 2017157819455, 605170248231, 33273965371, 0, 0, 0] := by
  decide +kernel

theorem rows706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t706 = true := by
  decide +kernel

theorem tot706 : totK PA10K2 A10K2.t706 = [0, 0, 371573238005, 1720844085497, 2127898898880, 695686649342, 40441619481, 0, 0, 0] := by
  decide +kernel

theorem rows707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t707 = true := by
  decide +kernel

theorem tot707 : totK PA10K2 A10K2.t707 = [0, 0, 0, 502836473669, 1880204372899, 1783135854099, 430217711038, 31017511657, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
