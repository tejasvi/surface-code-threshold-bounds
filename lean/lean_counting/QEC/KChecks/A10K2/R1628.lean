import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6512 = true := by
  decide +kernel

theorem tot6512 : totK PA10K2 A10K2.t6512 = [0, 0, 611437368501, 2125456366271, 1953021853690, 388573784885, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows6513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6513 = true := by
  decide +kernel

theorem tot6513 : totK PA10K2 A10K2.t6513 = [0, 0, 510015090104, 1843732670768, 2006507511825, 709282778693, 56417823835, 0, 0, 0] := by
  decide +kernel

theorem rows6514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6514 = true := by
  decide +kernel

theorem tot6514 : totK PA10K2 A10K2.t6514 = [0, 0, 228335335221, 1327054609494, 2239588316157, 1141194483887, 108989541629, 0, 0, 0] := by
  decide +kernel

theorem rows6515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6515 = true := by
  decide +kernel

theorem tot6515 : totK PA10K2 A10K2.t6515 = [0, 0, 539457679089, 1863659880192, 1927099413011, 542772426881, 31947994545, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
