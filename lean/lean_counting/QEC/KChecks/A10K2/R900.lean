import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3600 = true := by
  decide +kernel

theorem tot3600 : totK PA10K2 A10K2.t3600 = [0, 0, 0, 674667607013, 2133121447146, 1506029516828, 255244581706, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3601 = true := by
  decide +kernel

theorem tot3601 : totK PA10K2 A10K2.t3601 = [0, 0, 0, 466734127680, 1769414068117, 1904422656522, 470240889467, 31756067336, 0, 0] := by
  decide +kernel

theorem rows3602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3602 = true := by
  decide +kernel

theorem tot3602 : totK PA10K2 A10K2.t3602 = [0, 0, 0, 744034808311, 2190574560634, 1590050532638, 251888159106, 6239800209, 0, 0] := by
  decide +kernel

theorem rows3603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3603 = true := by
  decide +kernel

theorem tot3603 : totK PA10K2 A10K2.t3603 = [0, 0, 0, 560384022981, 1878877209231, 1742356355761, 434962847367, 30637645759, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
