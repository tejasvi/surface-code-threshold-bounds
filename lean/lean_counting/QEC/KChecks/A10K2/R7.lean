import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows28 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t28 = true := by
  decide +kernel

theorem tot28 : totK PA10K2 A10K2.t28 = [310758541238, 1105552092390, 1304568198739, 1062195082773, 763260724796, 187952782646, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows29 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t29 = true := by
  decide +kernel

theorem tot29 : totK PA10K2 A10K2.t29 = [503854197128, 1873967463890, 2024885531236, 577131434531, 19444713158, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows30 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t30 = true := by
  decide +kernel

theorem tot30 : totK PA10K2 A10K2.t30 = [0, 511454590885, 1945531928201, 1912396588266, 452363225090, 25351274858, 0, 0, 0, 0] := by
  decide +kernel

theorem rows31 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t31 = true := by
  decide +kernel

theorem tot31 : totK PA10K2 A10K2.t31 = [477482834340, 1717061273790, 1945552512545, 822936587096, 133644772376, 5459593153, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
