import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5312 = true := by
  decide +kernel

theorem tot5312 : totK PA10K2 A10K2.t5312 = [0, 0, 0, 711015671873, 2139694633372, 1515415721164, 262515286030, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5313 = true := by
  decide +kernel

theorem tot5313 : totK PA10K2 A10K2.t5313 = [0, 0, 0, 463071292111, 1834295551088, 1883672071495, 423180425487, 24838747437, 0, 0] := by
  decide +kernel

theorem rows5314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5314 = true := by
  decide +kernel

theorem tot5314 : totK PA10K2 A10K2.t5314 = [0, 0, 0, 685769676790, 1990560371428, 1603886192508, 405038692714, 31690778550, 0, 0] := by
  decide +kernel

theorem rows5315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5315 = true := by
  decide +kernel

theorem tot5315 : totK PA10K2 A10K2.t5315 = [0, 0, 0, 505436215817, 1856544630815, 1753935689653, 461253332345, 31009878902, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
