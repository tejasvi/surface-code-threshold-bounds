import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4860 = true := by
  decide +kernel

theorem tot4860 : totK PA10K2 A10K2.t4860 = [0, 120338364144, 1009158243494, 2157994902560, 1504464941231, 229679543799, 6066958478, 0, 0, 0] := by
  decide +kernel

theorem rows4861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4861 = true := by
  decide +kernel

theorem tot4861 : totK PA10K2 A10K2.t4861 = [0, 318420800840, 1149054954514, 1591686433533, 1335886777701, 535253605869, 48886019071, 0, 0, 0] := by
  decide +kernel

theorem rows4862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4862 = true := by
  decide +kernel

theorem tot4862 : totK PA10K2 A10K2.t4862 = [0, 479872810023, 1761941204199, 1917797587888, 541867538469, 31923522143, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4863 = true := by
  decide +kernel

theorem tot4863 : totK PA10K2 A10K2.t4863 = [0, 44706116827, 776277791913, 2019236257698, 1530385361516, 356957802062, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
