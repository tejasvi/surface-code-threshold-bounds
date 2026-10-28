import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3644 = true := by
  decide +kernel

theorem tot3644 : totK PA10K2 A10K2.t3644 = [0, 0, 0, 690015232084, 2249912743262, 1860811904753, 309731473338, 6157148557, 0, 0] := by
  decide +kernel

theorem rows3645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3645 = true := by
  decide +kernel

theorem tot3645 : totK PA10K2 A10K2.t3645 = [0, 0, 319639362920, 1147932539222, 1664032968316, 1325804459123, 467718475306, 35764095907, 0, 0] := by
  decide +kernel

theorem rows3646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3646 = true := by
  decide +kernel

theorem tot3646 : totK PA10K2 A10K2.t3646 = [0, 0, 538071541683, 1965852987926, 1950425353468, 440939396334, 12129354050, 0, 0, 0] := by
  decide +kernel

theorem rows3647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3647 = true := by
  decide +kernel

theorem tot3647 : totK PA10K2 A10K2.t3647 = [0, 0, 0, 628277044896, 1982671326969, 1737531941465, 416799787764, 25734533292, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
