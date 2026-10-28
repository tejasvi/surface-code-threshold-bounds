import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2612 = true := by
  decide +kernel

theorem tot2612 : totK PA10K2 A10K2.t2612 = [0, 502723522018, 1674643834596, 1788381047966, 853928609495, 173673316812, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2613 = true := by
  decide +kernel

theorem tot2613 : totK PA10K2 A10K2.t2613 = [0, 92465573479, 813532018479, 2166287669009, 1739877323073, 309118266222, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows2614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2614 = true := by
  decide +kernel

theorem tot2614 : totK PA10K2 A10K2.t2614 = [0, 466834568462, 1847675455827, 1866458655307, 452013553510, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2615 = true := by
  decide +kernel

theorem tot2615 : totK PA10K2 A10K2.t2615 = [0, 129948670344, 879237221201, 1860750995898, 1306238861819, 290029106011, 24614390653, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
