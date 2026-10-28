import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6996 = true := by
  decide +kernel

theorem tot6996 : totK PA10K2 A10K2.t6996 = [0, 0, 0, 787651085249, 2288143021331, 1636854781885, 234082498394, 6725424603, 0, 0] := by
  decide +kernel

theorem rows6997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6997 = true := by
  decide +kernel

theorem tot6997 : totK PA10K2 A10K2.t6997 = [0, 0, 488147704623, 1786550988914, 1915795457124, 666688395175, 65192132021, 0, 0, 0] := by
  decide +kernel

theorem rows6998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6998 = true := by
  decide +kernel

theorem tot6998 : totK PA10K2 A10K2.t6998 = [0, 0, 304353275390, 1457181318014, 2157512635790, 954870985630, 83084434878, 0, 0, 0] := by
  decide +kernel

theorem rows6999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6999 = true := by
  decide +kernel

theorem tot6999 : totK PA10K2 A10K2.t6999 = [0, 0, 62725904439, 585908594886, 1889289156664, 1908980197847, 409245795545, 12692412833, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
