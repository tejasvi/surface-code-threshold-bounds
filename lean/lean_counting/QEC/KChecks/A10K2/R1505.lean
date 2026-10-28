import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6020 = true := by
  decide +kernel

theorem tot6020 : totK PA10K2 A10K2.t6020 = [0, 0, 503825219263, 1834489583187, 1783523876666, 463689112000, 31193230065, 0, 0, 0] := by
  decide +kernel

theorem rows6021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6021 = true := by
  decide +kernel

theorem tot6021 : totK PA10K2 A10K2.t6021 = [0, 0, 697963303377, 2135535261451, 1644275354809, 279637196747, 6354603908, 0, 0, 0] := by
  decide +kernel

theorem rows6022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6022 = true := by
  decide +kernel

theorem tot6022 : totK PA10K2 A10K2.t6022 = [0, 0, 476891020685, 1794607135275, 1885906751728, 498282673434, 31690783744, 0, 0, 0] := by
  decide +kernel

theorem rows6023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6023 = true := by
  decide +kernel

theorem tot6023 : totK PA10K2 A10K2.t6023 = [0, 0, 434628526670, 1673942498625, 1814781996211, 548385780723, 50109395967, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
