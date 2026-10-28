import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3020 = true := by
  decide +kernel

theorem tot3020 : totK PA10K2 A10K2.t3020 = [0, 0, 594293228886, 1961056153398, 1873427194480, 614954305602, 51705825147, 0, 0, 0] := by
  decide +kernel

theorem rows3021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3021 = true := by
  decide +kernel

theorem tot3021 : totK PA10K2 A10K2.t3021 = [0, 0, 0, 809590685600, 2312767145573, 1652638191420, 241799411125, 6860445330, 0, 0] := by
  decide +kernel

theorem rows3022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3022 = true := by
  decide +kernel

theorem tot3022 : totK PA10K2 A10K2.t3022 = [0, 0, 539000210498, 1859860241187, 1904312020725, 618711806946, 56285200856, 0, 0, 0] := by
  decide +kernel

theorem rows3023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3023 = true := by
  decide +kernel

theorem tot3023 : totK PA10K2 A10K2.t3023 = [0, 0, 327737319032, 1477349091867, 2129317299113, 933267283740, 80601344643, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
