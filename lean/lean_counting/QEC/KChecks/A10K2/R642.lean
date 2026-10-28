import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2568 = true := by
  decide +kernel

theorem tot2568 : totK PA10K2 A10K2.t2568 = [0, 278009351286, 1194028976188, 1875020792746, 1109713891040, 190598885651, 5410721913, 0, 0, 0] := by
  decide +kernel

theorem rows2569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2569 = true := by
  decide +kernel

theorem tot2569 : totK PA10K2 A10K2.t2569 = [0, 500401232296, 1856720542703, 1903780118582, 496807275401, 31608797364, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2570 = true := by
  decide +kernel

theorem tot2570 : totK PA10K2 A10K2.t2570 = [0, 0, 888882697180, 2395732563668, 1259880920284, 104495421231, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2571 = true := by
  decide +kernel

theorem tot2571 : totK PA10K2 A10K2.t2571 = [311769148082, 1172192212502, 1595384177339, 1121065804720, 491523163108, 114682951011, 5546304973, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
