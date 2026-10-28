import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7656 = true := by
  decide +kernel

theorem tot7656 : totK PA10K2 A10K2.t7656 = [0, 0, 0, 471213704242, 1781831947867, 1973261231192, 529174245982, 32470938769, 0, 0] := by
  decide +kernel

theorem rows7657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7657 = true := by
  decide +kernel

theorem tot7657 : totK PA10K2 A10K2.t7657 = [0, 0, 0, 496526282785, 1952458061425, 1987218028625, 427602665399, 13227942247, 0, 0] := by
  decide +kernel

theorem rows7658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7658 = true := by
  decide +kernel

theorem tot7658 : totK PA10K2 A10K2.t7658 = [0, 0, 0, 568013831436, 1885870410144, 1772998225417, 433815126558, 30953568651, 0, 0] := by
  decide +kernel

theorem rows7659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7659 = true := by
  decide +kernel

theorem tot7659 : totK PA10K2 A10K2.t7659 = [0, 0, 0, 0, 944105854278, 2402581065487, 1122269070134, 98268089773, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
