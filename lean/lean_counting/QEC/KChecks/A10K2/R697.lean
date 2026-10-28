import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2788 = true := by
  decide +kernel

theorem tot2788 : totK PA10K2 A10K2.t2788 = [0, 476398299135, 1815711045591, 2050983190899, 626326714032, 25138202768, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2789 = true := by
  decide +kernel

theorem tot2789 : totK PA10K2 A10K2.t2789 = [0, 0, 602526901405, 2033989294480, 1911425270717, 379157893966, 12224107035, 0, 0, 0] := by
  decide +kernel

theorem rows2790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2790 = true := by
  decide +kernel

theorem tot2790 : totK PA10K2 A10K2.t2790 = [0, 210107306607, 875993101026, 1618007279421, 1595947401857, 565505712757, 48886019071, 0, 0, 0] := by
  decide +kernel

theorem rows2791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2791 = true := by
  decide +kernel

theorem tot2791 : totK PA10K2 A10K2.t2791 = [0, 491312015816, 1799369906885, 1957498447277, 542004127655, 31923522143, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
