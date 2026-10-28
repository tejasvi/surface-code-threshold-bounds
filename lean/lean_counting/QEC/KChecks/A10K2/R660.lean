import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2640 = true := by
  decide +kernel

theorem tot2640 : totK PA10K2 A10K2.t2640 = [0, 0, 0, 772865630313, 2248713617770, 1395192737922, 152501968625, 0, 0, 0] := by
  decide +kernel

theorem rows2641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2641 = true := by
  decide +kernel

theorem tot2641 : totK PA10K2 A10K2.t2641 = [0, 0, 591060099811, 1994082440178, 1908284897374, 496562321372, 73366485347, 5546304973, 0, 0] := by
  decide +kernel

theorem rows2642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2642 = true := by
  decide +kernel

theorem tot2642 : totK PA10K2 A10K2.t2642 = [0, 522945393773, 1615290856499, 1665299567737, 817181063868, 243611548275, 23009379923, 0, 0, 0] := by
  decide +kernel

theorem rows2643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2643 = true := by
  decide +kernel

theorem tot2643 : totK PA10K2 A10K2.t2643 = [0, 244118591212, 1468436439829, 2234477234270, 872526514576, 67691055152, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
