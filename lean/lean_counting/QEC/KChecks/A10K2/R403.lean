import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1612 = true := by
  decide +kernel

theorem tot1612 : totK PA10K2 A10K2.t1612 = [0, 0, 708518935375, 2163812634315, 1568268199440, 255466006805, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows1613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1613 = true := by
  decide +kernel

theorem tot1613 : totK PA10K2 A10K2.t1613 = [0, 0, 493806144994, 1915140201873, 1901877880714, 421593860218, 25633273041, 0, 0, 0] := by
  decide +kernel

theorem rows1614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1614 = true := by
  decide +kernel

theorem tot1614 : totK PA10K2 A10K2.t1614 = [0, 0, 581142082838, 1894664836563, 1804817797071, 505281154317, 32470938769, 0, 0, 0] := by
  decide +kernel

theorem rows1615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1615 = true := by
  decide +kernel

theorem tot1615 : totK PA10K2 A10K2.t1615 = [0, 0, 425425093243, 1737195773308, 2018857491805, 571725311100, 32541743821, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
