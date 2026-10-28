import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t528 = true := by
  decide +kernel

theorem tot528 : totK PA10K2 A10K2.t528 = [336236285345, 1638347282703, 2059092620630, 694929697613, 53383856823, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t529 = true := by
  decide +kernel

theorem tot529 : totK PA10K2 A10K2.t529 = [111822410833, 830826819416, 2044716861156, 1468597904085, 248656676753, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t530 = true := by
  decide +kernel

theorem tot530 : totK PA10K2 A10K2.t530 = [388272196882, 1720662175613, 2145809392427, 775810105286, 69511155409, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t531 = true := by
  decide +kernel

theorem tot531 : totK PA10K2 A10K2.t531 = [0, 503715355508, 1892497025301, 2036398599514, 620224693845, 49519616328, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
