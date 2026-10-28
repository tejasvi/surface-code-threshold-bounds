import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6376 = true := by
  decide +kernel

theorem tot6376 : totK PA10K2 A10K2.t6376 = [0, 362601568456, 1605228682021, 2096293004706, 774010204148, 57425167665, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6377 = true := by
  decide +kernel

theorem tot6377 : totK PA10K2 A10K2.t6377 = [0, 0, 464767173811, 1826376312755, 1894858927023, 479647866778, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows6378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6378 = true := by
  decide +kernel

theorem tot6378 : totK PA10K2 A10K2.t6378 = [0, 461452330429, 1658151481429, 1854404328319, 752971178665, 74655188303, 5718040558, 0, 0, 0] := by
  decide +kernel

theorem rows6379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6379 = true := by
  decide +kernel

theorem tot6379 : totK PA10K2 A10K2.t6379 = [0, 289345254879, 1492230655405, 2121821699722, 754631838075, 52620953014, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
