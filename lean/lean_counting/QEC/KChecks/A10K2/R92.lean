import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t368 = true := by
  decide +kernel

theorem tot368 : totK PA10K2 A10K2.t368 = [0, 0, 555160199446, 1946537270606, 1829600776244, 417318318995, 16710973331, 0, 0, 0] := by
  decide +kernel

theorem rows369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t369 = true := by
  decide +kernel

theorem tot369 : totK PA10K2 A10K2.t369 = [0, 0, 520047204997, 1950348043996, 2104782810179, 523590974815, 26788520415, 0, 0, 0] := by
  decide +kernel

theorem rows370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t370 = true := by
  decide +kernel

theorem tot370 : totK PA10K2 A10K2.t370 = [0, 476977255810, 1483193596324, 1568471934394, 1029822034084, 464997883380, 50548650670, 0, 0, 0] := by
  decide +kernel

theorem rows371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t371 = true := by
  decide +kernel

theorem tot371 : totK PA10K2 A10K2.t371 = [0, 116311930094, 985867885406, 2117404821973, 1472054963965, 309149346358, 20340910120, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
