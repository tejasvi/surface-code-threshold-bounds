import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2420 = true := by
  decide +kernel

theorem tot2420 : totK PA10K2 A10K2.t2420 = [0, 330865856800, 1518376645272, 2173612077485, 899509587026, 67259432327, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2421 = true := by
  decide +kernel

theorem tot2421 : totK PA10K2 A10K2.t2421 = [0, 0, 528392707587, 1947421166938, 2039764272348, 467185742475, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows2422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2422 = true := by
  decide +kernel

theorem tot2422 : totK PA10K2 A10K2.t2422 = [0, 0, 405468558774, 1640824666015, 2097845368846, 797221519368, 61665590386, 0, 0, 0] := by
  decide +kernel

theorem rows2423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2423 = true := by
  decide +kernel

theorem tot2423 : totK PA10K2 A10K2.t2423 = [0, 0, 303295676507, 1517646090936, 2192000978862, 936833541714, 69914746219, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
