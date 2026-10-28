import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5884 = true := by
  decide +kernel

theorem tot5884 : totK PA10K2 A10K2.t5884 = [0, 0, 0, 480359639732, 1706988329012, 1707734675472, 673536917158, 128362953560, 5718040558, 0] := by
  decide +kernel

theorem rows5885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5885 = true := by
  decide +kernel

theorem tot5885 : totK PA10K2 A10K2.t5885 = [0, 0, 0, 295075171265, 1484751455319, 2134994796370, 761103642324, 52620953014, 0, 0] := by
  decide +kernel

theorem rows5886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5886 = true := by
  decide +kernel

theorem tot5886 : totK PA10K2 A10K2.t5886 = [0, 0, 0, 160200231689, 942870845376, 1992984040497, 1322768395743, 248025820968, 6354482628, 0] := by
  decide +kernel

theorem rows5887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5887 = true := by
  decide +kernel

theorem tot5887 : totK PA10K2 A10K2.t5887 = [0, 0, 0, 587450602647, 2028396436630, 1787090193677, 398139003085, 40740278131, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
