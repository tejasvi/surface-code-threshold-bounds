import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7580 = true := by
  decide +kernel

theorem tot7580 : totK PA10K2 A10K2.t7580 = [0, 478711658477, 1851979549020, 2040522143795, 609064150982, 25753937681, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7581 = true := by
  decide +kernel

theorem tot7581 : totK PA10K2 A10K2.t7581 = [0, 0, 489023334810, 1889327870148, 1923536227168, 475385356319, 25654631657, 0, 0, 0] := by
  decide +kernel

theorem rows7582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7582 = true := by
  decide +kernel

theorem tot7582 : totK PA10K2 A10K2.t7582 = [0, 378303412531, 1556097204504, 2040024798349, 877804814523, 124642504486, 6022596713, 0, 0, 0] := by
  decide +kernel

theorem rows7583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7583 = true := by
  decide +kernel

theorem tot7583 : totK PA10K2 A10K2.t7583 = [0, 504843445940, 1861726042599, 2054608816162, 619420482270, 31461578691, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
