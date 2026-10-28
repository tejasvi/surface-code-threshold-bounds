import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3356 = true := by
  decide +kernel

theorem tot3356 : totK PA10K2 A10K2.t3356 = [0, 0, 297280109829, 1076455389810, 1603110363596, 1417132309767, 522441368230, 48886019071, 0, 0] := by
  decide +kernel

theorem rows3357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3357 = true := by
  decide +kernel

theorem tot3357 : totK PA10K2 A10K2.t3357 = [0, 0, 294321102783, 1551975761578, 2294899515271, 879262086094, 71664681669, 0, 0, 0] := by
  decide +kernel

theorem rows3358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3358 = true := by
  decide +kernel

theorem tot3358 : totK PA10K2 A10K2.t3358 = [0, 0, 255765480041, 1194808534642, 2011139789310, 1352759578994, 253293769587, 7903172220, 0, 0] := by
  decide +kernel

theorem rows3359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3359 = true := by
  decide +kernel

theorem tot3359 : totK PA10K2 A10K2.t3359 = [0, 0, 536864502332, 1948345729474, 2068000961396, 611088367889, 32233864571, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
