import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t484 = true := by
  decide +kernel

theorem tot484 : totK PA10K2 A10K2.t484 = [449613533314, 1797228660332, 2004117516758, 544792985322, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t485 = true := by
  decide +kernel

theorem tot485 : totK PA10K2 A10K2.t485 = [0, 557561718386, 1968429788221, 1763328766777, 421993348059, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t486 = true := by
  decide +kernel

theorem tot486 : totK PA10K2 A10K2.t486 = [581342673799, 1845715056571, 1658535706703, 600632918994, 107173596197, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t487 = true := by
  decide +kernel

theorem tot487 : totK PA10K2 A10K2.t487 = [188585202537, 1270072799217, 2294407380596, 1109198723280, 115055587317, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
