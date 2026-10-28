import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4752 = true := by
  decide +kernel

theorem tot4752 : totK PA10K2 A10K2.t4752 = [0, 0, 480045639941, 1837390201866, 2021228888280, 610920749358, 32712955001, 0, 0, 0] := by
  decide +kernel

theorem rows4753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4753 = true := by
  decide +kernel

theorem tot4753 : totK PA10K2 A10K2.t4753 = [0, 557742759892, 1744779752603, 1585007760920, 650429852357, 240045928549, 28907544418, 0, 0, 0] := by
  decide +kernel

theorem rows4754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4754 = true := by
  decide +kernel

theorem tot4754 : totK PA10K2 A10K2.t4754 = [0, 93946978215, 972000907068, 2075716458589, 1313457326852, 286417265543, 24941563133, 0, 0, 0] := by
  decide +kernel

theorem rows4755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4755 = true := by
  decide +kernel

theorem tot4755 : totK PA10K2 A10K2.t4755 = [0, 299638544946, 1211962417362, 1889451397213, 1163295505279, 191776795552, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
