import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t648 = true := by
  decide +kernel

theorem tot648 : totK PA10K2 A10K2.t648 = [0, 436153202774, 1768377908542, 1999159715920, 579279925921, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t649 = true := by
  decide +kernel

theorem tot649 : totK PA10K2 A10K2.t649 = [0, 119721761315, 936523169955, 1957236434291, 1511275681024, 382858554148, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t650 = true := by
  decide +kernel

theorem tot650 : totK PA10K2 A10K2.t650 = [0, 234454346688, 1089901428237, 1876984052634, 1316286399543, 226833090456, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t651 = true := by
  decide +kernel

theorem tot651 : totK PA10K2 A10K2.t651 = [0, 469429386939, 1663867553969, 1888219939054, 654828810993, 52232171148, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
