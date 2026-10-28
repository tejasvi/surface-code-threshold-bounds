import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5656 = true := by
  decide +kernel

theorem tot5656 : totK PA10K2 A10K2.t5656 = [0, 0, 586475409261, 1977446467568, 1823741329503, 398340386313, 17013136330, 0, 0, 0] := by
  decide +kernel

theorem rows5657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5657 = true := by
  decide +kernel

theorem tot5657 : totK PA10K2 A10K2.t5657 = [0, 0, 475528897785, 1775284523502, 1965377655415, 571898189259, 32470943963, 0, 0, 0] := by
  decide +kernel

theorem rows5658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5658 = true := by
  decide +kernel

theorem tot5658 : totK PA10K2 A10K2.t5658 = [0, 0, 514551687992, 1840462163020, 1863980794465, 494801467818, 31607162994, 0, 0, 0] := by
  decide +kernel

theorem rows5659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5659 = true := by
  decide +kernel

theorem tot5659 : totK PA10K2 A10K2.t5659 = [0, 0, 302082434609, 1555664262957, 2086899005235, 652234364862, 51402059204, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
