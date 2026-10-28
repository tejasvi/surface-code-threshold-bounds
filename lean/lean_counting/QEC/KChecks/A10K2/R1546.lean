import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6184 = true := by
  decide +kernel

theorem tot6184 : totK PA10K2 A10K2.t6184 = [0, 112037851608, 797835188947, 1917844757185, 1590135778639, 315255404900, 10760911071, 0, 0, 0] := by
  decide +kernel

theorem rows6185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6185 = true := by
  decide +kernel

theorem tot6185 : totK PA10K2 A10K2.t6185 = [0, 491292141402, 1721761350111, 1863385546283, 619700515453, 51794973690, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6186 = true := by
  decide +kernel

theorem tot6186 : totK PA10K2 A10K2.t6186 = [0, 132459554679, 1278521147654, 2258279982452, 976983179095, 80941132194, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6187 = true := by
  decide +kernel

theorem tot6187 : totK PA10K2 A10K2.t6187 = [0, 297392362862, 1205395950790, 1849433639607, 1152427565922, 219727073494, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
