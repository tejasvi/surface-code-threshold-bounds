import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8164 = true := by
  decide +kernel

theorem tot8164 : totK PA10K2 A10K2.t8164 = [0, 0, 0, 498395592943, 1822625641518, 1983280872119, 681582951097, 50514925555, 0, 0] := by
  decide +kernel

theorem rows8165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8165 = true := by
  decide +kernel

theorem tot8165 : totK PA10K2 A10K2.t8165 = [0, 0, 0, 0, 637215007774, 2060271461717, 1725669176101, 313765662840, 12696458652, 0] := by
  decide +kernel

theorem rows8166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8166 = true := by
  decide +kernel

theorem tot8166 : totK PA10K2 A10K2.t8166 = [0, 0, 0, 444535245055, 1630629048761, 1849586801377, 859775636793, 83869101288, 0, 0] := by
  decide +kernel

theorem rows8167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8167 = true := by
  decide +kernel

theorem tot8167 : totK PA10K2 A10K2.t8167 = [0, 0, 0, 506824276796, 1918690280993, 2060522548674, 535925481490, 18349730384, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
