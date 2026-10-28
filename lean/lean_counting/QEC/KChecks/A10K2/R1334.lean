import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5336 = true := by
  decide +kernel

theorem tot5336 : totK PA10K2 A10K2.t5336 = [0, 307485040078, 1483991486495, 2217047883485, 989299939262, 85858363510, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5337 = true := by
  decide +kernel

theorem tot5337 : totK PA10K2 A10K2.t5337 = [0, 282207666598, 1172273488705, 1856407819100, 1408088688807, 333636617956, 13572172291, 0, 0, 0] := by
  decide +kernel

theorem rows5338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5338 = true := by
  decide +kernel

theorem tot5338 : totK PA10K2 A10K2.t5338 = [0, 462833872393, 1774817457972, 1996675231921, 623901210730, 41896620766, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5339 = true := by
  decide +kernel

theorem tot5339 : totK PA10K2 A10K2.t5339 = [0, 122956571035, 940739687987, 2150320614970, 1557164400299, 265348061024, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
