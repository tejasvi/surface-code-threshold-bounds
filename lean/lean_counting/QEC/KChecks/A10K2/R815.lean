import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3260 = true := by
  decide +kernel

theorem tot3260 : totK PA10K2 A10K2.t3260 = [0, 0, 557764072828, 1897371662062, 1818746442949, 491419280725, 32021558464, 0, 0, 0] := by
  decide +kernel

theorem rows3261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3261 = true := by
  decide +kernel

theorem tot3261 : totK PA10K2 A10K2.t3261 = [0, 0, 446451768150, 1777478618495, 1967247299178, 486794559676, 31265925590, 0, 0, 0] := by
  decide +kernel

theorem rows3262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3262 = true := by
  decide +kernel

theorem tot3262 : totK PA10K2 A10K2.t3262 = [0, 0, 291810091996, 1536043114637, 2109229228932, 713269341657, 44915157038, 0, 0, 0] := by
  decide +kernel

theorem rows3263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3263 = true := by
  decide +kernel

theorem tot3263 : totK PA10K2 A10K2.t3263 = [0, 316846731414, 1021028622186, 1168578417286, 1234441580522, 809388883781, 153292242111, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
