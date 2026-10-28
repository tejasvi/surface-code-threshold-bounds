import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3896 = true := by
  decide +kernel

theorem tot3896 : totK PA10K2 A10K2.t3896 = [0, 0, 0, 779391332625, 2228784465980, 1572249381411, 273077239233, 6904928264, 0, 0] := by
  decide +kernel

theorem rows3897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3897 = true := by
  decide +kernel

theorem tot3897 : totK PA10K2 A10K2.t3897 = [0, 0, 593535314503, 1957293715870, 1874357517005, 602930227527, 52306984658, 0, 0, 0] := by
  decide +kernel

theorem rows3898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3898 = true := by
  decide +kernel

theorem tot3898 : totK PA10K2 A10K2.t3898 = [0, 0, 0, 766829394062, 2279513673596, 1708471527248, 247337352675, 7047025452, 0, 0] := by
  decide +kernel

theorem rows3899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3899 = true := by
  decide +kernel

theorem tot3899 : totK PA10K2 A10K2.t3899 = [0, 0, 538702996020, 1875287299087, 1920898476128, 610187173123, 50403516269, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
