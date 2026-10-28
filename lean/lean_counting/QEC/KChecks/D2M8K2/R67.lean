import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t268 = true := by
  decide +kernel

theorem tot268 : totK PD2M8K2 D2M8K2.t268 = [0, 195167430265, 465609344038, 233792958178, 13545138188, 0, 0, 0] := by
  decide +kernel

theorem rows269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t269 = true := by
  decide +kernel

theorem tot269 : totK PD2M8K2 D2M8K2.t269 = [0, 37697318208, 323988482196, 437898755541, 102414519425, 1402015981, 0, 0] := by
  decide +kernel

theorem rows270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t270 = true := by
  decide +kernel

theorem tot270 : totK PD2M8K2 D2M8K2.t270 = [0, 36946381487, 223880229000, 442593244804, 185562328217, 8173611642, 0, 0] := by
  decide +kernel

theorem rows271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t271 = true := by
  decide +kernel

theorem tot271 : totK PD2M8K2 D2M8K2.t271 = [0, 186181632360, 458402456461, 240610327188, 20886707449, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
