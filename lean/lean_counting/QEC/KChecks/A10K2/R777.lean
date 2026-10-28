import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3108 = true := by
  decide +kernel

theorem tot3108 : totK PA10K2 A10K2.t3108 = [0, 200263369735, 1342458145072, 2257394456201, 971132228925, 80714406204, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3109 = true := by
  decide +kernel

theorem tot3109 : totK PA10K2 A10K2.t3109 = [0, 507610568542, 1814209475694, 1979295696584, 663062318568, 48124291082, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3110 = true := by
  decide +kernel

theorem tot3110 : totK PA10K2 A10K2.t3110 = [0, 322051627922, 1551089568462, 2252765932304, 919363177113, 72380214855, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3111 = true := by
  decide +kernel

theorem tot3111 : totK PA10K2 A10K2.t3111 = [0, 0, 567814994043, 2004948224918, 2007489453813, 467379670086, 13814447077, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
