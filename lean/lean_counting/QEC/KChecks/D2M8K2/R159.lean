import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t636 = true := by
  decide +kernel

theorem tot636 : totK PD2M8K2 D2M8K2.t636 = [0, 167046815874, 434255356214, 284980282637, 34167921589, 0, 0, 0] := by
  decide +kernel

theorem rows637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t637 = true := by
  decide +kernel

theorem tot637 : totK PD2M8K2 D2M8K2.t637 = [0, 174627184372, 470759417737, 244081845603, 12816399842, 0, 0, 0] := by
  decide +kernel

theorem rows638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t638 = true := by
  decide +kernel

theorem tot638 : totK PD2M8K2 D2M8K2.t638 = [0, 87736198559, 337352137752, 365114753698, 110360550952, 13132862920, 0, 0] := by
  decide +kernel

theorem rows639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t639 = true := by
  decide +kernel

theorem tot639 : totK PD2M8K2 D2M8K2.t639 = [0, 0, 172414650191, 452781318391, 242238657601, 15911586077, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
