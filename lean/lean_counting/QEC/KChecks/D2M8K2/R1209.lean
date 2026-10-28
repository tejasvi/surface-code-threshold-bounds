import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4836 = true := by
  decide +kernel

theorem tot4836 : totK PD2M8K2 D2M8K2.t4836 = [0, 0, 176425804272, 468746386490, 249104475776, 14211171784, 0, 0] := by
  decide +kernel

theorem rows4837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4837 = true := by
  decide +kernel

theorem tot4837 : totK PD2M8K2 D2M8K2.t4837 = [0, 0, 0, 197845367278, 457674205272, 236103342922, 24216995793, 0] := by
  decide +kernel

theorem rows4838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4838 = true := by
  decide +kernel

theorem tot4838 : totK PD2M8K2 D2M8K2.t4838 = [0, 0, 0, 189496512876, 485451712268, 210899865094, 6521599928, 0] := by
  decide +kernel

theorem rows4839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4839 = true := by
  decide +kernel

theorem tot4839 : totK PD2M8K2 D2M8K2.t4839 = [0, 0, 104370356987, 314451247523, 368241608074, 133739753134, 6761411919, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
