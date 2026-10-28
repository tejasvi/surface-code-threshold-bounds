import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7232 = true := by
  decide +kernel

theorem tot7232 : totK PD2M8K2 D2M8K2.t7232 = [0, 0, 0, 0, 308718813146, 450132731486, 86953493005, 1369150432] := by
  decide +kernel

theorem rows7233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7233 = true := by
  decide +kernel

theorem tot7233 : totK PD2M8K2 D2M8K2.t7233 = [0, 0, 0, 178611860242, 460511647661, 222759082245, 14652870851, 0] := by
  decide +kernel

theorem rows7234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7234 = true := by
  decide +kernel

theorem tot7234 : totK PD2M8K2 D2M8K2.t7234 = [0, 0, 0, 196066928625, 465140340464, 184411416307, 12082697338, 0] := by
  decide +kernel

theorem rows7235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7235 = true := by
  decide +kernel

theorem tot7235 : totK PD2M8K2 D2M8K2.t7235 = [0, 0, 0, 224855475576, 478822929386, 170437292985, 10059231755, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
