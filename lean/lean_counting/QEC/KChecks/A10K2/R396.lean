import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1584 = true := by
  decide +kernel

theorem tot1584 : totK PA10K2 A10K2.t1584 = [0, 0, 308261319486, 818759815683, 965218448411, 1417420637997, 921075210765, 160162151064, 5676195732, 0] := by
  decide +kernel

theorem rows1585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1585 = true := by
  decide +kernel

theorem tot1585 : totK PA10K2 A10K2.t1585 = [0, 0, 497046551299, 1869655921588, 2014645146788, 554971409227, 31301336365, 0, 0, 0] := by
  decide +kernel

theorem rows1586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1586 = true := by
  decide +kernel

theorem tot1586 : totK PA10K2 A10K2.t1586 = [0, 0, 0, 679002764546, 2107422668020, 1720461453222, 389460286693, 25313348169, 0, 0] := by
  decide +kernel

theorem rows1587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1587 = true := by
  decide +kernel

theorem tot1587 : totK PA10K2 A10K2.t1587 = [0, 0, 368139604616, 1523380887001, 2175070812300, 901948408270, 77448716409, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
