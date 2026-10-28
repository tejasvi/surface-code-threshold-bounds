import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4836 = true := by
  decide +kernel

theorem tot4836 : totK PA10K2 A10K2.t4836 = [0, 0, 794810398497, 2304060939070, 1360423716863, 124435123062, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4837 = true := by
  decide +kernel

theorem tot4837 : totK PA10K2 A10K2.t4837 = [0, 623341764251, 2026197266415, 1797383807870, 463903931808, 88142940075, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows4838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4838 = true := by
  decide +kernel

theorem tot4838 : totK PA10K2 A10K2.t4838 = [409489349476, 1362938302565, 1605289483574, 1073638311179, 454412155901, 43925757666, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4839 = true := by
  decide +kernel

theorem tot4839 : totK PA10K2 A10K2.t4839 = [369286712839, 1630369043681, 2022943311734, 752080869186, 61736535564, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
