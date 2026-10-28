import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6072 = true := by
  decide +kernel

theorem tot6072 : totK PA10K2 A10K2.t6072 = [0, 293915060262, 1136167890458, 1824348712105, 1162714893521, 187132177885, 5705019915, 0, 0, 0] := by
  decide +kernel

theorem rows6073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6073 = true := by
  decide +kernel

theorem tot6073 : totK PA10K2 A10K2.t6073 = [0, 526633995392, 1936750390750, 2089243127447, 594493295200, 37383675790, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6074 = true := by
  decide +kernel

theorem tot6074 : totK PA10K2 A10K2.t6074 = [0, 0, 772501350204, 2234859519058, 1720852180889, 307621463545, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows6075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6075 = true := by
  decide +kernel

theorem tot6075 : totK PA10K2 A10K2.t6075 = [0, 0, 487351392250, 1793604144116, 2106962094368, 719458360837, 55498468803, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
