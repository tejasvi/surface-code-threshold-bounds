import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5100 = true := by
  decide +kernel

theorem tot5100 : totK PA10K2 A10K2.t5100 = [0, 307593027685, 803920779257, 899858488462, 1433358562161, 1037037013296, 213642913445, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5101 = true := by
  decide +kernel

theorem tot5101 : totK PA10K2 A10K2.t5101 = [0, 466296408916, 1812454573708, 2070742334214, 612291423481, 32408125582, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5102 = true := by
  decide +kernel

theorem tot5102 : totK PA10K2 A10K2.t5102 = [0, 0, 686041626062, 2070612276928, 1718175357294, 412232938343, 25715051306, 0, 0, 0] := by
  decide +kernel

theorem rows5103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5103 = true := by
  decide +kernel

theorem tot5103 : totK PA10K2 A10K2.t5103 = [0, 287800699719, 1221736766548, 1997769105921, 1244539407109, 208967428606, 5807182206, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
