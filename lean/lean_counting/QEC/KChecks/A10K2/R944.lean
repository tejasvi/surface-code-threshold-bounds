import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3776 = true := by
  decide +kernel

theorem tot3776 : totK PA10K2 A10K2.t3776 = [0, 0, 285708781362, 1471247270715, 2083350198044, 799753327803, 50982771138, 0, 0, 0] := by
  decide +kernel

theorem rows3777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3777 = true := by
  decide +kernel

theorem tot3777 : totK PA10K2 A10K2.t3777 = [0, 0, 356856991846, 1265871053791, 1900639581638, 1133427544302, 192667855392, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3778 = true := by
  decide +kernel

theorem tot3778 : totK PA10K2 A10K2.t3778 = [0, 0, 338266079698, 1634209497452, 2209693604782, 885811707060, 69045496041, 0, 0, 0] := by
  decide +kernel

theorem rows3779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3779 = true := by
  decide +kernel

theorem tot3779 : totK PA10K2 A10K2.t3779 = [0, 0, 0, 664484277916, 2228212887732, 1936121689975, 337959827106, 6962742351, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
