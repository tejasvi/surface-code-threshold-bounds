import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3672 = true := by
  decide +kernel

theorem tot3672 : totK PA10K2 A10K2.t3672 = [0, 0, 116150967364, 256625354356, 786254725202, 1944686580109, 1234139532945, 202894274768, 6239673734, 0] := by
  decide +kernel

theorem rows3673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3673 = true := by
  decide +kernel

theorem tot3673 : totK PA10K2 A10K2.t3673 = [0, 0, 543205573254, 1905710147515, 1944355887661, 528958981688, 31908368213, 0, 0, 0] := by
  decide +kernel

theorem rows3674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3674 = true := by
  decide +kernel

theorem tot3674 : totK PA10K2 A10K2.t3674 = [0, 0, 133710304625, 1094966966080, 2166184121331, 1361365565215, 266707110187, 20328650499, 0, 0] := by
  decide +kernel

theorem rows3675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3675 = true := by
  decide +kernel

theorem tot3675 : totK PA10K2 A10K2.t3675 = [0, 0, 192465652475, 1017685585836, 1963745741017, 1545831770167, 329306300313, 10956717587, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
