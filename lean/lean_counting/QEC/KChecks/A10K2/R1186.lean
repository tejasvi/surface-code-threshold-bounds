import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4744 = true := by
  decide +kernel

theorem tot4744 : totK PA10K2 A10K2.t4744 = [0, 554803763168, 1766488629869, 1711677554137, 713641905705, 153018442325, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4745 = true := by
  decide +kernel

theorem tot4745 : totK PA10K2 A10K2.t4745 = [0, 0, 727472783591, 2242909425804, 1710597530592, 286683206661, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows4746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4746 = true := by
  decide +kernel

theorem tot4746 : totK PA10K2 A10K2.t4746 = [0, 0, 398620750488, 1616679141326, 2030668995143, 764880702258, 61094605953, 0, 0, 0] := by
  decide +kernel

theorem rows4747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4747 = true := by
  decide +kernel

theorem tot4747 : totK PA10K2 A10K2.t4747 = [0, 0, 517784807938, 1887946633331, 1914269286123, 451544649983, 12917769548, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
