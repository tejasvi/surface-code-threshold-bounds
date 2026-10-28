import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12128 = true := by
  decide +kernel

theorem tot12128 : totK PD2M8K2 D2M8K2.t12128 = [0, 166053700476, 442379614281, 265288906442, 33779413825, 0, 0, 0] := by
  decide +kernel

theorem rows12129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12129 = true := by
  decide +kernel

theorem tot12129 : totK PD2M8K2 D2M8K2.t12129 = [0, 176508801254, 484173836298, 236704882195, 10960659078, 0, 0, 0] := by
  decide +kernel

theorem rows12130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12130 = true := by
  decide +kernel

theorem tot12130 : totK PD2M8K2 D2M8K2.t12130 = [0, 0, 286477529688, 511469411294, 90950474865, 1070790515, 0, 0] := by
  decide +kernel

theorem rows12131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12131 = true := by
  decide +kernel

theorem tot12131 : totK PD2M8K2 D2M8K2.t12131 = [0, 155237236290, 371391575111, 278126241074, 72792713248, 3462014130, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
