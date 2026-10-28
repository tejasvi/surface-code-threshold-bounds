import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7192 = true := by
  decide +kernel

theorem tot7192 : totK PD2M8K2 D2M8K2.t7192 = [0, 189273823132, 461892701368, 236797493386, 15023929769, 0, 0, 0] := by
  decide +kernel

theorem rows7193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7193 = true := by
  decide +kernel

theorem tot7193 : totK PD2M8K2 D2M8K2.t7193 = [0, 42320627977, 319213643546, 442109322158, 100811249119, 1268739303, 0, 0] := by
  decide +kernel

theorem rows7194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7194 = true := by
  decide +kernel

theorem tot7194 : totK PD2M8K2 D2M8K2.t7194 = [0, 0, 207999233754, 479965571480, 179934055541, 7442000727, 0, 0] := by
  decide +kernel

theorem rows7195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7195 = true := by
  decide +kernel

theorem tot7195 : totK PD2M8K2 D2M8K2.t7195 = [0, 0, 184295627794, 483054495599, 217478314026, 14707859566, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
