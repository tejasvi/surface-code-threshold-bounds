import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16160 = true := by
  decide +kernel

theorem tot16160 : totK PD2M8K2 D2M8K2.t16160 = [0, 0, 36484227454, 330085869787, 430902741710, 63172064872, 1021600638, 0] := by
  decide +kernel

theorem rows16161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16161 = true := by
  decide +kernel

theorem tot16161 : totK PD2M8K2 D2M8K2.t16161 = [0, 0, 188151033772, 454547903176, 241320934270, 20528394667, 0, 0] := by
  decide +kernel

theorem rows16162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16162 = true := by
  decide +kernel

theorem tot16162 : totK PD2M8K2 D2M8K2.t16162 = [0, 0, 202543780855, 488644891451, 209264854441, 9901604992, 0, 0] := by
  decide +kernel

theorem rows16163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16163 = true := by
  decide +kernel

theorem tot16163 : totK PD2M8K2 D2M8K2.t16163 = [0, 156589052074, 365550438881, 231842190449, 121257071785, 13566920432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
