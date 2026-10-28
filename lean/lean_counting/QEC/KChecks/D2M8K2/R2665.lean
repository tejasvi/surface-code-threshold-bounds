import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10660 = true := by
  decide +kernel

theorem tot10660 : totK PD2M8K2 D2M8K2.t10660 = [0, 0, 174394133180, 460929637022, 242159579454, 14779620411, 0, 0] := by
  decide +kernel

theorem rows10661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10661 = true := by
  decide +kernel

theorem tot10661 : totK PD2M8K2 D2M8K2.t10661 = [0, 0, 92671400364, 368809404524, 340231979730, 64571350827, 1095107716, 0] := by
  decide +kernel

theorem rows10662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10662 = true := by
  decide +kernel

theorem tot10662 : totK PD2M8K2 D2M8K2.t10662 = [0, 0, 0, 324836021172, 471207693210, 78667152094, 1067409660, 0] := by
  decide +kernel

theorem rows10663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10663 = true := by
  decide +kernel

theorem tot10663 : totK PD2M8K2 D2M8K2.t10663 = [0, 0, 175735631326, 414197972679, 230033726974, 60278380823, 2814597007, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
