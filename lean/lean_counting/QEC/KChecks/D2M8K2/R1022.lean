import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4088 = true := by
  decide +kernel

theorem tot4088 : totK PD2M8K2 D2M8K2.t4088 = [0, 0, 69328447648, 377341593419, 385721477051, 42750230408, 0, 0] := by
  decide +kernel

theorem rows4089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4089 = true := by
  decide +kernel

theorem tot4089 : totK PD2M8K2 D2M8K2.t4089 = [0, 0, 69081942644, 314648830770, 379978236987, 88249735211, 2340352732, 0] := by
  decide +kernel

theorem rows4090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4090 = true := by
  decide +kernel

theorem tot4090 : totK PD2M8K2 D2M8K2.t4090 = [0, 0, 181557764689, 466707439208, 244729817717, 20829303670, 0, 0] := by
  decide +kernel

theorem rows4091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4091 = true := by
  decide +kernel

theorem tot4091 : totK PD2M8K2 D2M8K2.t4091 = [0, 0, 161143110536, 475430733314, 260010130014, 12392787116, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
