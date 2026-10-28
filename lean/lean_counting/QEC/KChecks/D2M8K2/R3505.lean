import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14020 = true := by
  decide +kernel

theorem tot14020 : totK PD2M8K2 D2M8K2.t14020 = [0, 0, 52517250433, 240266594040, 408563304439, 146102083509, 5320761635, 0] := by
  decide +kernel

theorem rows14021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14021 = true := by
  decide +kernel

theorem tot14021 : totK PD2M8K2 D2M8K2.t14021 = [0, 0, 185683811654, 472049902188, 232206489952, 12206498855, 0, 0] := by
  decide +kernel

theorem rows14022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14022 = true := by
  decide +kernel

theorem tot14022 : totK PD2M8K2 D2M8K2.t14022 = [0, 0, 142164912838, 451154229715, 264668775912, 17436756360, 0, 0] := by
  decide +kernel

theorem rows14023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14023 = true := by
  decide +kernel

theorem tot14023 : totK PD2M8K2 D2M8K2.t14023 = [0, 0, 0, 321670716662, 477852680775, 68102090044, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
