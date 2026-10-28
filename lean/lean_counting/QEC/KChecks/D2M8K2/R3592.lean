import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14368 = true := by
  decide +kernel

theorem tot14368 : totK PD2M8K2 D2M8K2.t14368 = [0, 0, 208360072086, 491151714840, 180077677766, 9299314533, 0, 0] := by
  decide +kernel

theorem rows14369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14369 = true := by
  decide +kernel

theorem tot14369 : totK PD2M8K2 D2M8K2.t14369 = [0, 0, 199033578224, 472513714666, 223350377024, 16063424123, 0, 0] := by
  decide +kernel

theorem rows14370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14370 = true := by
  decide +kernel

theorem tot14370 : totK PD2M8K2 D2M8K2.t14370 = [0, 0, 172856664191, 470182797212, 226520534852, 13389191926, 0, 0] := by
  decide +kernel

theorem rows14371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14371 = true := by
  decide +kernel

theorem tot14371 : totK PD2M8K2 D2M8K2.t14371 = [0, 0, 0, 299735992131, 475765184599, 96787220835, 1162935789, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
